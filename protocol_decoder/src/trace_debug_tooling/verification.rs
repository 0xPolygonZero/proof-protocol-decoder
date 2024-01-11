// TODO: Replace all `unwraps()` with actual errors...

use core::fmt;
use std::{
    collections::{HashMap, HashSet},
    fmt::{Display, LowerHex},
};

use eth_trie_utils::partial_trie::PartialTrie;
use eth_trie_utils::{nibbles::Nibbles, partial_trie::HashedPartialTrie};
use ethereum_types::{Address, H256};
use futures::{executor::block_on, future::join_all};
use plonky2_evm::{generation::mpt::AccountRlp, proof::TrieRoots};
use reqwest::Url;
use thiserror::Error;

use super::rpc_utils::{
    AccountStateEntryDiff, EthGetProofResponse, GetBlockByNumberResponse,
    TraceReplayTransactionResponse,
};
use crate::{
    compact::compact_prestate_processing::PartialTriePreImages,
    decoding::TrieType,
    processed_block_trace::{
        process_block_trace_trie_pre_images, ProcessedBlockTrace, ProcessedTxnInfo, ProcessingMeta,
        VerificationCfg,
    },
    trace_protocol::{BlockTrace, TxnInfo},
    types::{
        BlockHeight, CodeHash, CodeHashResolveFunc, HashedAccountAddr, HashedAccountAddrNibbles,
        HashedStorageAddr, HashedStorageAddrNibbles, OtherBlockData, PartialTrieState, StorageAddr,
        TrieRootHash, TxnIdx, TxnProofGenIR, EMPTY_CODE_HASH, EMPTY_TRIE_HASH,
    },
    utils::{get_leaf_vals_from_trie, get_leaf_vals_from_trie_and_decode, hash},
};

// All account storage roots in accounts exist in the storage trie after each
// txn. All account code hashes have a matching entry for every txn.
// All pre-image leafs are accessed by the traces.
// All final storage slots mentioned in trace match result from rpc call to full
// node. All account entry fields match call to rpc call to full node.
// Check that all roots match rpc call to full node.

pub(crate) type TraceVerificationResult<T> = Result<T, TraceVerificationErrors>;

#[derive(Debug)]
pub(crate) struct GeneratedProofAndDebugInfo {
    ir: Vec<TxnProofGenIR>,
    final_tries_after_each_txn: Vec<PartialTrieState>,
    processed_trace: ProcessedBlockTrace,
}

#[derive(Debug, Error)]
pub struct TraceVerificationErrors {
    errs: Vec<TraceVerificationError>,
}

impl fmt::Display for TraceVerificationErrors {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "The following verification errors occurred:")?;

        for err in self.errs.iter() {
            writeln!(f, "{}", err)?;
        }

        Ok(())
    }
}

#[derive(Clone, Debug)]
struct HashedKeyAndUnhashedLookup<K>
where
    K: Clone + Display + LowerHex,
{
    k: HashLookupAttempt<K>,
    hashed: Nibbles,
}

impl<K> Display for HashedKeyAndUnhashedLookup<K>
where
    K: Clone + Display + LowerHex,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}, (hashed: {})", self.k, self.hashed)
    }
}

#[derive(Clone, Debug, Error)]
pub enum TraceVerificationError {
    #[error("No storage trie supplied for storage root {2:x} which is referenced by account {0} (hashed: {1:x})")]
    MissingStorageTrieForAccount(
        HashLookupAttempt<Address>,
        HashedAccountAddrNibbles,
        TrieRootHash,
    ),

    #[error("No contract bytecode supplied for code hash {2:x} which is referenced by account {0} (hashed: {1:x})")]
    MissingContractCodeForAccount(
        HashLookupAttempt<Address>,
        HashedAccountAddrNibbles,
        CodeHash,
    ),

    #[error("The decoder calculated a different trie root that the upstream block trace provider (eg. full-node) arrived at (type: {0}, decoder: {1:x}, upstream: {2:x})")]
    DecoderFinalTrieRootMismatch(TrieType, TrieRootHash, TrieRootHash),

    #[error("Pre-image had state nodes that are not referenced by the trace: {0:#?}")]
    UnusedStateNodesInPreImage(Vec<HashedKeyAndUnhashedLookup<Address>>),

    #[error("Pre-image had storage nodes that are not referenced by the trace: {0:#?}")]
    UnusedStorageNodesInPreImage(Vec<HashedKeyAndUnhashedLookup<StorageAddr>>),

    #[error(
        "Local account state was different from upstream: (txn_idx: {0}, Address: {1:x}, diff: {2}"
    )]
    AccountStateMismatch(TxnIdx, Address, AccountStateEntryDiff),
}

/// Wrapper around an `Option` just to make errors a bit more readable.
#[derive(Clone, Debug)]
struct HashLookupAttempt<T: LowerHex>(Option<T>);

impl<T: LowerHex> Display for HashLookupAttempt<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            Some(v) => write!(f, "{:x}", v),
            None => write!(f, "Unknown"),
        }
    }
}

impl<T: LowerHex> From<Option<T>> for HashLookupAttempt<T> {
    fn from(v: Option<T>) -> Self {
        Self(v)
    }
}

#[derive(Debug)]
struct ReverseHashMapping {
    hashed_addr_to_addr: HashMap<HashedAccountAddrNibbles, HashLookupAttempt<Address>>,
    hashed_slot_to_slot: HashMap<HashedStorageAddrNibbles, HashLookupAttempt<StorageAddr>>,
}

#[derive(Debug)]
struct AccountRlpWrapper(AccountRlp);

// Gross...
impl Clone for AccountRlpWrapper {
    fn clone(&self) -> Self {
        Self(AccountRlp {
            nonce: self.0.nonce,
            balance: self.0.balance,
            storage_root: self.0.storage_root,
            code_hash: self.0.code_hash,
        })
    }
}

impl PartialEq for AccountRlpWrapper {
    fn eq(&self, other: &Self) -> bool {
        self.0.balance == other.0.balance
            && self.0.nonce == other.0.nonce
            && self.0.code_hash == other.0.code_hash
            && self.0.storage_root == other.0.storage_root
    }
}

impl From<AccountRlp> for AccountRlpWrapper {
    fn from(v: AccountRlp) -> Self {
        Self(v)
    }
}

pub(crate) fn verify_proof_gen_ir<F: CodeHashResolveFunc>(
    b_trace: &BlockTrace,
    other_data: &OtherBlockData,
    p_meta: &ProcessingMeta<F>,
    verif_cfg: &VerificationCfg,
) -> TraceVerificationResult<()> {
    let mut err_buf = Vec::default();
    let pre_image = process_block_trace_trie_pre_images(b_trace.trie_pre_images.clone(), false);
    let code_supplied_by_pre_image = pre_image.extra_code_hash_mappings.unwrap_or_default();

    let reverse_hash_mapping =
        create_addr_to_hashed_addr_mapping(&pre_image.tries, &b_trace.txn_info);

    let proced_b_trace = b_trace.clone().into_processed_block_trace(p_meta, false);

    verify_all_referenced_code_exists_in_code_mapping(
        &pre_image.tries.state,
        &proced_b_trace.txn_info,
        &code_supplied_by_pre_image,
        &reverse_hash_mapping,
        &mut err_buf,
    );

    verify_all_prestate_storage_entries_point_to_existing_tries(
        &proced_b_trace.tries,
        &proced_b_trace.txn_info,
        &reverse_hash_mapping,
        &mut err_buf,
    );

    let ir = proced_b_trace
        .into_txn_proof_gen_ir(other_data.clone())
        .unwrap();

    if let Some(endpoint) = &verif_cfg.ground_truth_endpoint {
        block_on(rpc_verification_checks(
            &ir,
            &b_trace.txn_info,
            other_data.b_data.b_meta.block_number.as_u64(),
            &Url::parse(endpoint).unwrap(),
            &mut err_buf,
        ))
        .unwrap();
    }

    match err_buf.is_empty() {
        false => Err(TraceVerificationErrors { errs: err_buf }),
        true => Ok(()),
    }
}

async fn rpc_verification_checks(
    ir: &[TxnProofGenIR],
    raw_traces: &[TxnInfo],
    _b_height: BlockHeight,
    endpoint: &Url,
    err_buf: &mut Vec<TraceVerificationError>,
) -> anyhow::Result<()> {
    if let Some(final_txn_ir) = ir.last() {
        let b_height = final_txn_ir.b_height();

        verify_local_state_matches_upstream_per_txn(
            &final_txn_ir.gen_inputs.trie_roots_after,
            ir,
            b_height,
            endpoint,
            err_buf,
        )
        .await?;

        let _upstream_account_state = get_upstream_account_state_for_all_addresses_used_in_trace(
            raw_traces, b_height, endpoint,
        )
        .await;

        // verify_all_account_entry_nodes_match_full_node(&final_txn_ir.
        // gen_inputs.tries.state_trie);
    }

    Ok(())
}

fn verify_all_prestate_storage_entries_point_to_existing_tries(
    pre_image: &PartialTriePreImages,
    traces: &[ProcessedTxnInfo],
    reverse_hash_mapping: &ReverseHashMapping,
    err_buf: &mut Vec<TraceVerificationError>,
) {
    let all_storage_accessed = get_all_storage_tries_that_are_accessed(traces);

    for (h_addr, acc) in get_leaf_vals_from_trie_and_decode::<AccountRlp>(&pre_image.state) {
        if acc.storage_root != EMPTY_TRIE_HASH
            && all_storage_accessed.contains(&acc.storage_root)
            && !pre_image.storage.contains_key(&acc.storage_root)
        {
            let addr_lookup_attempt = reverse_hash_mapping.hashed_addr_to_addr[&h_addr].clone();

            err_buf.push(TraceVerificationError::MissingStorageTrieForAccount(
                addr_lookup_attempt,
                h_addr,
                acc.storage_root,
            ));
        }
    }
}

fn get_all_storage_tries_that_are_accessed(
    traces: &[ProcessedTxnInfo],
) -> HashSet<HashedAccountAddr> {
    traces
        .iter()
        .flat_map(|t| {
            t.nodes_used_by_txn
                .storage_accesses
                .iter()
                .map(|(h_addr, _)| H256::from_slice(&h_addr.bytes_be()))
        })
        .collect()
}

fn verify_all_referenced_code_exists_in_code_mapping(
    pre_image_state: &HashedPartialTrie,
    traces: &[ProcessedTxnInfo],
    code_supplied_by_pre_image: &HashMap<CodeHash, Vec<u8>>,
    reverse_hash_mapping: &ReverseHashMapping,
    err_buf: &mut Vec<TraceVerificationError>,
) {
    // TODO: For now, we are going to make the assumption that all byte code is
    // provided in the pre-state trie. This assumption may change in the future, and
    // if it does, we should either remove this check or put it behind a config
    // flag.

    let all_code_hashes_accessed = get_all_contract_code_hashes_that_are_accessed(traces);

    for (h_addr, acc) in get_leaf_vals_from_trie_and_decode::<AccountRlp>(pre_image_state) {
        if acc.code_hash != EMPTY_CODE_HASH
            && all_code_hashes_accessed.contains(&acc.code_hash)
            && !code_supplied_by_pre_image.contains_key(&acc.code_hash)
        {
            let addr_lookup_attempt = &reverse_hash_mapping.hashed_addr_to_addr[&h_addr];

            err_buf.push(TraceVerificationError::MissingContractCodeForAccount(
                addr_lookup_attempt.clone(),
                h_addr,
                acc.code_hash,
            ));
        }
    }
}

fn get_all_contract_code_hashes_that_are_accessed(
    traces: &[ProcessedTxnInfo],
) -> HashSet<CodeHash> {
    traces
        .iter()
        .flat_map(|t| t.contract_code_accessed.keys().cloned())
        .collect()
}

// Note: We can only verify the storage roots that are mentioned in the trace
// because the pre-image only contains addresses that are hashed.
async fn verify_all_upstream_storage_roots_match_our_storage_roots(
    raw_traces: &[TxnInfo],
    s_tries: &HashMap<HashedStorageAddr, HashedPartialTrie>,
    b_height: BlockHeight,
    endpoint: &Url,
    err_buf: &mut Vec<TraceVerificationError>,
) -> anyhow::Result<()> {
    let all_addresses_that_mutate_storage = raw_traces.iter().flat_map(|txn_info| {
        txn_info.traces.iter().filter_map(|(addr, trace)| {
            trace
                .storage_written
                .as_ref()
                .and_then(|s| s.is_empty().then_some(*addr))
        })
    });

    let (our_s_roots, upstream_s_root_futs): (Vec<_>, Vec<_>) = all_addresses_that_mutate_storage
        .map(|addr| {
            let our_s_root = s_tries.get(&hash(addr.as_bytes())).unwrap().hash();
            let upstream_s_root_fut = get_upstream_s_root_for_address(addr, b_height, endpoint);

            (our_s_root, upstream_s_root_fut)
        })
        .unzip();

    let upstream_s_roots = join_all(upstream_s_root_futs).await;

    for (our_s_root, upstream_s_root) in our_s_roots.into_iter().zip(upstream_s_roots) {
        if our_s_root != upstream_s_root {
            err_buf.push(TraceVerificationError::DecoderFinalTrieRootMismatch(
                TrieType::Storage,
                our_s_root,
                upstream_s_root,
            ));
        }
    }

    Ok(())
}

async fn get_upstream_s_root_for_address(
    addr: Address,
    b_height: BlockHeight,
    endpoint: &Url,
) -> TrieRootHash {
    EthGetProofResponse::fetch(endpoint, addr, b_height)
        .await
        .unwrap()
        .storage_hash
    // TODO: Handle errors later...
}

async fn get_upstream_account_state_for_all_addresses_used_in_trace(
    traces: &[TxnInfo],
    b_height: BlockHeight,
    endpoint: &Url,
) -> Vec<(Address, AccountRlp)> {
    let all_unique_addrs = get_all_unique_addrs_used_in_trace(traces);

    let get_account_futs: Vec<_> = all_unique_addrs
        .iter()
        .map(|addr| EthGetProofResponse::fetch(endpoint, *addr, b_height))
        .collect();

    // TODO: Handle errors later...
    // I can't think of a way to avoid all of these allocations, and I'm kind of
    // moving fast...
    let all_acc_state: Vec<_> = join_all(get_account_futs)
        .await
        .into_iter()
        .map(|res| res.unwrap().into())
        .collect();

    all_unique_addrs
        .into_iter()
        .zip(all_acc_state.into_iter())
        .collect()
}

// fn verify_all_account_entry_nodes_match_full_node(
//     state_trie: &HashedPartialTrie,
//     upstream_accounts_that_appear_in_trace: &[(Address, AccountRlpWrapper)],
//     err_buf: &mut Vec<TraceVerificationError>,
// ) {
//     for (acc_k, upstream_data) in upstream_accounts_that_appear_in_trace {
//         let local_data =
// AccountRlpWrapper::from(get_account_from_trie(state_trie, acc_k));

//         if &local_data != upstream_data {
//             err_buf.push(TraceVerificationError::AccountStateMismatch(*acc_k,
// local_data.clone(), upstream_data.clone()));         }

//         // TODO: Launch storage addr check here if the storage root does not
// match...     }
// }

async fn verify_local_state_matches_upstream_per_txn(
    decoder_final_trie_roots: &TrieRoots,
    ir: &[TxnProofGenIR],
    b_height: BlockHeight,
    endpoint: &Url,
    err_buf: &mut Vec<TraceVerificationError>,
) -> anyhow::Result<()> {
    let resp = GetBlockByNumberResponse::fetch(endpoint, b_height).await?;

    let some_roots_differ = decoder_final_trie_roots.state_root != resp.state_root
        || decoder_final_trie_roots.transactions_root != resp.txn_root
        || decoder_final_trie_roots.receipts_root != resp.receipts_root;

    if some_roots_differ {
        push_trie_root_mismatch_error_if_roots_differ(
            &decoder_final_trie_roots.state_root,
            &resp.state_root,
            TrieType::State,
            err_buf,
        );

        push_trie_root_mismatch_error_if_roots_differ(
            &decoder_final_trie_roots.transactions_root,
            &resp.txn_root,
            TrieType::Txn,
            err_buf,
        );

        push_trie_root_mismatch_error_if_roots_differ(
            &decoder_final_trie_roots.receipts_root,
            &resp.receipts_root,
            TrieType::Receipt,
            err_buf,
        );

        find_and_report_first_upstream_txn_state_that_differs_from_ours(
            &resp.txn_hashes,
            ir,
            endpoint,
            err_buf,
        )
        .await;
    }

    Ok(())
}

fn push_trie_root_mismatch_error_if_roots_differ(
    our_root: &TrieRootHash,
    upstream_root: &TrieRootHash,
    trie_type: TrieType,
    err_buf: &mut Vec<TraceVerificationError>,
) {
    if our_root != upstream_root {
        err_buf.push(TraceVerificationError::DecoderFinalTrieRootMismatch(
            trie_type,
            *our_root,
            *upstream_root,
        ));
    }
}

// Stops after first mismatch.
async fn find_and_report_first_upstream_txn_state_that_differs_from_ours(
    txn_hashes: &[H256],
    ir: &[TxnProofGenIR],
    endpoint: &Url,
    err_buf: &mut Vec<TraceVerificationError>,
) {
    let txn_diffs: Vec<_> = join_all(
        txn_hashes
            .iter()
            .map(|txn_hash| TraceReplayTransactionResponse::fetch(endpoint, txn_hash)),
    )
    .await;

    assert_eq!(txn_hashes.len(), ir.len());

    // Because the IR only contains the trie at the start of the txn and the diff
    // contains the final value at the end of the txn, we need to compare the diffs
    // to the previous IR value.
    for (txn_diff, txn_ir) in txn_diffs
        .into_iter()
        .map(|res| res.map(|resp| resp.result.state_diff).unwrap())
        .zip(ir.iter().skip(1))
    {
        for (diff_addr, new_upstream_val) in txn_diff.iter() {
            let acc_data = get_account_from_trie(&txn_ir.gen_inputs.tries.state_trie, diff_addr);

            let diff = new_upstream_val.create_diff_from_actual_data(&acc_data);
            if !diff.values_have_changed() {
                err_buf.push(TraceVerificationError::AccountStateMismatch(
                    txn_ir.txn_idx,
                    *diff_addr,
                    diff,
                ));
            }
        }
    }
}

fn create_addr_to_hashed_addr_mapping(
    pre_state: &PartialTriePreImages,
    traces: &[TxnInfo],
) -> ReverseHashMapping {
    let trace_addr_to_h_addr: HashMap<_, _> = traces
        .iter()
        .flat_map(|txn_info| {
            txn_info
                .traces
                .keys()
                .map(|addr| (hash(addr.as_bytes()), *addr))
        })
        .collect();

    let trace_slot_to_h_slot: HashMap<_, _> = traces
        .iter()
        .flat_map(|txn_info| {
            txn_info.traces.iter().flat_map(|(_, trace)| {
                let all_account_slots = trace
                    .storage_read
                    .iter()
                    .flat_map(|x| x.iter())
                    .chain(trace.storage_written.iter().flat_map(|x| x.keys()));
                all_account_slots.map(|slot| (hash(slot.as_bytes()), *slot))
            })
        })
        .collect();

    let hashed_addr_to_addr = get_leaf_vals_from_trie(&pre_state.state)
        .map(|(h_addr_nibs, _)| {
            let h_addr = HashedAccountAddr::from_slice(&h_addr_nibs.bytes_be());
            let addr_lookup_res = trace_addr_to_h_addr.get(&h_addr).cloned().into();

            (h_addr_nibs, addr_lookup_res)
        })
        .collect();

    let hashed_slot_to_slot = pre_state
        .storage
        .iter()
        .flat_map(|(_, s_trie)| {
            get_leaf_vals_from_trie(s_trie).map(|(h_slot_nibs, _)| {
                let h_slot = HashedStorageAddr::from_slice(&h_slot_nibs.bytes_be());
                let slot_lookup_res = trace_slot_to_h_slot.get(&h_slot).cloned().into();

                (h_slot_nibs, slot_lookup_res)
            })
        })
        .collect();

    ReverseHashMapping {
        hashed_addr_to_addr,
        hashed_slot_to_slot,
    }
}

fn get_all_unique_addrs_used_in_trace(trace: &[TxnInfo]) -> HashSet<Address> {
    trace
        .iter()
        .flat_map(|txn_info| txn_info.traces.keys().copied())
        .collect()
}

fn get_account_from_trie(trie: &HashedPartialTrie, addr: &Address) -> AccountRlp {
    let h_addr = hash(addr.as_bytes());
    let bytes = trie.get(Nibbles::from_h256_be(h_addr)).unwrap();

    rlp::decode(bytes).unwrap()
}
