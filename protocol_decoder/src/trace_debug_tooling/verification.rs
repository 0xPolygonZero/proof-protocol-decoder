// TODO: Replace all `unwraps()` with actual errors...

use core::fmt;
use std::{collections::HashMap, fmt::Display};

use eth_trie_utils::partial_trie::PartialTrie;
use ethereum_types::Address;
use plonky2_evm::generation::mpt::AccountRlp;
use thiserror::Error;

use crate::{
    compact::compact_prestate_processing::PartialTriePreImages,
    processed_block_trace::{ProcessedBlockTrace, ProcessingMeta},
    trace_protocol::{BlockTrace, TxnInfo},
    types::{
        CodeHashResolveFunc, HashedAccountAddr, HashedAccountAddrNibbles, HashedStorageAddr,
        HashedStorageAddrNibbles, PartialTrieState, StorageAddr, TxnProofGenIR,
    },
    utils::{get_leaf_vals_from_trie_and_decode, hash},
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
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

#[derive(Clone, Debug)]
pub enum TraceVerificationError {}

pub enum PreStateVerificationError {
    MissingStorageTrieForAccount(HashLookupAttempt<Address>, HashedAccountAddrNibbles),
}

/// Wrapper around an `Option` just to make errors a bit more readable.
#[derive(Clone, Debug)]
struct HashLookupAttempt<T: Display>(Option<T>);

impl<T: Display> Display for HashLookupAttempt<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            Some(v) => write!(f, "{}", v),
            None => write!(f, "Unknown"),
        }
    }
}

impl<T: Display> From<Option<T>> for HashLookupAttempt<T> {
    fn from(v: Option<T>) -> Self {
        Self(v)
    }
}

#[derive(Debug)]
struct ReverseHashMapping {
    hashed_addr_to_addr: HashMap<HashedAccountAddrNibbles, HashLookupAttempt<Address>>,
    hashed_slot_to_slot: HashMap<HashedStorageAddrNibbles, HashLookupAttempt<StorageAddr>>,
}

pub(crate) fn verify_proof_gen_ir<F: CodeHashResolveFunc>(
    b_trace: &BlockTrace,
    p_meta: &ProcessingMeta<F>,
) -> TraceVerificationResult<()> {
    let proced_b_trace = b_trace.clone().into_processed_block_trace(p_meta, false);
    let reverse_hash_mapping =
        create_addr_to_hashed_addr_mapping(&proced_b_trace.tries, &b_trace.txn_info);

    verify_all_prestate_account_entries_point_to_valid_data(
        &proced_b_trace.tries,
        &reverse_hash_mapping,
    );

    Ok(())
}

fn verify_all_prestate_account_entries_point_to_valid_data(
    pre_state: &PartialTriePreImages,
    reverse_hash_mapping: &ReverseHashMapping,
) -> Vec<PreStateVerificationError> {
    let mut errs = Vec::default();

    for (h_addr, acc) in get_leaf_vals_from_trie_and_decode::<AccountRlp>(&pre_state.state) {
        if !pre_state.storage.contains_key(&acc.storage_root) {
            let addr_lookup_attempt = reverse_hash_mapping.hashed_addr_to_addr[&h_addr].clone();
            errs.push(PreStateVerificationError::MissingStorageTrieForAccount(
                addr_lookup_attempt,
                h_addr,
            ));
        }

        // TODO: Also verify code hashes...
    }

    errs
}

fn verify_all_account_storage_roots_exist_in_account_partial_trie() {
    todo!();
}

fn verify_all_referenced_code_exists_in_code_mapping() {
    todo!();
}

fn verify_all_pre_image_nodes_are_accessed_throughout_the_block() {
    todo!();
}

fn verify_all_final_block_storage_slots_match_full_node() {
    todo!();
}

fn verify_all_account_entry_nodes_match_full_node() {
    todo!();
}

fn verify_all_final_trie_roots_match_full_node() {
    todo!();
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

    let hashed_addr_to_addr = pre_state
        .state
        .keys()
        .map(|h_addr_nibs| {
            let h_addr = HashedAccountAddr::from_slice(&h_addr_nibs.bytes_be());
            let addr_lookup_res = trace_addr_to_h_addr.get(&h_addr).cloned().into();

            (h_addr_nibs, addr_lookup_res)
        })
        .collect();

    let hashed_slot_to_slot = pre_state
        .storage
        .iter()
        .flat_map(|(_, s_trie)| {
            s_trie.items().map(|(h_slot_nibs, _)| {
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
