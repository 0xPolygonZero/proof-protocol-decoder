use std::{
    collections::HashMap,
    fmt::{self, Display, Formatter},
    iter::once,
};

use eth_trie_utils::{
    nibbles::Nibbles,
    partial_trie::{HashedPartialTrie, Node, PartialTrie},
    trie_ops::ValOrHash,
    trie_subsets::create_trie_subset,
};
use ethereum_types::{Address, H256, U256};
use plonky2_evm::{
    generation::{mpt::AccountRlp, GenerationInputs, TrieInputs},
    proof::TrieRoots,
};
use thiserror::Error;

use crate::{
    processed_block_trace::{
        NodesUsedByTxn, ProcessedBlockTrace, ProcessedTxnInfo, StateTrieWrites, TxnMetaState,
    },
    trace_debug_tooling::verification::TraceVerificationErrors,
    types::{
        HashedAccountAddr, HashedNodeAddr, HashedStorageAddrNibbles, OtherBlockData,
        PartialTrieState, TrieRootHash, TxnIdx, TxnProofGenIR, EMPTY_ACCOUNT_BYTES_RLPED,
        EMPTY_TRIE_HASH, ZERO_STORAGE_SLOT_VAL_RLPED,
    },
    utils::{hash, update_val_if_some},
};

pub type TraceParsingResult<T> = Result<T, TraceParsingError>;

#[derive(Debug, Error)]
pub enum TraceParsingError {
    #[error("Failed to decode RLP bytes ({0}) as an Ethereum account due to the error: {1}")]
    AccountDecode(String, String),

    #[error("Missing account storage trie in base trie when constructing subset partial trie for txn (account: {0})")]
    MissingAccountStorageTrie(HashedAccountAddr),

    #[error("Tried accessing a non-existent key ({1}) in the {0} trie (root hash: {2:x})")]
    NonExistentTrieEntry(TrieType, Nibbles, TrieRootHash),

    // TODO: Figure out how to make this error useful/meaningful... For now this is just a
    // placeholder.
    #[error("Missing keys when creating sub-partial tries (Trie type: {0})")]
    MissingKeysCreatingSubPartialTrie(TrieType),

    #[error("A trace failed verification. This is likely a bug in the source creating the trace, but may also be an issue in the decoder itself.\nThe following errors occurred:\n{0}")]
    VerificationError(#[from] TraceVerificationErrors),
}

#[derive(Copy, Clone, Debug)]
pub enum TrieType {
    State,
    Storage,
    Receipt,
    Txn,
}

impl Display for TrieType {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            TrieType::State => write!(f, "state"),
            TrieType::Storage => write!(f, "storage"),
            TrieType::Receipt => write!(f, "receipt"),
            TrieType::Txn => write!(f, "transaction"),
        }
    }
}

impl ProcessedBlockTrace {
    pub(crate) fn into_txn_proof_gen_ir_with_extra_debug_info(
        self,
        other_data: OtherBlockData,
    ) -> TraceParsingResult<(Vec<TxnProofGenIR>, Vec<PartialTrieState>)> {
        let (mut curr_block_tries, initial_tries_for_dummies, mut tot_gas_used) =
            self.create_initial_state_for_creating_proof_gen_ir();

        let gen_inputs_and_final_trie_states = self
            .txn_info
            .into_iter()
            .enumerate()
            .map(|(txn_idx, txn_info)| {
                let res = Self::process_txn_gen_input_into_ir(
                    txn_idx,
                    txn_info,
                    &other_data,
                    &mut curr_block_tries,
                    &mut tot_gas_used,
                );
                res.map(|ir| (ir, curr_block_tries.clone()))
            })
            .collect::<TraceParsingResult<Vec<_>>>()?;

        let (mut txn_gen_inputs, tries_after_each_txn) =
            gen_inputs_and_final_trie_states.into_iter().unzip();

        Self::pad_gen_inputs_with_dummy_inputs_if_needed(
            &mut txn_gen_inputs,
            &other_data,
            &initial_tries_for_dummies,
        );
        Ok((txn_gen_inputs, tries_after_each_txn))
    }

    pub(crate) fn into_txn_proof_gen_ir(
        self,
        other_data: OtherBlockData,
    ) -> TraceParsingResult<Vec<TxnProofGenIR>> {
        let (mut curr_block_tries, initial_tries_for_dummies, mut tot_gas_used) =
            self.create_initial_state_for_creating_proof_gen_ir();

        let mut txn_gen_inputs = self
            .txn_info
            .into_iter()
            .enumerate()
            .map(|(txn_idx, txn_info)| {
                Self::process_txn_gen_input_into_ir(
                    txn_idx,
                    txn_info,
                    &other_data,
                    &mut curr_block_tries,
                    &mut tot_gas_used,
                )
            })
            .collect::<TraceParsingResult<Vec<_>>>()?;

        for (k, v) in curr_block_tries.state.items() {
            if let Some(v) = v.as_val() {
                let acc_data = rlp::decode::<AccountRlp>(v).unwrap();
                println!("(FULL) account data: {:x} --> {:#?}", k, acc_data);
            }
        }

        Self::pad_gen_inputs_with_dummy_inputs_if_needed(
            &mut txn_gen_inputs,
            &other_data,
            &initial_tries_for_dummies,
        );
        Ok(txn_gen_inputs)
    }

    fn create_initial_state_for_creating_proof_gen_ir(
        &self,
    ) -> (PartialTrieState, PartialTrieState, U256) {
        let curr_block_tries = PartialTrieState {
            state: self.tries.state.clone(),
            storage: self.tries.storage.clone(),
            ..Default::default()
        };

        // This is just a copy of `curr_block_tries`.
        let initial_tries_for_dummies = PartialTrieState {
            state: self.tries.state.clone(),
            storage: self.tries.storage.clone(),
            ..Default::default()
        };

        println!("State trie initial contents:");
        for (k, v) in curr_block_tries.state.items() {
            let v_str = match v {
                ValOrHash::Val(v) => hex::encode(&v),
                ValOrHash::Hash(h) => format!("{:x}", h),
            };

            println!("k: {} --> {}", k, v_str);
        }

        println!("Initial state Root: {:x}", curr_block_tries.state.hash());

        let tot_gas_used = U256::zero();

        (curr_block_tries, initial_tries_for_dummies, tot_gas_used)
    }

    fn process_txn_gen_input_into_ir(
        txn_idx: TxnIdx,
        txn_info: ProcessedTxnInfo,
        other_data: &OtherBlockData,
        curr_block_tries: &mut PartialTrieState,
        tot_gas_used: &mut U256,
    ) -> TraceParsingResult<TxnProofGenIR> {
        let tries = Self::create_minimal_partial_tries_needed_by_txn(
            curr_block_tries,
            &txn_info.nodes_used_by_txn,
            txn_idx,
            &other_data.b_data.b_meta.block_beneficiary,
        )?;

        let new_tot_gas_used = *tot_gas_used + txn_info.meta.gas_used;

        Self::apply_deltas_to_trie_state(
            curr_block_tries,
            txn_info.nodes_used_by_txn,
            &txn_info.meta,
            txn_idx,
        )?;

        let trie_roots_after = calculate_trie_input_hashes(curr_block_tries);
        println!(
            "Protocol expected trie roots after txn {}: {:?}",
            txn_idx, trie_roots_after
        );

        let gen_inputs = GenerationInputs {
            txn_number_before: txn_idx.into(),
            gas_used_before: *tot_gas_used,
            gas_used_after: new_tot_gas_used,
            signed_txn: txn_info.meta.txn_bytes,
            withdrawals: Vec::new(), /* TODO: Once this is added to the trace spec, add
                                      * it here... */
            tries,
            trie_roots_after,
            checkpoint_state_trie_root: other_data.checkpoint_state_trie_root,
            contract_code: txn_info.contract_code_accessed,
            block_metadata: other_data.b_data.b_meta.clone(),
            block_hashes: other_data.b_data.b_hashes.clone(),
        };

        let txn_proof_gen_ir = TxnProofGenIR {
            txn_idx,
            gen_inputs,
        };

        *tot_gas_used = new_tot_gas_used;

        Ok(txn_proof_gen_ir)
    }

    fn create_minimal_partial_tries_needed_by_txn(
        curr_block_tries: &mut PartialTrieState,
        nodes_used_by_txn: &NodesUsedByTxn,
        txn_idx: TxnIdx,
        _coin_base_addr: &Address,
    ) -> TraceParsingResult<TrieInputs> {
        let state_trie = create_minimal_state_partial_trie(
            &curr_block_tries.state,
            nodes_used_by_txn.state_accesses.iter().cloned(),
        )?;

        let _s: Vec<_> = state_trie
            .items()
            .map(|(_k, v)| match v {
                ValOrHash::Val(v) => format!("V - {}", hex::encode(v)),
                ValOrHash::Hash(h) => format!("H - {:x}", h),
            })
            .collect();

        // println!("Actual final sub state trie: {:#?}", s);

        // println!(
        //     "Querying the hash(H160::zero()) ({}):",
        //     hash(H160::zero().as_bytes())
        // );
        // state_trie.get(
        //     Nibbles::from_bytes_be(
        //         &hex::decode("
        // 5380c7b7ae81a58eb98d9c78de4a1fd7fd9535fc953ed2be602daaa41767312a")
        //             .unwrap(),
        //     )
        //     .unwrap(),
        // );
        // println!("DONE QUERY");

        // println!("State partial trie: {}", s);

        let txn_k = Nibbles::from_bytes_be(&rlp::encode(&txn_idx)).unwrap();
        // TODO: Replace cast once `eth_trie_utils` supports `into` for `usize...
        let transactions_trie =
            create_trie_subset_wrapped(&curr_block_tries.txn, once(txn_k), TrieType::Txn)?;

        let receipts_trie =
            create_trie_subset_wrapped(&curr_block_tries.receipt, once(txn_k), TrieType::Receipt)?;

        // TODO: Refactor so we can remove this vec alloc...
        let storage_access_vec = nodes_used_by_txn
            .storage_accesses
            .iter()
            .map(|(k, v)| (H256::from_slice(&k.bytes_be()), v.clone()))
            .collect::<Vec<_>>();

        let storage_tries = create_minimal_storage_partial_tries(
            &mut curr_block_tries.storage,
            &nodes_used_by_txn.state_accounts_with_no_accesses_but_storage_tries,
            storage_access_vec.iter(),
        )?;

        Ok(TrieInputs {
            state_trie,
            transactions_trie,
            receipts_trie,
            storage_tries,
        })
    }
    fn apply_deltas_to_trie_state(
        trie_state: &mut PartialTrieState,
        deltas: NodesUsedByTxn,
        meta: &TxnMetaState,
        txn_idx: TxnIdx,
    ) -> TraceParsingResult<()> {
        // Used for some errors. Note that the clone is very cheap.
        let state_trie_initial = trie_state.state.clone();

        for (hashed_acc_addr, storage_writes) in deltas.storage_writes {
            let storage_trie = trie_state
                .storage
                .get_mut(&H256::from_slice(&hashed_acc_addr.bytes_be()))
                .ok_or(TraceParsingError::MissingAccountStorageTrie(
                    H256::from_slice(&hashed_acc_addr.bytes_be()),
                ))?;

            for (slot, val) in storage_writes
                .into_iter()
                .map(|(k, v)| (Nibbles::from_h256_be(hash(&k.bytes_be())), v))
            {
                // If we are writing a zero, then we actually need to perform a delete.
                match val == ZERO_STORAGE_SLOT_VAL_RLPED {
                    false => storage_trie.insert(slot, val),
                    true => {
                        storage_trie.delete(slot);
                    }
                };
            }
        }

        // trie_state.state.insert(Nibbles::from_h256_be(hash(H160::zero().as_bytes())),
        // ValOrHash::Val(EMPTY_ACCOUNT_BYTES_RLPED.to_vec()));

        for (hashed_acc_addr, s_trie_writes) in deltas.state_writes {
            let val_k = Nibbles::from_h256_be(hashed_acc_addr);

            // If the account was created, then it will not exist in the trie.
            let val_bytes = trie_state
                .state
                .get(val_k)
                .unwrap_or(&EMPTY_ACCOUNT_BYTES_RLPED);

            let mut account = account_from_rlped_bytes(val_bytes)?;

            s_trie_writes.apply_writes_to_state_node(
                &mut account,
                &hashed_acc_addr,
                &trie_state.storage,
            )?;

            let updated_account_bytes = rlp::encode(&account);
            trie_state
                .state
                .insert(val_k, updated_account_bytes.to_vec());
        }

        // Remove any accounts that self-destructed.
        for hashed_addr in deltas.self_destructed_accounts {
            let k = Nibbles::from_h256_be(hashed_addr);

            let account_data = trie_state.state.get(k).ok_or_else(|| {
                TraceParsingError::NonExistentTrieEntry(
                    TrieType::State,
                    k,
                    state_trie_initial.hash(),
                )
            })?;
            let _account = account_from_rlped_bytes(account_data)?;

            trie_state
                .storage
                .remove(&hashed_addr)
                .ok_or(TraceParsingError::MissingAccountStorageTrie(hashed_addr))?;
            // TODO: Once the mechanism for resolving code hashes settles, we probably want
            // to also delete the code hash mapping here as well...

            trie_state.state.delete(k);
        }

        let txn_k = Nibbles::from_bytes_be(&rlp::encode(&txn_idx)).unwrap();
        trie_state.txn.insert(txn_k, meta.txn_bytes());

        trie_state
            .receipt
            .insert(txn_k, meta.receipt_node_bytes.as_ref());

        Ok(())
    }

    fn pad_gen_inputs_with_dummy_inputs_if_needed(
        gen_inputs: &mut Vec<TxnProofGenIR>,
        other_data: &OtherBlockData,
        initial_trie_state: &PartialTrieState,
    ) {
        match gen_inputs.len() {
            0 => {
                // Need to pad with two dummy txns.
                gen_inputs.extend(create_dummy_txn_pair_for_empty_block(
                    other_data,
                    initial_trie_state,
                ));
            }
            1 => {
                let dummy_txn = create_dummy_gen_input(other_data, initial_trie_state, 0);
                gen_inputs.insert(0, dummy_txn);
            }
            _ => (),
        }
    }
}

impl StateTrieWrites {
    fn apply_writes_to_state_node(
        &self,
        state_node: &mut AccountRlp,
        h_addr: &HashedAccountAddr,
        acc_storage_tries: &HashMap<HashedAccountAddr, HashedPartialTrie>,
    ) -> TraceParsingResult<()> {
        let storage_root_hash_change = match self.storage_trie_change {
            false => None,
            true => {
                let storage_trie = acc_storage_tries
                    .get(h_addr)
                    .ok_or(TraceParsingError::MissingAccountStorageTrie(*h_addr))?;

                Some(storage_trie.hash())
            }
        };

        if self.balance.is_some()
            || self.nonce.is_some()
            || self.code_hash.is_some()
            || storage_root_hash_change.is_some()
        {
            println!("DELTA FOR {:x}", h_addr);

            if let Some(v) = self.balance {
                println!("---- balance: {:x}", v);
            }

            if let Some(v) = self.nonce {
                println!("---- nonce: {:x}", v);
            }

            if let Some(v) = self.code_hash {
                println!("---- c_hash: {:x}", v);
            }

            if let Some(v) = storage_root_hash_change {
                println!("---- storage change: {:x}", v);
            }
        }

        update_val_if_some(&mut state_node.balance, self.balance);
        update_val_if_some(&mut state_node.nonce, self.nonce);
        update_val_if_some(&mut state_node.storage_root, storage_root_hash_change);
        update_val_if_some(&mut state_node.code_hash, self.code_hash);

        Ok(())
    }
}

fn calculate_trie_input_hashes(t_inputs: &PartialTrieState) -> TrieRoots {
    TrieRoots {
        state_root: t_inputs.state.hash(),
        transactions_root: t_inputs.txn.hash(),
        receipts_root: t_inputs.receipt.hash(),
    }
}

// We really want to get a trie with just a hash node here, and this is an easy
// way to do it.
fn create_fully_hashed_out_sub_partial_trie(trie: &HashedPartialTrie) -> HashedPartialTrie {
    // Impossible to actually fail with an empty iter.
    create_trie_subset(trie, once(0_u64)).unwrap()
}

fn create_dummy_txn_pair_for_empty_block(
    other_data: &OtherBlockData,
    initial_trie_state: &PartialTrieState,
) -> [TxnProofGenIR; 2] {
    [
        create_dummy_gen_input(other_data, initial_trie_state, 0),
        create_dummy_gen_input(other_data, initial_trie_state, 0),
    ]
}

fn create_dummy_gen_input(
    other_data: &OtherBlockData,
    initial_trie_state: &PartialTrieState,
    txn_idx: TxnIdx,
) -> TxnProofGenIR {
    let tries = create_dummy_proof_trie_inputs(initial_trie_state);

    let trie_roots_after = TrieRoots {
        state_root: tries.state_trie.hash(),
        transactions_root: EMPTY_TRIE_HASH,
        receipts_root: EMPTY_TRIE_HASH,
    };

    let gen_inputs = GenerationInputs {
        signed_txn: None,
        tries,
        trie_roots_after,
        checkpoint_state_trie_root: other_data.checkpoint_state_trie_root,
        block_metadata: other_data.b_data.b_meta.clone(),
        block_hashes: other_data.b_data.b_hashes.clone(),
        ..GenerationInputs::default()
    };

    gen_inputs_to_ir(gen_inputs, txn_idx)
}

impl TxnMetaState {
    fn txn_bytes(&self) -> Vec<u8> {
        match self.txn_bytes.as_ref() {
            Some(v) => v.clone(),
            None => Vec::default(),
        }
    }
}

fn gen_inputs_to_ir(gen_inputs: GenerationInputs, txn_idx: TxnIdx) -> TxnProofGenIR {
    TxnProofGenIR {
        txn_idx,
        gen_inputs,
    }
}

fn create_dummy_proof_trie_inputs(final_trie_state: &PartialTrieState) -> TrieInputs {
    let partial_sub_storage_tries: Vec<_> = final_trie_state
        .storage
        .iter()
        .map(|(hashed_acc_addr, s_trie)| {
            (
                *hashed_acc_addr,
                create_fully_hashed_out_sub_partial_trie(s_trie),
            )
        })
        .collect();

    TrieInputs {
        state_trie: create_fully_hashed_out_sub_partial_trie(&final_trie_state.state),
        transactions_trie: HashedPartialTrie::default(),
        receipts_trie: HashedPartialTrie::default(),
        storage_tries: partial_sub_storage_tries,
    }
}

fn create_minimal_state_partial_trie(
    state_trie: &HashedPartialTrie,
    state_accesses: impl Iterator<Item = HashedNodeAddr>,
) -> TraceParsingResult<HashedPartialTrie> {
    create_trie_subset_wrapped(
        state_trie,
        state_accesses.into_iter().map(Nibbles::from_h256_be),
        TrieType::State,
    )
}

// TODO!!!: We really need to be appending the empty storage tries to the base
// trie somewhere else! This is a big hack!
fn create_minimal_storage_partial_tries<'a>(
    storage_tries: &mut HashMap<HashedAccountAddr, HashedPartialTrie>,
    state_accounts_with_no_accesses_but_storage_tries: &HashMap<HashedAccountAddr, TrieRootHash>,
    accesses_per_account: impl Iterator<Item = &'a (HashedAccountAddr, Vec<HashedStorageAddrNibbles>)>,
) -> TraceParsingResult<Vec<(HashedAccountAddr, HashedPartialTrie)>> {
    accesses_per_account
        .map(|(h_addr, mem_accesses)| {
            // TODO: Clean up...
            let base_storage_trie = match storage_tries.get(&H256(h_addr.0)) {
                Some(s_trie) => s_trie,
                None => {
                    let trie = state_accounts_with_no_accesses_but_storage_tries
                        .get(h_addr)
                        .map(|s_root| HashedPartialTrie::new(Node::Hash(*s_root)))
                        .unwrap_or_default();
                    storage_tries.insert(*h_addr, trie); // TODO: Really change this...
                    storage_tries.get(h_addr).unwrap()
                }
            };

            let partial_storage_trie = create_trie_subset_wrapped(
                base_storage_trie,
                mem_accesses.iter().cloned(),
                TrieType::Storage,
            )?;

            Ok((*h_addr, partial_storage_trie))
        })
        .collect::<TraceParsingResult<_>>()
}

fn create_trie_subset_wrapped(
    trie: &HashedPartialTrie,
    accesses: impl Iterator<Item = Nibbles>,
    trie_type: TrieType,
) -> TraceParsingResult<HashedPartialTrie> {
    create_trie_subset(trie, accesses)
        .map_err(|_| TraceParsingError::MissingKeysCreatingSubPartialTrie(trie_type))
}

fn account_from_rlped_bytes(bytes: &[u8]) -> TraceParsingResult<AccountRlp> {
    rlp::decode(bytes)
        .map_err(|err| TraceParsingError::AccountDecode(hex::encode(bytes), err.to_string()))
}
