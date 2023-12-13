use core::fmt;

use thiserror::Error;

use crate::{
    processed_block_trace::ProcessedBlockTrace,
    trace_protocol::BlockTrace,
    types::{PartialTrieState, TxnProofGenIR},
};

// All account storage roots in accounts exist in the storage trie after each
// txn. All account code hashes have a matching entry for every txn.
// All pre-image leafs are accessed by the traces.
// All final storage slots mentioned in trace match result from rpc call to full
// node. All account entry fields match call to rpc call to full node.
// Check that all roots match rpc call to full node.

pub(crate) type TraceVerificationResult = Result<(), TraceVerificationErrors>;

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
pub(crate) enum TraceVerificationError {}

pub(crate) fn verify_proof_gen_ir(_b_trace: &BlockTrace) -> TraceVerificationResult {
    todo!();
}

fn verify_all_account_storage_roots_exist_in_account_pre_state() {
    todo!();
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
