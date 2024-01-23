#![feature(linked_list_cursors)]
#![feature(trait_alias)]
#![feature(iter_array_chunks)]

pub mod compact;
pub mod decoding;
mod deserializers;
pub mod processed_block_trace;
pub mod proof_gen_types;
pub mod trace_protocol;

// TODO: Consider moving behind a feature flag...
pub mod trace_debug_tooling;
pub mod types;
pub mod utils;
