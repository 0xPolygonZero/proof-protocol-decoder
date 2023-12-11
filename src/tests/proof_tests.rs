use paste::paste;
use plonky_block_proof_gen::proof_types::GeneratedBlockProof;
use serde::{Deserialize, Serialize};

use crate::{
    processed_block_trace::ProcessingMeta,
    trace_protocol::BlockTrace,
    types::{CodeHashResolveFunc, OtherBlockData, TxnProofGenIR},
};

macro_rules! gen_proof_test {
    ($test_payload_name:ident) => {
        paste! {
            #[test]
            fn $test_payload_name() {
                let payload_str = include_str!(concat!("payloads/", stringify!($test_payload_name), ".json"));
                let t_input = serde_json::from_str(payload_str).unwrap();

                generate_and_verify_block_proof_from_inputs(t_input);
            }
        }
    };
}

#[derive(Debug, Deserialize, Serialize)]
pub(super) struct ProofTestInput {
    pub(super) prev_proof: Option<GeneratedBlockProof>,
    pub(super) block_trace: BlockTrace,
    pub(super) other_data: OtherBlockData,
}

fn generate_and_verify_block_proof_from_inputs(t_input: ProofTestInput) {
    let p_meta = create_fake_processing_meta();
    let ir = t_input
        .block_trace
        .into_txn_proof_gen_ir(&p_meta, t_input.other_data)
        .unwrap();

    generate_block_proof(&ir);
}

fn generate_block_proof(_ir: &[TxnProofGenIR]) -> GeneratedBlockProof {
    // Just do simple aggregation and always merge neighbors.
    // Eg. (for 7 txns):
    // Pass 1: 0, 1, 2, 3, 4, 5, 6           (7 txn proofs)
    //
    // Pass 2: (0,1), (2,3) (4,5), 6         (3 agg proofs)
    //           ^      ^     ^
    // Pass 3: ((0,1), (1,2)), ((4,5), 6)    (2 agg proofs)
    //               ^              ^
    // Pass 4: ((0,1), (1,2)), ((4,5), 6)    (1 agg proof)
    //                  ^
    // Pass 5: [((0,1), (1,2)), ((4,5), 6)]  (block proof)

    todo!()
}

fn create_fake_processing_meta() -> ProcessingMeta<impl CodeHashResolveFunc> {
    ProcessingMeta::new(|_| todo!())
}

gen_proof_test!(proof_test_payload_1);
