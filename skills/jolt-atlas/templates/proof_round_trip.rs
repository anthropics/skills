//! Proof Serialization Round-Trip Template
//!
//! Demonstrates how to serialize a JOLT Atlas SNARK proof and ProgramIO
//! to bytes/JSON, deserialize them, and re-verify. This pattern is essential
//! for real-world usage where proofs are stored, transmitted, or verified
//! by a separate party.
//!
//! Key dependencies:
//!   ark-serialize = { version = "0.4", features = ["derive"] }
//!   serde_json = "1"
//!
//! To use:
//! 1. Copy to `examples/your_round_trip.rs` in the jolt-atlas repo
//! 2. Add to Cargo.toml as an [[example]]
//! 3. Run: `cargo run --release --example your_round_trip`

use ark_bn254::Fr;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use jolt_core::{poly::commitment::dory::DoryCommitmentScheme, transcripts::KeccakTranscript};
use onnx_tracer::{builder, tensor::Tensor, ProgramIO};
use zkml_jolt_core::jolt::{JoltSNARK, JoltVerifierPreprocessing};

#[allow(clippy::upper_case_acronyms)]
type PCS = DoryCommitmentScheme;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("Proof serialization round-trip test");
    println!("====================================\n");

    // Create input tensor
    let input_data = vec![1, 2, 3, 4];
    let shape = [1, 4];
    let input_tensor = Tensor::new(Some(&input_data), &shape)?;

    // Preprocess and generate proof
    let max_trace_length = 1 << 12;
    let preprocessing = JoltSNARK::<Fr, PCS, KeccakTranscript>::prover_preprocess(
        builder::simple_mlp_small_model,
        max_trace_length,
    );
    let verifier_preprocessing: JoltVerifierPreprocessing<Fr, PCS> = (&preprocessing).into();

    let (snark, program_io, _debug_info) = JoltSNARK::<Fr, PCS, KeccakTranscript>::prove(
        &preprocessing,
        builder::simple_mlp_small_model,
        &input_tensor,
    );

    // Verify original proof
    snark
        .clone()
        .verify(&verifier_preprocessing, program_io.clone(), None)
        .expect("original proof should verify");
    println!("✓ Original proof verified");

    // Serialize proof to bytes (ark-serialize CanonicalSerialize)
    let mut proof_buffer = Vec::new();
    snark
        .serialize_compressed(&mut proof_buffer)
        .expect("proof serialization should succeed");
    println!("✓ Proof serialized ({} bytes)", proof_buffer.len());

    // Serialize ProgramIO to JSON (serde)
    let program_io_json =
        serde_json::to_string(&program_io).expect("program_io serialization should succeed");
    println!("✓ ProgramIO serialized ({} bytes)", program_io_json.len());

    // Deserialize proof from bytes
    let deserialized_snark =
        JoltSNARK::<Fr, PCS, KeccakTranscript>::deserialize_compressed(proof_buffer.as_slice())
            .expect("proof deserialization should succeed");
    println!("✓ Proof deserialized");

    // Deserialize ProgramIO from JSON
    let deserialized_program_io: ProgramIO =
        serde_json::from_str(&program_io_json).expect("program_io deserialization should succeed");
    println!("✓ ProgramIO deserialized");

    // Verify deserialized proof with deserialized ProgramIO
    deserialized_snark
        .verify(&verifier_preprocessing, deserialized_program_io, None)
        .expect("deserialized proof should verify");
    println!("✓ Deserialized proof verified with deserialized ProgramIO\n");

    println!("Round-trip serialization successful!");
    Ok(())
}
