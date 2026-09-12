//! zkML Proof Example Template
//!
//! This template demonstrates how to create a zero-knowledge proof
//! for an ONNX model inference using JOLT Atlas.
//!
//! To use this template:
//! 1. Copy to `examples/your_example.rs` in the jolt-atlas repo
//! 2. Add the example to Cargo.toml:
//!    ```toml
//!    [[example]]
//!    name = "your_example"
//!    path = "examples/your_example.rs"
//!    ```
//! 3. Replace MODEL_PATH with your ONNX model path
//! 4. Adjust INPUT_SHAPE and input data generation
//! 5. Run: `cargo run --release --example your_example`

use ark_bn254::Fr;
use jolt_core::{poly::commitment::dory::DoryCommitmentScheme, transcripts::KeccakTranscript};
use onnx_tracer::{model, tensor::Tensor};
use std::path::PathBuf;
use zkml_jolt_core::jolt::JoltSNARK;

// Polynomial Commitment Scheme type
type PCS = DoryCommitmentScheme;

// ============================================================================
// CONFIGURATION - Modify these for your use case
// ============================================================================

/// Path to your ONNX model (relative to repo root)
const MODEL_PATH: &str = "onnx-tracer/models/perceptron/network.onnx";

/// Input tensor shape [batch_size, ...dimensions]
const INPUT_SHAPE: &[usize] = &[1, 4];

/// Memory size for prover (power of 2, increase if you get memory errors)
/// Common values: 1 << 14 (small), 1 << 20 (medium), 1 << 21 (large)
const MEMORY_SIZE: usize = 1 << 14;

// ============================================================================
// MAIN LOGIC
// ============================================================================

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("zkML Proof Generation Example");
    println!("==============================\n");

    // Step 1: Define model loader function
    let model_fn = || model(&PathBuf::from(MODEL_PATH));

    // Step 2: Generate input data
    // Replace this with your actual input data generation
    let input_data = generate_input_data();
    let input = Tensor::new(Some(&input_data), INPUT_SHAPE)?;

    println!("Model: {}", MODEL_PATH);
    println!("Input shape: {:?}", INPUT_SHAPE);
    println!("Input data (first 10): {:?}\n", &input_data[..input_data.len().min(10)]);

    // Step 3: Run model to verify output (optional but recommended)
    println!("Running model inference...");
    let model_instance = model_fn();
    let result = model_instance.forward(&[input.clone()])?;
    let output = &result.outputs[0];

    println!("Output shape: {:?}", output.shape());
    println!("Output values: {:?}\n", output.iter().collect::<Vec<_>>());

    // Step 4: Preprocess for proving (one-time setup)
    println!("Preprocessing for SNARK generation...");
    let preprocess_start = std::time::Instant::now();
    let preprocessing = JoltSNARK::<Fr, PCS, KeccakTranscript>::prover_preprocess(
        model_fn,
        MEMORY_SIZE,
    );
    println!("Preprocessing time: {:?}\n", preprocess_start.elapsed());

    // Step 5: Generate proof
    println!("Generating SNARK proof...");
    let prove_start = std::time::Instant::now();
    let (snark, program_io, _debug_info) = JoltSNARK::<Fr, PCS, KeccakTranscript>::prove(
        &preprocessing,
        model_fn,
        &input,
    );
    let prove_time = prove_start.elapsed();
    println!("Proving time: {:?}\n", prove_time);

    // Step 6: Verify proof
    println!("Verifying SNARK proof...");
    let verify_start = std::time::Instant::now();
    snark.verify(&(&preprocessing).into(), program_io, None)?;
    let verify_time = verify_start.elapsed();
    println!("Verification time: {:?}\n", verify_time);

    // Summary
    println!("==============================");
    println!("Proof generation successful!");
    println!("  Prove time:  {:?}", prove_time);
    println!("  Verify time: {:?}", verify_time);
    println!("==============================");

    Ok(())
}

/// Generate input data for the model
///
/// Modify this function to generate appropriate input for your model:
/// - For classification: feature vectors
/// - For image models: pixel values (usually scaled to integers)
/// - For text models: tokenized/embedded text
fn generate_input_data() -> Vec<i32> {
    let total_elements: usize = INPUT_SHAPE.iter().product();

    // Example: simple sequential data
    // Replace with your actual input generation logic
    (0..total_elements as i32).collect()

    // Alternative: random data
    // use rand::{Rng, SeedableRng, rngs::StdRng};
    // let mut rng = StdRng::seed_from_u64(42);
    // (0..total_elements).map(|_| rng.gen_range(-100..100)).collect()

    // Alternative: zeros
    // vec![0; total_elements]
}

// ============================================================================
// OPTIONAL: Add custom preprocessing functions below
// ============================================================================

/// Example: Text preprocessing for classification models
#[allow(dead_code)]
fn preprocess_text(text: &str, vocab_size: usize) -> Vec<i32> {
    // Simple bag-of-words style encoding
    let mut vec = vec![0; vocab_size];
    for (i, _word) in text.split_whitespace().enumerate() {
        if i < vocab_size {
            vec[i] = 1;  // Presence indicator
        }
    }
    vec
}

/// Example: Image preprocessing (normalize to integer range)
#[allow(dead_code)]
fn preprocess_image(pixels: &[f32], scale: i32) -> Vec<i32> {
    pixels.iter().map(|&p| (p * scale as f32) as i32).collect()
}
