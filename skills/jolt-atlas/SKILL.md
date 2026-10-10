---
name: jolt-atlas
description: Zero-knowledge machine learning (zkML) framework for generating cryptographic proofs of ML inference from ONNX models. Activate when the user mentions zkML, zero-knowledge machine learning, jolt-atlas, SNARK proofs for ML, ONNX model verification, proof generation for neural networks, or the JOLT proving system.
homepage: https://github.com/ICME-Lab/jolt-atlas
user-invocable: true
metadata: {"zkml":{"framework":"jolt-atlas","proving_system":"JOLT","curve":"BN254","commitment":"HyperKZG"}}
---

# Jolt Atlas — Zero-Knowledge Machine Learning

Jolt Atlas is a zkML framework that generates cryptographic proofs of ML inference correctness from ONNX models. It extends the [JOLT](https://github.com/a16z/jolt) proving system (a16z Crypto) and replaces expensive circuit-based approaches with **lookup tables** — no quotient polynomials, no byte decomposition, no grand products, no permutation checks, no complicated circuits. Core principle: reduce commitment costs via sumcheck while committing only to small-value polynomials.

**Repository:** <https://github.com/ICME-Lab/jolt-atlas>
**Authors:** ICME Labs (Wyatt Benno, Khalil Gibran Hassam, Alberto Centelles Hidalgo, Antoine Douchet)

## Prerequisites

1. **Rust toolchain** (nightly recommended):
   ```bash
   curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
   rustup default nightly
   ```
2. **Clone the repository:**
   ```bash
   git clone https://github.com/ICME-Lab/jolt-atlas.git
   cd jolt-atlas
   ```
3. **Build:**
   ```bash
   cargo build --release
   ```

## Core Workflow

Every zkML proof follows a four-step pipeline:

1. **Load ONNX model** — `onnx_tracer::model(&path)` or a builder function
2. **Create input tensor** — `Tensor::new(Some(&data), &shape)`
3. **Preprocess + prove** — `JoltSNARK::prover_preprocess(model_fn, mem_size)` then `JoltSNARK::prove(&preprocessing, model_fn, &input)`
4. **Verify** — `snark.verify(&verifier_preprocessing, program_io, None)`

## Quick-Reference Code Pattern

```rust
use ark_bn254::Fr;
use jolt_core::{poly::commitment::dory::DoryCommitmentScheme, transcripts::KeccakTranscript};
use onnx_tracer::{model, tensor::Tensor};
use std::path::PathBuf;
use zkml_jolt_core::jolt::JoltSNARK;

type PCS = DoryCommitmentScheme;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let model_fn = || model(&PathBuf::from("onnx-tracer/models/perceptron/network.onnx"));
    let input = Tensor::new(Some(&vec![1, 2, 3, 4]), &[1, 4])?;

    // Preprocess (one-time)
    let preprocessing = JoltSNARK::<Fr, PCS, KeccakTranscript>::prover_preprocess(
        model_fn, 1 << 14,
    );

    // Prove
    let (snark, program_io, _dbg) = JoltSNARK::<Fr, PCS, KeccakTranscript>::prove(
        &preprocessing, model_fn, &input,
    );

    // Verify
    snark.verify(&(&preprocessing).into(), program_io, None)?;
    println!("Proof verified!");
    Ok(())
}
```

See [templates/zkml_example.rs](templates/zkml_example.rs) for a fully commented version with config section and preprocessing helpers.

## Workspace Crates

| Crate | Path | Purpose |
|---|---|---|
| `jolt-atlas` | `/` (root) | Workspace root, top-level examples |
| `jolt-atlas-core` | `jolt-atlas-core/` | Main proving/verification engine, examples (nanoGPT, GPT-2, transformer) |
| `onnx-tracer` | `onnx-tracer/` | ONNX model loading, graph tracing, tensor ops |
| `atlas-onnx-tracer` | `atlas-onnx-tracer/` | Extended ONNX tracing utilities |
| `zkml-jolt-core` | `zkml-jolt-core/` | Core zkML SNARK logic, benchmarks, profiling CLI |
| `joltworks` | `joltworks/` | Polynomial commitment scheme support |
| `common` | `common/` | Shared utilities |

## Available Examples

### Root workspace examples (`examples/`)

```bash
cargo run --release --example article_classification
cargo run --release --example authorization
cargo run --release --example proof_round_trip
```

### jolt-atlas-core examples (`jolt-atlas-core/examples/`)

```bash
cargo run --release --package jolt-atlas-core --example nanoGPT
cargo run --release --package jolt-atlas-core --example transformer
cargo run --release --package jolt-atlas-core --example minigpt
cargo run --release --package jolt-atlas-core --example microgpt
cargo run --release --package jolt-atlas-core --example gpt2
```

> **GPT-2 note:** The model is not checked into the repo. Run `python scripts/download_gpt2.py` first to download and export via Hugging Face Optimum.

## Pre-Trained Models

Models live in `onnx-tracer/models/`:

| Model | Use Case |
|---|---|
| `perceptron` | Simple MLP baseline |
| `article_classification` | Text categorization (5 classes) |
| `authorization` | Transaction approval decisions |
| `self_attention` | Transformer attention layer |
| `nanoGPT` | ~0.25M-param GPT (4 transformer layers) |
| `sentiment0`, `sentiment1` | Sentiment analysis |
| `bge-m3` | Embedding model |
| `ffn_gelu`, `ffn_tanh` | Feed-forward networks with different activations |
| `layernorm_*` | Layer normalization variants |

GPT-2 (125M params) is downloaded separately via `scripts/download_gpt2.py` into `atlas-onnx-tracer/models/gpt2/`.

## Memory Size Tuning

The `max_trace_length` parameter passed to `prover_preprocess` must be a power of 2. Larger values support bigger models but use more RAM:

| Value | Hex | Typical Use | Approx. RAM |
|---|---|---|---|
| `1 << 12` | 4,096 | Tiny models, round-trip tests | < 1 GB |
| `1 << 14` | 16,384 | Perceptron, small MLPs | ~1 GB |
| `1 << 16` | 65,536 | Article classification | ~2 GB |
| `1 << 18` | 262,144 | Mid-size models | ~3 GB |
| `1 << 20` | 1,048,576 | Self-attention, transformers | ~5 GB |
| `1 << 21` | 2,097,152 | Large transformers, nanoGPT | ~8 GB |
| `1 << 22`+ | 4,194,304+ | GPT-2 scale | 16+ GB |

If you see memory errors or the prover panics, double the value to the next power of 2.

## Performance Benchmarks

Measured on MacBook Pro M3, 16 GB RAM:

### nanoGPT (~0.25M params)

| Stage | JOLT Atlas | ezkl (comparison) |
|---|---|---|
| Key generation | 0.246 s | ~404 s combined |
| Proof time | **~14 s** | ~237 s |
| Verify time | 0.517 s | 0.34 s |

**~17× speed-up** on proof generation versus ezkl.

### GPT-2 (125M params)

| Stage | Wall Clock |
|---|---|
| Key generation | 0.872 s |
| Witness generation | ~7.5 s |
| Commitment time | ~3.5 s |
| Sumcheck proving | ~16 s |
| Reduction opening proof | ~7 s |
| HyperKZG prove | ~3 s |
| **End-to-end total** | **~38 s** |

### Other workloads (zkml-jolt-core profiler)

| Workload | Prove Time | Verify Time | Peak Memory |
|---|---|---|---|
| Transformer self-attention | ~20.8 s | ~143 ms | ~5.6 GB |
| Article classification | ~0.7 s | — | — |
| Perceptron MLP | ~800 ms | — | — |

## Profiling

Run from the `zkml-jolt-core/` directory:

```bash
# Terminal output
cargo run -r -- profile --name mlp --format default
cargo run -r -- profile --name article-classification --format default
cargo run -r -- profile --name self-attention --format default

# Chrome tracing (open chrome://tracing, load the generated JSON)
cargo run -r -- profile --name self-attention --format chrome
```

For jolt-atlas-core examples, append `-- --trace` or `-- --trace-terminal`:

```bash
cargo run --release --package jolt-atlas-core --example nanoGPT -- --trace
cargo run --release --package jolt-atlas-core --example nanoGPT -- --trace-terminal
```

## Key Concepts

- **BN254** — Elliptic curve used as the scalar field (`ark_bn254::Fr`).
- **HyperKZG** — Polynomial commitment scheme used by jolt-atlas-core for GPT-scale proofs. The older `DoryCommitmentScheme` is used in zkml-jolt-core examples.
- **Keccak transcript** — Fiat-Shamir transcript implementation for non-interactivity.
- **Sumcheck protocol** — Core proof mechanism; avoids circuit representation entirely.
- **Lookup tables (JOLT)** — Non-linear activations (ReLU, Softmax) resolved via lookup instead of arithmetic circuits.
- **Neural teleportation** — Model transformation that folds batch-norm layers into adjacent linear layers, reducing proof complexity. See [references/onnx-operations.md](references/onnx-operations.md).
- **Fixed-point arithmetic** — All tensor values are `i32`; floating-point weights are quantized during ONNX tracing with configurable scale factors.

## Supported Instructions

Add, Sub, Mul, MatMul, Einsum, Relu, Sigmoid, Erf, Gelu, Tanh, Softmax, LayerNorm, Conv, MaxPool, AveragePool, Flatten, Reshape, Transpose, Concat, Split, Gather, Unsqueeze, Squeeze, Expand, Slice, Pad, Cast, BatchNorm, Dropout (identity at inference), Constant, ConstantOfShape, Where, Shape, Pow, Sqrt, Reciprocal, Log, Exp, Clip, ReduceMean.

See [references/onnx-operations.md](references/onnx-operations.md) for detailed descriptions and limitations.

## Reference Files

- [references/architecture.md](references/architecture.md) — Crate architecture, key types, dependency graph, proving pipeline
- [references/onnx-operations.md](references/onnx-operations.md) — Supported ops, teleportation, fixed-point details
- [references/troubleshooting.md](references/troubleshooting.md) — Common errors, memory tuning, debugging

## Templates

- [templates/zkml_example.rs](templates/zkml_example.rs) — Full proof generation template with config section and helpers
- [templates/proof_round_trip.rs](templates/proof_round_trip.rs) — Proof serialization and re-verification round-trip
