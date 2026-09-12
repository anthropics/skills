# Jolt Atlas Architecture

This document describes the crate structure, key types, dependency graph, and proving pipeline of jolt-atlas.

## Crate Dependency Graph

```
jolt-atlas (workspace root)
├── jolt-atlas-core          # Main proving engine, GPT-scale examples
│   ├── atlas-onnx-tracer    # Extended ONNX tracing for atlas-core
│   ├── joltworks            # Polynomial commitment schemes (HyperKZG)
│   └── common               # Shared utilities
├── zkml-jolt-core           # Original zkML SNARK logic (Dory PCS)
│   └── onnx-tracer          # ONNX model loading, tensor ops, graph tracing
└── onnx-tracer              # Also used directly by root examples
```

### External dependencies

| Dependency | Source | Purpose |
|---|---|---|
| `jolt-core` | [a16z/jolt](https://github.com/a16z/jolt) | Base JOLT proving system, commitment schemes, transcripts |
| `ark-bn254` | [arkworks](https://github.com/arkworks-rs) | BN254 elliptic curve field elements (`Fr`) |
| `ark-serialize` | arkworks | Canonical serialization/deserialization for proofs |
| `ark-ff` | arkworks | Finite field traits and arithmetic |

## Workspace Crates in Detail

### `jolt-atlas` (root)

The workspace root. Contains top-level examples (`article_classification`, `authorization`, `proof_round_trip`) that use `zkml-jolt-core` and `onnx-tracer` with the Dory commitment scheme. These are the simplest entry points for small models.

### `jolt-atlas-core`

The main proving/verification engine for larger models. Uses HyperKZG commitment scheme instead of Dory. Contains examples for nanoGPT, GPT-2, transformer, minigpt, and microgpt. This is the crate to use for production-scale proofs.

Key modules:
- `src/` — Proving and verification logic
- `examples/` — End-to-end prove/verify examples for GPT-scale models

### `onnx-tracer`

Handles ONNX model loading, graph tracing, and tensor operations. Core types:

- `Model` — Loaded ONNX computational graph
- `Tensor<i32>` — Fixed-point integer tensor (all values are `i32`)
- `ProgramIO` — Input/output witness for the SNARK (serializable via serde)
- `RunArgs` — Configuration for model execution (scale factors, etc.)
- `builder` module — Pre-built model loader functions (e.g., `builder::simple_mlp_small_model`)

Loading a model:
```rust
use onnx_tracer::model;
use std::path::PathBuf;

let model_instance = model(&PathBuf::from("onnx-tracer/models/perceptron/network.onnx"));
let result = model_instance.forward(&[input_tensor])?;
let output = &result.outputs[0];
```

### `atlas-onnx-tracer`

Extended tracing utilities used by `jolt-atlas-core`. Provides model loading for larger architectures (GPT-2, nanoGPT) with additional graph optimization passes.

### `zkml-jolt-core`

Core zkML SNARK implementation. Contains:

- `jolt` module — `JoltSNARK` type and proving/verification functions
- `benches` module — Benchmark definitions (`BenchType` enum)
- `main.rs` — CLI for profiling (`--name`, `--format`)

### `joltworks`

Polynomial commitment scheme implementations and supporting cryptographic operations. Provides the bridge between the JOLT proving system and arkworks.

### `common`

Shared utility types and helper functions used across crates.

## Key Types

### `JoltSNARK<F, PCS, FS>`

The central proving/verification type. Generic over:

- `F` — Scalar field (always `ark_bn254::Fr` in practice)
- `PCS` — Polynomial commitment scheme (`DoryCommitmentScheme` for small models, HyperKZG for large)
- `FS` — Fiat-Shamir transcript (`KeccakTranscript`)

Static methods:

| Method | Signature (simplified) | Description |
|---|---|---|
| `prover_preprocess` | `(model_fn, max_trace_length) -> JoltProverPreprocessing` | One-time setup: generates proving/verifying keys |
| `prove` | `(&preprocessing, model_fn, &input) -> (Self, ProgramIO, DebugInfo)` | Generate SNARK proof for a given input |
| `verify` | `(self, &verifier_preprocessing, program_io, debug) -> Result<()>` | Verify the proof |

### `JoltProverPreprocessing<F, PCS>`

Output of `prover_preprocess`. Contains the structured reference string (SRS), proving key, and verifying key. Expensive to compute but reusable across multiple proofs for the same model.

Convertible to `JoltVerifierPreprocessing` via `Into`:
```rust
let verifier_preprocessing: JoltVerifierPreprocessing<Fr, PCS> = (&preprocessing).into();
```

### `JoltVerifierPreprocessing<F, PCS>`

Subset of preprocessing data needed only for verification. Smaller than the full prover preprocessing. This is what a verifier needs.

### `ProgramIO`

The public input/output witness. Serializable via serde (`serde_json::to_string`). Contains the model inputs and outputs that are committed to in the proof.

### `Model`

An ONNX computational graph loaded into memory. Created via `onnx_tracer::model(&path)` or builder functions. Supports:

- `forward(&[Tensor]) -> Result<RunResult>` — Execute inference
- Graph inspection and tracing

### `Tensor<i32>`

Fixed-point integer tensor. Created via:
```rust
let tensor = Tensor::new(Some(&data), &[dim1, dim2, ...])?;
```

Supports standard tensor operations, iteration, cloning, and shape queries.

## Proving Pipeline (Detailed)

### Step 1: Model Loading

```rust
let model_fn = || model(&PathBuf::from("path/to/model.onnx"));
```

The model function is a closure that returns a fresh `Model` instance. It is called multiple times during proving (once for tracing, once for proof generation), so it must be repeatable.

### Step 2: Preprocessing (Key Generation)

```rust
let preprocessing = JoltSNARK::<Fr, PCS, KeccakTranscript>::prover_preprocess(
    model_fn,
    max_trace_length,  // power of 2
);
```

This step:
1. Traces the model to determine the computation graph structure
2. Generates the structured reference string (SRS)
3. Computes the proving key and verifying key
4. Returns `JoltProverPreprocessing` containing all material

The `max_trace_length` parameter controls how much memory the prover allocates. Must be a power of 2 and large enough to hold the full execution trace.

### Step 3: Proof Generation

```rust
let (snark, program_io, debug_info) = JoltSNARK::<Fr, PCS, KeccakTranscript>::prove(
    &preprocessing,
    model_fn,
    &input,
);
```

This step:
1. Re-executes the model on the input to generate the witness
2. Commits to the witness polynomials
3. Runs the sumcheck protocol
4. Produces the SNARK proof and the public `ProgramIO`

### Step 4: Verification

```rust
snark.verify(&verifier_preprocessing, program_io, None)?;
```

The verifier checks:
1. All sumcheck rounds are consistent
2. Polynomial commitments open correctly
3. The claimed input/output matches the committed values

Verification is significantly faster than proving (~100 ms vs seconds/minutes).

## Proof Serialization

Proofs can be serialized for storage or transmission using arkworks' `CanonicalSerialize`:

```rust
use ark_serialize::{CanonicalSerialize, CanonicalDeserialize};

// Serialize
let mut buffer = Vec::new();
snark.serialize_compressed(&mut buffer)?;

// Deserialize
let deserialized = JoltSNARK::<Fr, PCS, KeccakTranscript>::deserialize_compressed(&buffer[..])?;
```

`ProgramIO` is serialized via serde/JSON:

```rust
let json = serde_json::to_string(&program_io)?;
let deserialized: ProgramIO = serde_json::from_str(&json)?;
```

See [../templates/proof_round_trip.rs](../templates/proof_round_trip.rs) for a complete working example.

## DAG-Based Proof Structure

The computation is represented as a directed acyclic graph (DAG) where:
- Nodes represent operations (Add, MatMul, ReLU, etc.)
- Edges represent tensor data flow
- The graph is topologically sorted for execution
- Each node's execution trace is committed to independently
- The sumcheck protocol ties all commitments together

This DAG structure enables:
- Parallelism in witness generation
- Incremental verification of sub-computations
- Natural mapping from ONNX graph structure

## Commitment Schemes

### DoryCommitmentScheme

Used in `zkml-jolt-core` and root workspace examples. Transparent (no trusted setup), based on the Dory polynomial commitment scheme. Good for smaller models and development.

### HyperKZG

Used in `jolt-atlas-core` for production-scale proofs (nanoGPT, GPT-2). Based on KZG commitments with hyperplonk-style multilinear extensions. Requires a structured reference string but is more efficient for large computations.

Both schemes implement the same trait interface, so switching between them requires only changing the type alias:

```rust
// For small models (zkml-jolt-core style)
type PCS = DoryCommitmentScheme;

// For large models (jolt-atlas-core style)
// type PCS = HyperKZGScheme;  // actual type depends on jolt-atlas-core imports
```
