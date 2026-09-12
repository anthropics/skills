# Troubleshooting

Common issues when working with jolt-atlas and how to resolve them.

## Memory Errors During Proving

**Symptom:** Panic with "index out of bounds" or "memory allocation failed" during `prover_preprocess` or `prove`.

**Cause:** The `max_trace_length` parameter is too small for the model's computation trace.

**Fix:** Double the value to the next power of 2:

```rust
// Too small — causes memory errors
let preprocessing = JoltSNARK::<Fr, PCS, KeccakTranscript>::prover_preprocess(model_fn, 1 << 14);

// Try the next power of 2
let preprocessing = JoltSNARK::<Fr, PCS, KeccakTranscript>::prover_preprocess(model_fn, 1 << 16);
```

Size guide:

| Model complexity | Start with | Max reasonable |
|---|---|---|
| Perceptron / tiny MLP | `1 << 12` | `1 << 14` |
| Article classification | `1 << 14` | `1 << 18` |
| Self-attention layer | `1 << 18` | `1 << 21` |
| nanoGPT | `1 << 20` | `1 << 22` |
| GPT-2 | `1 << 22` | `1 << 24` |

Also ensure you have sufficient system RAM. Transformer-scale models need 6+ GB, GPT-2 needs 16+ GB.

## Sumcheck Verification Failures

**Symptom:** `verify()` returns an error about sumcheck round mismatch or incorrect evaluation.

**Known issue:** See [GitHub issue #88](https://github.com/ICME-Lab/jolt-atlas/issues/88) for tracked sumcheck verification edge cases.

**Possible causes:**
1. `max_trace_length` too small — the trace was truncated, producing an inconsistent proof. Increase the value.
2. Numeric overflow in fixed-point arithmetic — intermediate values exceeded `i32` range. Reduce the scale factor or simplify the model.
3. Mismatched preprocessing — the `verifier_preprocessing` was derived from a different `prover_preprocess` call or a different model. Ensure they match.

**Debugging steps:**
1. Run the model forward pass separately and check output values are reasonable
2. Try a smaller model first to confirm the pipeline works
3. Enable debug info: the third return value from `prove()` contains diagnostic data

## Model Loading Failures

**Symptom:** Panic or error when calling `model(&path)` or during `forward()`.

**Possible causes:**

1. **Wrong file path:** Verify the ONNX file exists at the specified path:
   ```bash
   ls -la onnx-tracer/models/your_model/network.onnx
   ```

2. **Unsupported ONNX operation:** The model uses an op not in the supported instruction set. The error message usually names the unsupported op. See [onnx-operations.md](onnx-operations.md) for the full list.

3. **Dynamic shapes:** The ONNX model was exported with dynamic axes. Re-export with static shapes:
   ```python
   torch.onnx.export(model, input, "model.onnx", dynamic_axes=None)
   ```

4. **Corrupted ONNX file:** Re-export from PyTorch or validate with:
   ```python
   import onnx
   model = onnx.load("model.onnx")
   onnx.checker.check_model(model)
   ```

## Slow Compilation

**Symptom:** `cargo build` takes a very long time (10+ minutes on first build).

**This is expected.** jolt-atlas has heavy dependencies (arkworks, jolt-core) with extensive generic code. Subsequent incremental builds are much faster.

**Tips:**
- Always use `--release` for running examples (debug builds are extremely slow at runtime)
- Use `cargo build --release` once, then run examples — they won't recompile unless source changes
- If iterating on your own example code, the incremental rebuild should be fast
- Consider using `sccache` or `mold` linker for faster link times:
  ```bash
  # Install mold linker
  # Add to .cargo/config.toml:
  # [target.x86_64-unknown-linux-gnu]
  # linker = "clang"
  # rustflags = ["-C", "link-arg=-fuse-ld=mold"]
  ```

## Overflow in onnx-tracer

**Symptom:** Panic with "attempt to multiply with overflow" or "attempt to add with overflow" during model tracing.

**Cause:** The fixed-point integer values exceeded `i32` range during matrix multiplication or accumulation.

**Fix:**
1. Reduce the quantization scale factor in `RunArgs`
2. Check that your input values are reasonable (not excessively large)
3. Simplify the model (fewer layers, smaller weight magnitudes)
4. Check for weights with very large magnitudes in the original model

## Chrome Tracing / Profiling

For performance analysis, generate Chrome tracing output:

```bash
# zkml-jolt-core profiler
cd zkml-jolt-core
cargo run -r -- profile --name self-attention --format chrome
# Opens chrome://tracing in browser, load the generated trace-*.json

# jolt-atlas-core examples
cargo run --release --package jolt-atlas-core --example nanoGPT -- --trace
# Terminal timing output
cargo run --release --package jolt-atlas-core --example nanoGPT -- --trace-terminal
```

The Chrome tracing view shows:
- Time spent in each proving stage (commitment, sumcheck, opening)
- Witness generation breakdown
- Memory allocation patterns

## Running Tests

```bash
# All workspace tests
cargo test --release

# Specific crate tests
cargo test --release -p onnx-tracer
cargo test --release -p zkml-jolt-core
cargo test --release -p jolt-atlas-core

# Single test
cargo test --release -p zkml-jolt-core -- test_name
```

Use `--release` for tests too — debug mode is orders of magnitude slower for cryptographic operations.

## Common Cargo.toml Patterns

When adding a new example to the jolt-atlas workspace:

```toml
[[example]]
name = "my_example"
path = "examples/my_example.rs"
```

Required dependencies for proof generation (root workspace):

```toml
[dependencies]
ark-bn254 = "0.4"
ark-serialize = { version = "0.4", features = ["derive"] }
jolt-core = { path = "path/to/jolt-core" }
onnx-tracer = { path = "onnx-tracer" }
zkml-jolt-core = { path = "zkml-jolt-core" }
serde_json = "1"
```

For jolt-atlas-core examples, dependencies are already declared in `jolt-atlas-core/Cargo.toml`.

## Getting Help

- **GitHub Issues:** <https://github.com/ICME-Lab/jolt-atlas/issues>
- **JOLT Paper:** <https://eprint.iacr.org/2023/1217>
- **a16z JOLT docs:** <https://github.com/a16z/jolt>
