# Reproducibility Protocol

Defines how validate mode verifies reproducibility of code experiments by re-running and comparing.

## Applicability

- **Applicable**: Any experiment with an executable command and recorded original results
- **Environment-sensitive but still comparable**: Hardware-dependent benchmarks, GPU training runs, OS-sensitive pipelines where the environment can be documented and approximately matched
- **Not applicable**: Human studies, external API calls with non-deterministic responses, experiments whose original environment can no longer be reconstructed at all
- If not applicable, skip reproducibility verification and report: "Reproducibility: N/A — [reason]"

## Procedure

### Step 1: Classify Experiment Determinism

| Type | Criteria | Expected Outcome |
|------|----------|-----------------|
| **Deterministic** | Same seed, same data, same code, same environment | Exact match required |
| **Stochastic** | Random elements (different seed, dropout, data augmentation) | Statistical equivalence within default tolerance |
| **Environment-sensitive** | Results depend on hardware, OS, driver, or library version | Document environment, compare with wider tolerance, do not compare timing metrics |

Ask user: "Is this experiment deterministic, stochastic, or environment-sensitive (for example hardware/OS dependent)?"

### Step 2: Re-Run

1. Delegate to code_runner_agent with the same command and working directory
2. code_runner_agent runs full EXECUTE → MONITOR → COLLECT cycle
3. Collect new experiment_result

### Step 3: Compare

**Deterministic comparison:**
- For each numeric metric: `abs(original - rerun)` must be exactly 0
- For output files: byte-for-byte comparison (`diff` or hash)
- Any difference = `MISMATCH`

**Stochastic comparison:**
- For each numeric metric: `abs(original - rerun) / max(abs(original), abs(rerun), epsilon)` must be < threshold
- Default threshold: 5% relative difference
- User can override with `reproducibility_threshold`
- For distributions: compare summary statistics (mean, std, min, max)

**Environment-sensitive comparison:**
- Record environment details first: hardware, OS, major library/toolchain versions
- For each numeric metric: `abs(original - rerun) / max(abs(original), abs(rerun), epsilon)` must be < threshold
- Default threshold: 10% relative difference unless the user specifies a tighter benchmark tolerance
- Compare structure and artifact presence; do not compare wall-clock timing metrics

**File comparison:**
- Size within 10% tolerance (stochastic outputs may vary)
- Structure match (same columns, same row count for CSV)
- Content: spot-check first/last 5 rows

### Step 4: Verdict

| Verdict | Criteria |
|---------|---------|
| `REPRODUCIBLE` | All metrics within tolerance; all output files match |
| `PARTIALLY_REPRODUCIBLE` | Some metrics match, some don't; or files differ in non-critical ways |
| `NOT_REPRODUCIBLE` | Significant differences in primary metrics |
| `CANNOT_VERIFY` | Re-run or comparison could not be completed meaningfully |

## Tolerance Defaults

Use `epsilon = 1e-12` to avoid division-by-zero when a baseline metric is `0`.

| Comparison | Deterministic | Stochastic | Environment-sensitive |
|-----------|--------------|------------|-----------------------|
| Numeric metrics | Exact (0 diff) | < 5% relative, symmetric denominator | < 10% relative, symmetric denominator |
| Output file size | Exact | < 10% | < 20% |
| Output file content | Byte-for-byte | Structure + spot check | Structure + spot check |
| Timing metrics | Not compared (always varies) | Not compared | Not compared |

## Edge Cases

- **Missing original results**: Cannot compare → report "Reproducibility: CANNOT_VERIFY — original results not provided"
- **Environment changed**: Warn "environment may differ from original run — results may not match even if code is correct"
- **Original metric is zero**: Use the symmetric denominator rule above; if both values are zero, treat the metric as a match
- **Partial output**: If original has 5 output files but re-run produces 4 → `PARTIALLY_REPRODUCIBLE` + flag missing file
