# Reproduction and Implementation (Step 3-R)

Goal: put **results obtained by actually running** the paper's public code (or its core algorithm) on the slides. "Including the implementation" means reproduction results, not code excerpts. The audience wants to see "this is what happens when you actually run it", not lines of code.

## 1. The ladder — the highest rung the environment allows
| Rung | What | Output | Condition |
|---|---|---|---|
| L1 Full reproduction | Official code, from training through evaluation | Reproduced version of the paper's figures/tables | GPU, simulator and data all available |
| L2 Evaluation reproduction | Inference and evaluation only, with public checkpoints and data | Paper values vs reproduced values table, plots | Checkpoints public; often feasible on CPU |
| L3 Toy implementation | Core algorithm scaled down to a small problem (1-DoF, 2D, a few hundred samples) | A plot that shows the principle (e.g. a curve of FIM active exploration reducing parameter identification error, a curve of LoRA error dropping within a few steps) | Feasible anywhere — under 30 minutes |
| L4 Box | Could not run | `[[Repro n | … ]]` box + run procedure in Reproduction Notes | — |

- Choose the starting rung from the reproduction scope and compute environment given in Step 0. If the user's PC (GPU) is connected, run L1 and L2 there via `device_bash`. The cloud workspace is CPU only, so L2 (light inference) and L3 are what is realistic there.
- If a rung fails (cannot install, over 30 minutes, blocked dependency), **step down one rung**. Record the reason for the failure in one line in Reproduction Notes.
- In bundle mode, the rung may differ per paper. However, the slide template (per-paper b) keeps the "reproduction results" block in the same place.

## 2. Procedure
1. Inspect the repository — what the README says is released (training / inference / sim2real / checkpoints), license, required environment (GPU, IsaacGym, MuJoCo, etc.), data and checkpoint links (HF etc.). Fetch with `git clone --depth 1` (clone often works even when the API and raw URLs are blocked). Keep the fetched code in `reproduction/{paper}/repo/` and run it from scripts outside that directory, passing the path in.
2. Decide the rung — the ladder above. In a bundle, papers can proceed in parallel.
3. Run — record the commands, environment and time taken exactly. Logs go to `reproduction/{paper}/log.txt`.
4. Produce the outputs — plots as `figures/{paper}_repro_{name}.png` (deck style constants, 300 dpi, no caption). Numbers as a three-column table: **reproduced / paper / difference and reason**. For video, `figures/{paper}_repro_{name}.mp4` + `_poster.jpg`.
5. Verify — if a reproduced value differs from the paper's by 10% or more, find the cause (seed, number of evaluation runs, hardware, config differences) and write it in the table's "difference and reason" column. If it cannot be found, write "cause unknown" — do not hide it.

## 3. Toy implementation guidelines (L3)
- Pick **one claim** from the paper (e.g. "active exploration has lower identification error than random exploration", "the Planner is invariant to payload", "after Δa correction the simulated trajectory moves closer to the real one").
- Make the problem as small as possible: 1-DoF mass-spring, 2D point robot, linear model. It must finish within minutes on numpy or torch CPU.
- One plot with 2–3 curves to compare. Mark "toy" in the title and state in the caption that it is "a scaled-down implementation, not the paper's setup" — it must not be mistaken for a reproduction of the paper.
- Leave the script at `reproduction/{paper}/toy_{name}.py` (runnable with no arguments so the user can rerun it).

## 4. Notation on slides
- Per-paper b (bundle) / 5-2 (single): the reproduction plot or the reproduced vs paper table. Caption below in the form `Repro: L2 · 8-core CPU · 12 min · python eval.py --ckpt hf://…`.
- For a toy, the caption starts with `toy implementation:`.
- For L4, a `[[Repro n | what | command, environment, expected time | why]]` box (green dashed).

## 5. Reproduction Notes.md format
| Paper | Rung | Environment | Command summary | Time | Result file | Reproduced vs paper | Notes (failure reason, cause of difference) |
|---|---|---|---|---|---|---|---|
| FADA | L2 | Cloud CPU | `python -m … --ckpt …` | 14 min | figures/FADA_repro_payload.png | 0.87 vs 0.866 | Mean over 5 seeds |

Write each row's command in a form that can be copied and run as is, so the user can rerun it on their own PC.
