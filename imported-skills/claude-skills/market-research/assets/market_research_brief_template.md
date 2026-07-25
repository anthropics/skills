# Market Research Brief — Template

> Fill this before running the tools. Every number in the final brief must carry its method,
> assumptions, and confidence. Size to the decision's tolerance, not to false precision.

## 1. Objective
- Research question:
- **The decision this informs** (and who makes it):
- Precision required (order-of-magnitude / ±20% / ±5%):

## 2. Market sizing
- Approach: [top-down | bottoms-up | both — recommended both]
- Top-down inputs: total market value + source citation; serviceable fraction; reachable share.
- Bottoms-up inputs: total potential customers + source; annual price; serviceable fraction; realistic adoption.
- Triangulation result (from `market_sizer.py`) + divergence:

## 3. Survey plan (if primary data)
- Population (N) + sampling frame:
- Confidence level / overall margin of error / expected proportion:
- Segments to report + per-segment margin of error:
- Recommended n (overall + per-segment floors, from `sample_size_planner.py`):
- Mode (online panel / phone / mixed) + coverage risk:

## 4. Segmentation
- Candidate segments + scores across measurable / substantial / accessible / differentiable / actionable:
- Verdicts (from `segmentation_scorer.py`): TARGET / WATCH / DROP

## 5. Competitive intelligence
- Sources (public, ethically obtained — SCIP code):
- Five Forces summary:

## 6. Assumptions register
- (List every assumption behind the sizing, sampling, and segmentation. Each must trace to a source or be flagged as an unverified planning assumption.)

## 7. Confidence statement
- Overall confidence in the headline numbers (high / moderate / low) and why:
