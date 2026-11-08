---
name: 3dgs-method-compare
description: "Compare 3D Gaussian Splatting variants across 11 dimensions. Built-in knowledge of 760+ methods across 25 categories including Foundation, Compression, Dynamic, SLAM, Geometry, Semantic, Avatar, Autonomous Driving, and more. Supports axis-driven fragment loading for efficient context usage. Use when: comparing 3DGS methods or variants, analyzing trade-offs between Gaussian Splatting approaches, generating comparison tables for 3DGS papers, finding the best 3DGS method for a scenario, 检索3DGS方法对比/3D高斯泼溅方法比较."
license: Apache-2.0
---

# 3DGS Method Comparison Engine

> **Architecture**: Axis-driven static/dynamic router. Do NOT try to apply the comparison logic from memory. Always load fragments from disk as described below.

## Capabilities

- Compare any combination of 3DGS variants across 11 technical dimensions
- Generate publication-quality comparison tables
- Analyze design trade-offs and identify positioning
- Provide recommendation based on specific use cases

## Step 1 — Detect Request Axes

Analyze the user's request to determine axis values:

### Axis: category

| User Intent | category value |
|-------------|---------------|
| Foundation/baseline methods, opacity, compression | core |
| Surface reconstruction, geometry, text-to-3D generation | geometry |
| Language features, semantic, feed-forward inference | semantic |
| SLAM, large-scale scene, urban reconstruction | slam |
| Dynamic scenes, 4DGS, human/avatar, articulated objects | dynamic |
| Cross-domain, autonomous driving, spatial intelligence, editing, systems | application |
| Broad/unspecified comparison across many categories | all |

### Axis: depth

| User Intent | depth value |
|-------------|-------------|
| Quick lookup, single method info | quick |
| Standard comparison (2-5 methods, focused analysis) | standard |
| Comprehensive survey, full-category scan | comprehensive |

If the user does not specify, defaults are: category=all, depth=standard.

## Step 2 — Load Required Fragments

### Always Load (every invocation)
Read these files from static/:
- static/core-stance.md — Role, capabilities, comparison dimensions, rendering comparison table, guardrails

### On-Demand Load (by detected category)

| category | Fragment to Load |
|----------|-----------------|
| core | static/methods-core.md |
| geometry | static/methods-geometry.md |
| semantic | static/methods-semantic.md |
| slam | static/methods-slam.md |
| dynamic | static/methods-dynamic.md |
| application | static/methods-application.md |
| all | ALL method fragments (methods-core.md through methods-application.md) |

### Reference Load (when producing structured output)
- static/output-rules.md — Output format template and comparison rules

**Optimization**: For depth=quick, load only the relevant category fragment + core-stance. For depth=comprehensive, load all fragments plus output-rules.

## Step 3 — Execute Comparison

After loading the required fragments:

1. Apply the comparison dimensions from core-stance.md
2. Use method data from the loaded category fragment(s)
3. Follow output format from output-rules.md if producing tables/reports
4. Observe all guardrails (no fabrication, flag uncertainty, load from disk not memory)

## Comparison Dimensions (11 Axes)

When comparing methods, analyze across these 11 dimensions:

1. **Primitive Representation** — Shape (3D Gaussian / 2D disk / 1D splat / hybrid / SVGS / Spline / Triangle / Token-cluster), Anisotropy, Parameterization
2. **Opacity / Alpha Mechanism** — Range ([0,1] / [-1,1] / unbounded / sigmoid / tanh), Signed support, Negative mechanism, Representational Abstraction (RAF)
3. **Color Representation** — SH order, Color space (RGB / HDR / Feature / Albedo-decomposed), Negative color support
4. **Rendering Formulation** — Rasterization (Tile-based / Forward / Deferred), Blending direction, Anti-aliasing (EWA / Mip-aware / None)
5. **Frequency & Geometry Modeling** — HF boundary handling, Surface quality, Geometric constraints
6. **Density Control** — Strategy (Clone+Split+Prune / Progressive / Anchor-based / Variational), Adaptivity, Compression
7. **Training Strategy** — Resolution schedule, Iterations, Regularization, Acceleration methods
8. **Performance Characteristics** — FPS tier, VRAM, Model size, Scalability
9. **Applicable Scenarios** — NVS / Surface reconstruction / 3D editing / Dynamic / Large-scale / Autonomous driving
10. **Code & Reproducibility** — Implementation availability, Framework, Dependencies
11. **Spatial Intelligence & World Model** — 3DGS-as-state / dynamics-primitive / differentiable-simulation-engine

### Rendering Formulation Comparison

| Method | Primitive | Compositing | Key Feature |
|--------|-----------|-------------|-------------|
| 3DGS | 3D Anisotropic Gaussian | alpha-compositing (front-to-back) | Tile-based rasterization |
| Softmax-GS | 3D Anisotropic Gaussian | Softmax competition | Replaces alpha-compositing with learnable softmax |
| Mip-Splatting | 3D Anisotropic Gaussian + Mip | alpha-compositing | 3D smoothing + 2D Mip filter |
| 3DGEER | 3D Anisotropic Gaussian | Exact ray-Gaussian integral | Replaces splatting with exact rendering |
| SNS | Azzalini Skew-Normal Distribution | alpha-compositing | Learnable skewness for asymmetric boundaries |
| DP-GES | Surfel (sort-free) | Depth Peeling transparency | Eliminates sorting via depth peeling |
| TriSplat | Triangle primitive | Triangle rasterization | Triangle primitives replacing Gaussians |

## Key Method Categories (Summary)

### Foundation Methods
3DGS (SIGGRAPH'23), Mip-Splatting (CVPR'24), 2DGS (SIGGRAPH'24), Scaffold-GS (ICCV'23), Softmax-GS (CVPR'26), LeGS, CAdam (SIGGRAPH'26)

### Compression Methods
Compact-3DGS (10-15x), LightGS (15-20x), MobileGS (50-100x), HAC (~100x), NanoGS (training-free), GETA-3DGS (5x, end-to-end pruning+quantization), MGS (Matryoshka continuous LoD), Prune Wisely (90% reduction via DoG), ProGS (45x, octree progressive)

### Geometry / Surface Methods
SuGaR (CVPR'24), PGSR (TVCG'24, SOTA), 2D-SuGaR (DTU SOTA), 3DSS (differentiable surface splatting), SVGS (Blender SOTA), AmbiSuR (ICML'26), TriSplat (triangle primitives)

### SLAM Methods
Gaussian Splatting SLAM (CVPR'24), WildGS-SLAM (CVPR'25), S3PO-GS (ICCV'25), E2EGS (CVPR'26, event camera), MAGS-SLAM (multi-agent), Real-Time LiDAR GS-SLAM

### Dynamic / 4DGS Methods
Multi-solver sub-dimension: Unified Query (D4RT, 200+ FPS) vs Separate Deformation Fields

### Semantic / Feed-Forward Methods
LangSplat (CVPR'24), Feature 3DGS (CVPR'24), Semantic Foam (CVPR'26), GS-LRM (ECCV'24), AnySplat (SIGGRAPH'25), SplatWeaver (cardinality expert routing), ArtSplat (articulated feed-forward)

### Human / Avatar Methods
HumanSplatHMR, EmoTaG (CVPR'26), HairGPT (SIGGRAPH'26), D-Rex (decoupled relighting)

### World Models & Spatial Intelligence
GWM (dynamics primitive), FlashWorld (real-time interactive 3D), GS-World (differentiable sim engine), GSMem (spatial memory), ESI-Bench (embodied spatial intelligence benchmark)

## Output Format

```
## [Method A] vs [Method B] vs [Method C]

### Overview Table
| Dimension | Method A | Method B | Method C |
|-----------|----------|----------|----------|
| Primitive | ... | ... | ... |
| Opacity | ... | ... | ... |
| Rendering | ... | ... | ... |

### Detailed Analysis
#### Primitive Representation
[Paragraph comparing the fundamental representational differences]

#### Design Trade-offs
[Analysis of what each method gains and sacrifices]

#### Recommendation
- For novel view synthesis: [Best choice] because ...
- For surface reconstruction: [Best choice] because ...
- For real-time rendering: [Best choice] because ...
```

## Rules

1. **Be technically precise**: Never oversimplify differences. If two methods differ in their opacity parameterization, explain exactly how.
2. **Quote metrics when available**: Use actual numbers from papers, not estimates.
3. **Avoid bias**: Present each method's strengths and weaknesses fairly.
4. **Context matters**: A method that's worse on PSNR might be better for real-time. Always mention the use case.
5. **Flag uncertainty**: If you don't have reliable data for a comparison dimension, say so explicitly.

## Cross-Skill Routing

- **Paper reading/analysis** → 3dgs-paper-reader
- **Code review/bug detection** → 3dgs-code-reviewer
- **Experiment design** → 3dgs-experiment-planner
- **Engineering deployment** → 3dgs-engineering-guide
- **Visualization/radar charts** → 3dgs-visualizer
- **CAD/Mesh integration** → cad-mesh-3dgs
- **Spatial intelligence/agent** → 3dgs-spatial-agent

## Guardrails

- **Do NOT apply comparison logic from memory.** Always load method data from the static/ fragments. The methods database is updated frequently; stale memory may produce outdated or fabricated comparisons.
- **Do NOT invent metrics, venues, or method features.** If a method is not found in the loaded fragments, say so explicitly.
- **Flag uncertainty.** If you don't have reliable data for a comparison dimension, say so explicitly rather than guessing.