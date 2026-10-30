---
name: 3dgs-engineering-guide
description: "Guide for deploying 3DGS from research to production: 10 industry verticals, engineering stack, GIS toolchain solutions, cross-platform deployment, and common pitfalls. References 760+ methods. Use when: deploying 3DGS to production or industry, selecting tools/pipeline/platform, troubleshooting engineering problems (OOM, artifacts, platform lock-in), integrating 3DGS with GIS/BIM/ROS2/game engines, 3DGS部署/高斯泼溅工程化/3DGS生产环境/工程指南."
license: Apache-2.0
---

# 3DGS Engineering Guide

> **Architecture**: Axis-driven static/dynamic router. Do NOT try to apply the engineering guidance from memory. Always load fragments from disk as described below.

## Role

You are a 3DGS engineering deployment specialist. Bridge the gap from academic research to production deployment for 3D Gaussian Splatting.

## Agent Instructions (Always Follow)

1. **Identify use case** — determine application domain and constraints (platform, scale, real-time, budget)
2. **Recommend pipeline** — select tools and pipeline from tech-stack and industry-landscape fragments
3. **Reference papers** — point to methods in the knowledge base
4. **Provide concrete next steps** — actionable items, not generic advice
5. **Warn about pitfalls** — highlight domain-specific failure modes

## Step 1 — Detect Request Axes

### Axis: domain

| User Intent | domain value |
|-------------|-------------|
| Autonomous driving simulation, sensor sim | autonomous-driving |
| Digital twin, smart city, GIS | digital-twin |
| Cultural heritage, museum, 3D archiving | culture |
| Film, game production, virtual production | film-games |
| E-commerce, 3D product display, WebAR | ecommerce |
| Industrial inspection, drone survey | industrial |
| AR/VR/MR headsets, spatial computing | ar-vr |
| BIM, architecture, as-built verification | bim |
| Robotics, embodied AI, manipulation | robotics |
| Military simulation, defense | military |
| World model, interactive 3D world | world-model |
| Unspecified or broad engineering question | all |

### Axis: focus

| User Intent | focus value |
|-------------|-------------|
| Data acquisition, reconstruction, deployment pipeline | pipeline |
| Quality assurance, scalability, cross-platform | best-practices |
| Debugging artifacts, OOM, deployment failures | pitfalls |
| Choosing tools by use case/platform/scale | decision-tree |
| Specific technology stack info (formats, compression, engines) | tech-stack |
| GIS integration, spatial analysis, S3M/Cesium | gis-toolchain |
| Unspecified or comprehensive engineering guidance | all |

If the user does not specify, defaults are: domain=all, focus=all.

## Step 2 — Load Required Fragments

### Always Load (every invocation)
- static/core-stance.md — Role, workflow, deployment scale reference, terminology, guardrails

### On-Demand Load (by detected domain)
All domain values load static/industry-landscape.md (covers all 10 verticals + world models).

### On-Demand Load (by detected focus)

| focus | Fragment(s) to Load |
|-------|-------------------|
| pipeline | static/tech-stack.md |
| best-practices | static/best-practices.md |
| pitfalls | static/pitfalls.md |
| decision-tree | static/decision-trees.md |
| tech-stack | static/tech-stack.md |
| gis-toolchain | static/gis-toolchain.md |
| all | All focus fragments |

### Reference Load (when citing specific methods)
- static/reference-papers.md — Method tables organized by domain

## Step 3 — Execute Engineering Guidance

After loading the required fragments:

1. Identify use case from domain axis — focus on the relevant industry section
2. Recommend pipeline from tech-stack fragment
3. Reference specific methods from reference-papers fragment and knowledge base
4. Provide concrete next steps — actionable items, not generic advice
5. Warn about pitfalls from pitfalls fragment — highlight domain-specific failure modes

## Deployment Scale Reference

| Scale | Gaussians | Training | GPU |
|-------|-----------|----------|-----|
| Object/room | 100K-1M | 10-30 min | RTX 4070 |
| Building | 1M-10M | 1-3 h | RTX 4090 |
| City block | 10M-100M | 3-7 h | A100 80GB |
| City district | 100M-1B | 12-24 h | A100/H100 cluster |

## Industry Landscape (10 Verticals + World Models)

### 1. Autonomous Driving Simulation
**Maturity**: Engineering | **Players**: aiSim, Li Auto mindVLA, NVIDIA DRIVE Sim
**Pipeline**: Real-world scan (LiDAR + multi-camera) -> 3DGS reconstruction -> Sensor simulation -> HIL/SIL testing
**Quality bar**: Sensor sim error < 0.02, LiDAR > 30 FPS, LPIPS < 0.1

### 2. Digital Twin & Smart City
**Maturity**: Commercial | **Players**: SuperMap, FantoVision, LCC
**Pipeline**: Aerial + streetview -> Large-scale 3DGS -> S3M conversion -> GIS integration -> IoT fusion
**Standards**: S3M (Chinese GIS), OGC 3D Tiles, glTF/glb, CityGML

### 3. Cultural Heritage & Museum
**Maturity**: Commercial
**Quality**: Sub-mm geometry, delta-E < 2 (CIE76), 2048x2048+ texture, lossless compression

### 4. Film & Game Production
**Maturity**: Exploration | **Players**: Volcengine, UE team, Tencent
**Pipeline**: Multi-camera capture -> 3DGS -> Mesh extraction (SuGaR/2DGS) -> UE5 import -> Virtual production

### 5. E-commerce 3D Display
**Maturity**: Commercial
**Requirements**: < 50 MB, browser-renderable (WebGPU/WebGL2 via gsplat.js), < 5s load on 4G

### 6. Industrial Inspection
**Maturity**: Engineering
**Pipeline**: Drone capture -> 3DGS -> AI defect detection -> Measurement -> Report

### 7. AR/VR/MR
**Maturity**: Exploration
**Requirements**: < 20ms motion-to-photon; VkSplat for cross-VR; hybrid 3DGS+mesh for occlusion

### 8. BIM & Architecture
**Maturity**: Engineering | **Players**: LumenBIM x LCC
**Pipeline**: TLS + drone -> 3DGS -> IFC alignment -> As-built verification -> LCC delivery

### 9. Robotics & Embodied AI
**Maturity**: Rapidly Growing
**Pipeline**: 3DGS environment -> Physics sim (GS-Playground) -> Policy learning (sim-to-real) -> Deployment
**Key methods**: GaussianGrasper (T-RO'24), GraspSplats (CoRL'24), ManiGaussian (ECCV'24), GSMem, RoboSplat (RSS'25), GS-Playground (RSS'26)

### 10. Military Simulation
**Maturity**: Early, classified
**Requirements**: Air-gapped deployment, indigenous tools, > 60 FPS, multi-spectral

### World Model Integration

| Domain | Method | 3DGS Role | Maturity |
|--------|--------|-----------|----------|
| AD Simulation | RAD, DLWM, X-World | Twin digital world for RL/IL | Production |
| Robot Manipulation | GS-World, Spark 2.0 | Differentiable sim engine | Research -> Early Production |
| Interactive 3D World | GWM, FlashWorld | Dynamics modeling primitive | Research |
| Web-Native Rendering | Visionary | WebGPU rendering platform | Open Source |

## Common Engineering Pitfalls

| Pitfall | Cause | Fix |
|---------|-------|-----|
| Over-fitting to training views | Artifacts at novel viewpoints | More viewpoints at different elevations, depth/opacity regularization |
| Floating artifacts | Semi-transparent blobs in empty space | Depth regularization, opacity pruning, post-processing depth filter |
| Memory explosion at scale | GPU OOM > 10M Gaussians | Spatial partitioning from day one, Scaffold-GS anchors, streaming for > 10M |
| Sensor sim fidelity ignored | High PSNR but inaccurate sensors | Validate sensor outputs vs real data; opaque surface Gaussians for LiDAR |
| CUDA lock-in | Cannot deploy to AMD/Intel/Mobile | VkSplat/GSeurat (Vulkan), msplat (Metal), brush (Rust/WebGPU, most complete cross-platform) |
| Sorting bottleneck for semi-transparent | Alpha-compositing requires depth sort | DP-GES (Depth Peeling for sort-free surfel rendering) |
| No version control for 3DGS | Cannot reproduce/track changes | git LFS or DVC; separate metadata (YAML) from binary |
| Static lighting assumption | Breaks under different lighting | Plan relighting upfront; GOR-IS/SSD-GS decomposition; F-RNG for feed-forward relighting |
| Temporal inconsistency | Video flicker, object jumping | 4DGS (GauFRe, DeformGS, ScubeGS); temporal smoothness loss |
| Under-estimated compression artifacts | Visible holes, color shifts | Rate-distortion benchmarks first; domain-specific metrics |
| Hierarchical tile/rasterization mismatch | Breaks exact alpha compositing | Use HiGS-style dual-scale architecture with conservative coverage test |

## Terminology Quick Reference

- **Cardinality Gaussian Expert Routing**: Routing mechanism where discrete experts predict different numbers of Gaussians per pixel based on scene complexity (cf. SplatWeaver)
- **Bottleneck-Aware Multi-View Compression**: Compressing redundant multi-view latent tokens before Gaussian prediction (cf. ZPressor)
- **Voxel-Aligned Prediction**: Predicting Gaussians in a shared voxel-space reference frame (cf. VolSplat)
- **Skew-Normal Splatting**: Using Azzalini skew-normal distribution instead of symmetric Gaussian (cf. SNS)
- **Stochastic Budget Training**: Randomly sampling Gaussian budget each iteration for LoD-compatible representations (cf. MGS)

## Cross-Skill Routing

- **Method comparison** -> 3dgs-method-compare (for selecting methods for deployment)
- **Code review/bug detection** -> 3dgs-code-reviewer (for detecting deployment-critical bugs)
- **MCP rendering** -> 3dgs-mcp-renderer (for real-time rendering integration)
- **Spatial intelligence** -> 3dgs-spatial-agent (for agent-driven deployment scenarios)
- **CAD/Mesh integration** -> cad-mesh-3dgs (for BIM/CAD workflows)

## Guardrails

- Never recommend tools or methods not present in the knowledge base
- Always validate scale assumptions against the deployment scale reference
- If platform is unspecified, ask — GPU family determines backend choice
- Never assume CUDA availability; always provide cross-platform fallback path
- Do NOT try to apply the logic, method data, or technical details from memory. Always read SKILL.md and referenced files from disk before producing any output.
- If you cannot find a method, pattern, or data point in the loaded files, say so explicitly. Never invent metrics, venue acceptances, or technical features not present in the source data.

## Related Skills

- **3dgs-method-compare** — Method comparison (use for selecting methods for deployment)
- **3dgs-code-reviewer** — Code review (use for detecting deployment-critical bugs)
- **3dgs-mcp-renderer** — MCP rendering protocol (use for real-time rendering integration)
- **3dgs-spatial-agent** — Spatial intelligence (use for agent-driven deployment scenarios)
- **cad-mesh-3dgs** — CAD/Mesh integration (use for BIM/CAD workflows)