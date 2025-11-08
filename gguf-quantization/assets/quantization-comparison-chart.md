# Quantization Comparison Chart

## Visual Comparison: Quality Across Quantization Levels

### Side-by-Side Quality Progression

```
Original (FP32)              Quantization Levels              File Size
┌──────────────┐
│              │
│  Perfect     │  Q8_K   Q6_K   Q5_K   Q4_K   Q3_K   Q2_K
│  Quality     │   •      •      •      •      •      •
│ (Baseline)   │  99%    98%    97%    95%    75%    50%
│              │
│              │ ┌─────────────────────────────────────┐
│              │ │ Imperceptible ↓ Visible ↓ Severe   │
│              │ │ Quality Loss                        │
└──────────────┘ └─────────────────────────────────────┘

File Size Reduction

FP32:  ████████████████████ 100% (4.5 GB)
Q8_K:  ██████████░░░░░░░░░░  50% (2.25 GB)
Q6_K:  ███████░░░░░░░░░░░░░░  35% (1.6 GB)
Q5_K:  █████░░░░░░░░░░░░░░░░░░░░ 25% (1.1 GB)
Q4_K:  ████░░░░░░░░░░░░░░░░░░░░░░░  21% (0.95 GB)
Q3_K:  ███░░░░░░░░░░░░░░░░░░░░░░░░░░░  15% (0.67 GB)
Q2_K:  ██░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░  12% (0.54 GB)
```

## Feature Comparison Matrix

| Feature | Q2_K | Q3_K | Q4_K | Q5_K | Q6_K | Q8_K |
|---------|------|------|------|------|------|------|
| **Bit Depth** | 2 | 3 | 4 | 5 | 6 | 8 |
| **File Size** | 0.54GB | 0.67GB | 0.95GB | 1.1GB | 1.6GB | 2.25GB |
| **VRAM (img gen)** | 2GB | 2.5GB | 3.5GB | 4.5GB | 5.5GB | 7GB |
| **Speed (img/sec)** | 18 | 14 | 10 | 8 | 6 | 4 |
| **Quality Score** | 50 | 75 | 92 | 97 | 98 | 99 |
| **Artifacts** | Severe | Visible | Minimal | None | None | None |
| **Use Type** | Mobile | Preview | Production | Professional | Research | Validation |

## Hardware Recommendation Map

```
┌─────────────────────────────────────────────────────────────────┐
│                  VRAM vs Quantization Level                     │
├─────────────────────────────────────────────────────────────────┤
│  8 GB VRAM                                                       │
│  ├─ Q3_K: ✓ (tight)                                             │
│  ├─ Q4_K: ✓ (optimal)                                           │
│  ├─ Q5_K: ✗ (exceeds)                                           │
│                                                                   │
│  12 GB VRAM (RTX 3060, RTX 4070)                                │
│  ├─ Q3_K: ✓ (comfortable)                                       │
│  ├─ Q4_K: ✓✓ (ideal)                                            │
│  ├─ Q5_K: ✓ (possible with optimization)                        │
│                                                                   │
│  16 GB VRAM (RTX 4080)                                          │
│  ├─ Q4_K: ✓ (safe)                                              │
│  ├─ Q5_K: ✓✓ (recommended)                                      │
│  ├─ Q6_K: ✓ (possible)                                          │
│                                                                   │
│  24 GB VRAM (RTX 3090, RTX 4090)                                │
│  ├─ Q5_K: ✓ (safe)                                              │
│  ├─ Q6_K: ✓✓ (recommended)                                      │
│  ├─ Q8_K: ✓ (research/validation)                               │
└─────────────────────────────────────────────────────────────────┘
```

## Quality Analysis by Use Case

### Face Generation Quality

```
FP32:  █████████████████████████ 100% Perfect
Q8_K:  ████████████████████████░  99% Imperceptible
Q6_K:  ███████████████████████░░  98% Imperceptible
Q5_K:  ██████████████████████░░░░  97% Imperceptible
Q4_K:  █████████████████████░░░░░░ 95% Slight softness
Q3_K:  ███████████████░░░░░░░░░░░░░ 75% Visible smoothing
Q2_K:  ██████████░░░░░░░░░░░░░░░░░░ 50% Heavy distortion

Recommendation: Q4_K minimum for production
```

### Texture Detail Quality

```
FP32:  █████████████████████████ 100% Sharp details
Q8_K:  ████████████████████████░  99% Perfect
Q6_K:  ███████████████████████░░  98% Nearly perfect
Q5_K:  ██████████████████████░░░░  96% Fine details preserved
Q4_K:  █████████████████████░░░░░░ 92% Minor smoothing
Q3_K:  ███████████████░░░░░░░░░░░░░ 70% Visible smoothing
Q2_K:  ██████████░░░░░░░░░░░░░░░░░░ 40% Severe loss

Recommendation: Q5_K for texture-critical work
```

### Color Accuracy

```
FP32:  █████████████████████████ 100% Perfect
Q8_K:  ████████████████████████░  99% Perfect
Q6_K:  ███████████████████████░░  98% Perfect
Q5_K:  ██████████████████████░░░░  97% Perfect
Q4_K:  █████████████████████░░░░░░ 94% Accurate
Q3_K:  ███████████████░░░░░░░░░░░░░ 80% Minor banding
Q2_K:  ██████████░░░░░░░░░░░░░░░░░░ 55% Severe banding

Recommendation: Q4_K+ for color-critical work
```

## Performance Curves

### Speed vs Quality Tradeoff

```
Quality Score
100 │                  Q8_K─────Q6_K
    │                  /         /
 95 │            Q5_K───        /
    │             /   \        /
 90 │        Q4_K─      \      /
    │         /   \      \    /
 80 │    Q3_K─      \     \  /
    │    /   \       \     \/
 60 │Q2_K     \       \    /
    │          └──────┴──┴─
    └─────────────────────────→ Speed
      Slow ← Speed → Fast
```

### VRAM vs Quality Tradeoff

```
Quality
100 │          Q8_K
    │           /│
 95 │          / Q6_K
    │         /   │ \
 90 │    Q5_K─    │   Q4_K
    │   /    \    │    │
 80 │  /      \   │    │
    │ /        Q3_K    │
 60 │                  Q2_K
    │
    └────────────────────→ VRAM Usage
      Low    Medium    High
```

## Real-World Comparison Examples

### Scenario 1: Budget Gaming Setup (RTX 3060, 12GB)

```
Recommended Path: Q4_K

File Size:      0.95 GB (vs 4.5 GB original) ✓ 80% reduction
VRAM Usage:     3-4 GB for inference
Generation Speed: 10-12 img/sec
Quality:        Excellent (imperceptible loss)
Result:         ✓ Perfect for daily use
```

### Scenario 2: Enthusiast System (RTX 4080, 16GB)

```
Recommended Path: Q5_K

File Size:      1.1 GB (vs 4.5 GB original) ✓ 75% reduction
VRAM Usage:     4-5 GB for inference
Generation Speed: 8-10 img/sec
Quality:        Near-lossless (professional grade)
Result:         ✓ Ideal for content creation
```

### Scenario 3: Professional Workstation (RTX 4090, 24GB)

```
Recommended Path: Q5_K or Q6_K

Option A: Q5_K
- Speed: 8-10 img/sec
- VRAM: 4-5 GB
- Quality: Near-lossless

Option B: Q6_K
- Speed: 6-8 img/sec
- VRAM: 5-6 GB
- Quality: Imperceptibly lossless

Result:         ✓ Either option excellent
                  Choose based on speed priority
```

### Scenario 4: Mobile/Edge (4GB VRAM or CPU)

```
Recommended Path: Q3_K

File Size:      0.67 GB (85% reduction) ✓
VRAM Usage:     2-2.5 GB CPU + GPU
Generation Speed: 2-3 img/sec (mobile)
Quality:        Acceptable for preview
Result:         ✓ Only practical option
                  Production use: No
```

## Artifact Progression Chart

```
Artifact Severity vs Quantization Level

┌─────────────────────────────────────────┐
│ Artifact Examples by Level              │
├─────────────────────────────────────────┤
│
│ Q2_K: SEVERE
│ ├─ Color banding in gradients
│ ├─ Complete detail loss in textures
│ ├─ Face distortion severe
│ └─ Not usable for delivery
│
│ Q3_K: VISIBLE
│ ├─ Color banding noticeable
│ ├─ Detail smoothing apparent
│ ├─ Face softening obvious
│ └─ Preview quality only
│
│ Q4_K: MINIMAL
│ ├─ Slight smoothing in fine details
│ ├─ No color banding visible
│ ├─ Face quality excellent
│ └─ Production ready
│
│ Q5_K: IMPERCEPTIBLE
│ ├─ No visible artifacts
│ ├─ Full detail preservation
│ ├─ Perfect face quality
│ └─ Professional grade
│
│ Q6_K+: NONE
│ ├─ Indistinguishable from original
│ ├─ Complete preservation
│ └─ Validation/research use
│
└─────────────────────────────────────────┘
```

## Decision Tree

```
START: Need to quantize model?
    ↓
    ├─→ Limited VRAM (≤4GB)?
    │   ├─→ Yes → Q2_K/Q3_K (mobile/edge)
    │   └─→ No → Continue
    ├─→ Quality critical?
    │   ├─→ Yes, unlimited VRAM → Q6_K/Q8_K
    │   ├─→ Yes, limited → Q5_K
    │   └─→ No → Continue
    ├─→ Speed critical?
    │   ├─→ Yes (real-time) → Q3_K
    │   ├─→ Yes (interactive) → Q4_K
    │   └─→ No → Continue
    └─→ DEFAULT: Q4_K ← Recommended for 90% of users
        │
        └─→ If quality loss visible:
            └─→ Upgrade to Q5_K
```

## Summary Table: Quick Reference

```
╔═══════════════════════════════════════════════════════════════╗
║           QUICK QUANTIZATION SELECTION GUIDE                  ║
╠═══════════════════════════════════════════════════════════════╣
║ Q2_K  │ Extreme compression, mobile/CPU only                 ║
║ Q3_K  │ Aggressive compression, real-time/preview            ║
║ Q4_K  │ ✓ RECOMMENDED: Balanced, production-ready            ║
║ Q5_K  │ ✓✓ BEST: Professional quality, slightly slower       ║
║ Q6_K  │ Research/archive, unnecessary for most                ║
║ Q8_K  │ Validation only, not practical                       ║
╠═══════════════════════════════════════════════════════════════╣
║ Hardware Pairing:                                             ║
║ - RTX 3060/4060: Q4_K (or Q3_K if tight)                    ║
║ - RTX 4070/4080: Q4_K or Q5_K                               ║
║ - RTX 3090/4090: Q5_K or Q6_K                               ║
║ - Mobile/CPU: Q2_K or Q3_K                                  ║
╚═══════════════════════════════════════════════════════════════╝
```

## Key Insights

1. **Q4_K is the Sweet Spot**
   - 75% size reduction
   - Imperceptible quality loss
   - Excellent speed
   - Works on most consumer hardware
   - Default recommendation

2. **Diminishing Returns After Q5_K**
   - Q6_K is only ~2% better than Q5_K
   - File size increases 45%
   - Speed drops 20%
   - Not worth for diffusion models

3. **Quality Loss Pattern**
   - Q2_K-Q3_K: Visible degradation
   - Q4_K: Expert-only detection
   - Q5_K+: Imperceptible

4. **Hardware Sweet Spots**
   - 12GB: Q4_K
   - 16GB: Q5_K
   - 24GB: Q5_K or Q6_K

5. **Always Test**
   - Benchmark your specific model
   - Generate with same seed/prompt
   - Compare visually and numerically
   - Hardware-specific variations exist
