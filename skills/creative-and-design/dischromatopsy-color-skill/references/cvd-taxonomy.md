# CVD Taxonomy — Color Vision Deficiency Science Reference
<!-- dischromatopsy-color-skill v1.0.0 | references/cvd-taxonomy.md -->

## 1. Cone Cell Biology

The human retina contains three types of cone photoreceptors:

| Cone type | Peak sensitivity | Primary perception |
|-----------|:---:|---|
| L cones (long) | ~560–570 nm | Red-yellow range |
| M cones (medium) | ~530–540 nm | Green-yellow range |
| S cones (short) | ~420–440 nm | Blue-violet range |

Normal trichromacy = all three cone types functional.
Color vision deficiency = one or more cone types absent, reduced, or spectrally shifted.

---

## 2. Classification

### 2.1 Dichromacy — cone type absent

| Name | Cone absent | Prevalence (male) | Prevalence (female) |
|------|------------|:---:|:---:|
| Protanopia | L (red) | ~1.0% | ~0.01% |
| Deuteranopia | M (green) | ~1.1% | ~0.01% |
| Tritanopia | S (blue) | ~0.001–0.003% | ~0.001–0.003% |
| Achromatopsia | All cones | ~0.003% | ~0.003% |

### 2.2 Anomalous Trichromacy — cone type defective/shifted

| Name | Cone affected | Effect |
|------|--------------|--------|
| Protanomaly | L cones shifted | Red appears faded, greenish |
| Deuteranomaly | M cones shifted | Green appears reddish — most common CVD overall (~5% of males) |
| Tritanomaly | S cones shifted | Blue/yellow confusion, less severe than tritanopia |

### 2.3 Rare compound CVD

Documented cases exist where individuals present with deficiencies in BOTH
the red-green axis (protan/deutan) AND the blue-yellow axis (tritan).
Mechanism: can be genetic (rare combination of mutations) or acquired
(optic nerve damage, retinal disease, diabetes, certain medications).

**Acquired tritanopia is more common than congenital.** Causes include:
- Aging (S cone sensitivity decline after ~40)
- Glaucoma
- Optic neuritis
- Retinal detachment
- Hydroxychloroquine toxicity
- Vigabatrin toxicity

This means a user presenting with both protan/deutan AND tritan issues
is plausible, especially in older populations or those on certain medications.

---

## 3. Perceptual Consequences by Type

### Protanopia / Protanomaly
- Red appears as very dark / near black (protanopia) or brownish/olive (protanomaly)
- Cannot distinguish red from green, or red from black
- Traffic lights: green/amber visible, red appears black or very dark
- Warm colors (red, orange, yellow) shift toward brown/olive/gray
- Blues and cyans appear relatively normal

### Deuteranopia / Deuteranomaly
- Most common CVD — affects ~5% of males
- Green shifts toward red/brown
- Cannot distinguish green from red, or green from orange
- Blues and yellows visible
- Confusion matrix: red=green=brown=olive (all cluster)

### Tritanopia / Tritanomaly
- Blue appears greenish or gray
- Yellow appears pink, pale, or gray
- Purple/violet appears red
- Cyan appears white or gray
- Blue/green indistinguishable
- Red/green perception is NORMAL (unlike protan/deutan)

### Achromatopsia
- No hue perception at all
- Only luminance contrast is available
- Also: photophobia, reduced visual acuity, nystagmus
- Design for this = design for pure grayscale luminance

---

## 4. The Ishihara Test and Its Limits

The Ishihara test (dot plates) detects red-green CVD (protan/deutan) reliably.
It does NOT detect tritanopia. It does NOT grade severity accurately.

Tests for blue-yellow CVD:
- Hardy-Rand-Rittler (HRR) plates — detects both axes
- Farnsworth-Munsell 100 Hue Test — detects and grades all types
- Cambridge Color Test — clinical research standard
- Anomaloscope — gold standard for protan/deutan grading

A user who says "I struggle with Ishihara" almost certainly has protan or deutan CVD.
A user who says "I struggle with Ishihara AND something else" may have compound CVD.
Design for worst-case regardless — it costs nothing extra.

---

## 5. Prevalence Summary

- ~8% of males, ~0.5% of females have some form of CVD
- 300+ million people worldwide
- Red-green (protan+deutan combined) accounts for ~99% of all CVD cases
- Tritanopia is rare (~1 in 30,000) but acquired tritan defects are more common
- Achromatopsia: ~1 in 33,000

**Design consequence:** designing for all CVD types simultaneously protects
the entire CVD population (~300M), not just the most common subtype.

---

## 6. Key Research References

- Brettel, H., Viénot, F., & Mollon, J.D. (1997). Computerized simulation of color
  appearance for dichromats. Journal of the Optical Society of America A.
  → Simulation algorithm, still the best for tritanopia modeling.

- Machado, G.M., Oliveira, M.M., & Fernandes, L.A.F. (2009). A Physiologically-based
  Model for Simulation of Color Vision Deficiency. IEEE Transactions on Visualization
  and Computer Graphics.
  → Best current algorithm for protan/deutan simulation.

- Okabe, M., & Ito, K. (2008). Color Universal Design (CUD): How to make figures and
  presentations that are friendly to colorblind people. JCVIS.
  → Origin of the Okabe-Ito palette — safe across all three CVD types.

- Wong, B. (2011). Points of view: Color blindness. Nature Methods, 8(6), 441.
  → Nature Methods color blind palette (essentially Okabe-Ito).

- W3C. (2023). Web Content Accessibility Guidelines (WCAG) 2.2.
  → Current legal standard. SC 1.4.3 (contrast minimum), SC 1.4.11 (non-text contrast).

- Myndex Research. APCA: Advanced Perceptual Contrast Algorithm.
  → Future direction for WCAG 3.0. Still in beta as of 2026.
  → https://github.com/Myndex/SAPC-APCA
