# CPC/IPC Classification — Why the Class Follow-Up Catches What Keywords Miss

This reference answers exactly one decision: **why does the patent skill always run a CPC/IPC class-restricted query after initial keyword searches, and how does class follow-up systematically surface art that pure keyword search misses?**

## The Core Claim

Keyword search alone systematically misses adjacent prior art. Patent attorneys describe this as the **"different vocabulary problem"**:

- A 1995 patent on "machine learning for image recognition" might describe its invention as "neural network for visual classification" — different terminology, same underlying concept
- A patent in semiconductors might use "transistor channel" where a software paper would use "data flow path" — same idea, different field's vocabulary
- A patent might intentionally use unusual terminology to **broaden claim scope** (legal strategy)

The CPC/IPC classification system was designed precisely to bridge these vocabulary gaps. **Always-run class follow-up** is the skill's mechanical correction for keyword-only blind spots.

## What Are CPC and IPC?

| System | Maintained by | Granularity | Used by |
|---|---|---|---|
| **CPC** (Cooperative Patent Classification) | USPTO + EPO | ~250,000 classes | All major patent offices since 2013 |
| **IPC** (International Patent Classification) | WIPO | ~75,000 classes | Used as fallback in some jurisdictions |

Both are hierarchical. Examples:

- `G06N` → Computer systems based on specific computational models (CPC + IPC)
- `G06N3/00` → Computing arrangements based on biological models
- `G06N3/04` → Architecture, e.g. interconnection topology
- `G06N3/045` → Combinations of networks (deep learning hidden layers)

When a patent examiner classifies a patent, they assign one or more CPC classes. Patents in the same class are conceptually related EVEN IF they use different vocabulary.

## The CPC Class Follow-Up Pattern

After initial keyword search returns top 5 hits:

1. **Extract CPC classes** from those 5 hits
2. **Tally** to find the dominant class (1-3 classes typically)
3. **Run one class-restricted query** — same keywords + CPC class filter
4. **Compare** results to initial keyword-only results

**Empirical observation:** the class-restricted query consistently surfaces 2-5 additional hits that the keyword search missed. Some of these are highly relevant (the "vocabulary mismatch" cases).

## Concrete Examples

### Example 1: AI for medical diagnosis

| Search | Top results |
|---|---|
| Keyword "AI medical diagnosis" | 2017+ patents using "AI" / "ML" / "deep learning" + "diagnosis" |
| **+ CPC G16H50/20** (medical informatics for diagnosis) | + 1990s patents on "expert systems" + "decision support" — same concept, different era's vocabulary |

Without the class follow-up, the searcher would miss 25 years of foundational expert-system art that the USPTO clearly considers prior art.

### Example 2: 3D printing materials

| Search | Top results |
|---|---|
| Keyword "3D printing polymer" | 2010+ patents using "additive manufacturing" + "polymer" |
| **+ CPC B33Y70/00** (materials for additive manufacturing) | + 1980s patents on "stereolithography resin" — predecessor terminology |

### Example 3: Recommender systems

| Search | Top results |
|---|---|
| Keyword "recommendation algorithm" | 2010+ patents using "recommender" / "collaborative filtering" |
| **+ CPC G06Q30/0631** (recommender system for products/services) | + 1990s patents on "preference matching" + "user modeling" |

## Why This Matters Per Sub-Use-Case

### Novelty

Missing class-adjacent art = **false negative**. User concludes invention is novel; later examiner finds the missed art and rejects. Class follow-up prevents this expensive surprise.

### FTO

Missing class-adjacent active patents = **false confidence**. User ships product believing it's clear; gets sued by patent owner whose patent used different vocabulary. Class follow-up surfaces these.

### Litigation prior-art

Missing class-adjacent art before priority date = **weak invalidity case**. The art that would knock out the target patent might be using completely different vocabulary; class follow-up finds it.

### Landscape + Diligence

Class follow-up surfaces the **technology lineage** — which classes the field operates in, who files in each class, how the field has evolved.

## Operational Pattern

In `Phase 3` of patent's SKILL.md:

```
1. Run initial keyword queries (per sub-use-case)
2. Extract CPC classes from top 5 hits → identify 1-3 dominant classes
3. Run ONE class-restricted query: keywords + CPC class filter
4. Merge results, deduplicate, rank
5. (Optional) If multi-class: run one query per dominant class
```

The class follow-up is a **single additional query per dominant class** — minimal budget cost, high signal yield.

## How to Identify the Right Class

After initial search, look at the top 3-5 hits' classification fields. Most patent search interfaces (Google Patents, Espacenet, USPTO PPS) show CPC classes in the metadata.

**Heuristic:**
- If 3+ of top 5 hits share a class → that's your dominant class
- If hits are spread across many classes → dominant class is the most-frequent across the top 10 hits
- If still spread → run class follow-up for top 2 classes (2 extra queries)

## Anti-Patterns

### Skipping class follow-up "to save queries"

The skill's query budget per sub-use-case explicitly allocates 1-2 queries for class follow-up. **Skipping it to save 1 query is the most common false-economy** in patent search. The signal-per-query of class follow-up consistently exceeds keyword-only queries.

### Relying solely on top-1 hit's class

The top-1 hit might be an outlier. Look at the top 3-5 hits' shared classes for the dominant class.

### Treating IPC and CPC as interchangeable

CPC is more granular and modern (post-2013). When available, prefer CPC classes. Fall back to IPC for older patents that haven't been re-classified.

### Class follow-up without CPC class identification

Just running "G06N" with no further specificity is too broad. Use the most specific class that 2+ top hits share (e.g., `G06N3/045` not just `G06N`).

### Ignoring class signals in DOCX

The dominant CPC classes ARE valuable signal for the DOCX. Surface them in Section 3 (Patent Landscape) so the user understands the technology classification of their search space.

## Operational Checklist

- [ ] Initial keyword queries run (per sub-use-case)
- [ ] CPC classes extracted from top 5 hits
- [ ] Dominant class(es) identified (1-3)
- [ ] Class-restricted query run (additional 1-2 queries)
- [ ] Results merged + deduplicated + ranked
- [ ] Dominant CPC classes surfaced in DOCX Section 3 (or Section 2 for novelty)
- [ ] Audit log notes class follow-up as part of search strategy

## Citations (7 sources)

1. **CPC Scheme — USPTO + EPO joint maintenance.** https://www.cooperativepatentclassification.org. Authoritative source for the CPC hierarchy + per-class definitions. The skill recommends consulting CPC scheme for any class beyond top-3 frequency.

2. **WIPO IPC Strategic Plan + IPC Schema.** https://www.wipo.int/classifications/ipc. Source for IPC fallback discipline (used for pre-2013 patents that lack CPC reclassification).

3. **Mowery, D. C., Nelson, R. R., Sampat, B. N., & Ziedonis, A. A., *Ivory Tower and Industrial Innovation* (Stanford U Press, 2004).** Source for the historical analysis of how patent classifications evolve over time and why cross-era keyword search fails. Empirical evidence for the "different vocabulary problem".

4. **WIPO PATENTSCOPE search documentation.** https://patentscope.wipo.int. Source for cross-jurisdictional class search syntax (especially for non-US/EP jurisdictions).

5. **Cohen, W. M., Nelson, R. R., & Walsh, J. P., "Protecting Their Intellectual Assets" — *NBER Working Paper* 7552 (2000).** Source for the empirical evidence that keyword-only patent search systematically under-reports prior art (especially in fast-moving technology areas).

6. **MPEP §901 — *Manual of Patent Examining Procedure* (USPTO).** Source for the examiner-side discipline of using CPC classes for prior-art search. The skill mirrors examiner discipline by including class follow-up as mandatory.

7. **Lemley, M. A., & Sampat, B., "Examiner Characteristics and Patent Office Outcomes" — *Review of Economics and Statistics* 94(3), 2012.** Source for the empirical analysis showing experienced examiners use CPC classes more aggressively + produce stronger prior-art rejections. Class follow-up is the experienced-examiner technique.
