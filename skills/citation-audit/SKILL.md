---
name: citation-audit
description: >
  Systematic audit of academic manuscript references: authenticity verification,
  bibliographic accuracy, citation appropriateness, and software/data version
  consistency. Triggers on: citation audit, reference check, bibliography
  verification, fabricated/fake/hallucinated reference detection, DOI verification,
  pre-submission check, manuscript review, R/Python package version consistency,
  data source citation, checking if a paper is real, 文献审查, 引用审查, 参考文献检查,
  伪造文献, 投稿前检查, DOI核对, 软件版本核对, 数据源引用.
  Applicable file types: .docx, .tex, .bib, .ris, .enl, .nbib, manuscript files.
---

# Citation Audit / 学术文献审查

Systematic audit of all references in an academic manuscript before submission.
投稿前对学术稿件参考文献进行系统性全面审查。

## Audit Dimensions / 审查维度

| Level | Scope / 范围 | Severity / 严重度 |
| ----- | ------------ | ----------------- |
| **L1** | Authenticity — does the paper exist? Is the DOI correct? / 真实性——论文是否存在？DOI 是否正确？ | 🔴 Fatal |
| **L2** | Bibliographic accuracy — authors, year, volume, pages, journal / 书目信息——作者、年份、卷号、页码、期刊 | 🔴 Critical |
| **L3** | Text–list consistency — every in-text citation has a matching entry and vice versa / 正文与列表一致性 | 🟡 Important |
| **L4** | Citation appropriateness — each citation supports the claim it is attached to / 引用恰当性 | 🟡 Improvement |
| **L5** | Formatting & version consistency — style uniformity, software/data versions match actual usage / 格式与版本一致性 | ⚪ Housekeeping |

## Workflow / 工作流程

### Phase 1: Extract manuscript text / 提取稿件全文

Extract all text with paragraph indices for cross-referencing. See `scripts/extract_docx.py`.

For `.tex` files, parse directly. For `.docx`, use the python-docx library. Separate the **reference list** from the **body text** and index each entry.

### Phase 2: L1 — Authenticity verification / 真实性验证

> [!CAUTION]
> AI-assisted writing frequently introduces "hallucinated" references — DOIs that resolve to unrelated papers, or entirely fabricated entries. This is the most severe error class.
>
> AI 辅助写作极易引入"幻觉文献"。此类错误一旦发表后果严重。

**Method / 方法: CrossRef API + web search dual verification**

1. Run `scripts/crossref_batch_check.py` to batch-query CrossRef API metadata.
2. **Mandatory web-search re-verification** for:
   - Entries where API results mismatch the manuscript
   - Connection errors or timeouts
   - Papers published within the last 1–2 years (CrossRef indexing lag)
   - Any citation that "looks too perfect" but cannot be independently found

**Red flags for fabricated references / 伪造文献特征:**

- DOI resolves to an unrelated paper
- Author + year + journal combination yields zero Google Scholar results
- Claims to cite a "preprint" but provides a formal journal DOI

**Verification chain for suspicious entries / 可疑条目验证链:**

1. Resolve DOI directly → check title and author match
2. Google Scholar: search author + keywords
3. Author's personal page / ORCID publication list
4. Journal website: browse the table of contents for the cited volume/issue

### Phase 3: L2 — Bibliographic accuracy / 书目信息核对

Check every entry against its verified source for:

| Field | Common errors / 常见错误 |
| ----- | ----------------------- |
| Authors | Missing co-authors (especially 4th+), wrong initials (G.H. vs C.H.) / 遗漏合著者、名缩写错误 |
| Year | Early Online vs. official publication date confusion / 在线优先与正式出版日期混淆 |
| Journal | Abbreviated vs. full name inconsistency / 缩写不统一 |
| Volume/Pages | Mismatch with DOI record / 与 DOI 记录不符 |
| DOI | Placeholder not replaced (e.g. `zenodo.XXXXXXX`), points to wrong article / 占位符未替换 |

### Phase 4: L3 — Text–list cross-check / 正文-列表交叉核对

1. Extract all `(Author, Year)` and `(Author et al., Year)` citations from the body text.
2. Match bidirectionally:
   - **In text → not in list** = missing reference (must add) / 缺失引用
   - **In list → not in text** = orphan reference (delete or cite) / 幽灵引用
3. Special attention to data sources, software packages, and datasets that are mentioned in text but absent from the reference list.

### Phase 5: L4 — Citation appropriateness / 引用恰当性

Evaluate each citation:

- Does it directly support the claim it is attached to?
- Is there a more canonical or more recent alternative?
- Excessive self-citation or citation stacking?

### Phase 6: L5 — Formatting & version consistency / 格式与版本一致性

#### Style uniformity / 格式统一

- "et al." usage, punctuation, spacing
- Author name ordering for multi-work citations

#### Software & package version verification / 软件版本核对

> [!IMPORTANT]
> The manuscript MUST report the actual software versions used for the analysis, not the latest CRAN/PyPI versions.

**R environment:**

```r
pkgs <- c('ecospat', 'biomod2', 'terra', 'sf')
for (p in pkgs) cat(sprintf("%-12s %s\n", p, packageVersion(p)))
cat(sprintf("%-12s %s\n", "R", R.version.string))
```

**Python environment:**

```python
import pkg_resources, sys
for p in ['numpy', 'pandas', 'scikit-learn', 'tensorflow']:
    try: print(f"{p:20s} {pkg_resources.get_distribution(p).version}")
    except: print(f"{p:20s} NOT INSTALLED")
print(f"{'Python':20s} {sys.version.split()[0]}")
```

**Other environments** (Julia, MATLAB, etc.): adapt the pattern to query installed package versions.

**Cross-check steps:**

1. Search project scripts for all `library()` / `import` / `using` calls.
2. Query actual installed versions in the runtime environment.
3. Compare with versions stated in the manuscript and reference list.
4. Flag packages mentioned in the manuscript but never called in any script (may indicate a method–code mismatch).

#### Data source & dataset citation / 数据源引用核对

Verify that **every external data source** used in the analysis is properly cited:

| Data type | Examples | What to check |
| --------- | -------- | ------------- |
| Remote sensing | MODIS, Landsat, Sentinel | Product name, version, DOI or data center URL |
| Climate data | WorldClim, CHELSA, ERA5 | Version number, resolution, temporal coverage |
| Biodiversity records | GBIF, iNaturalist, VertNet | Download DOI, access date, query parameters |
| Geospatial layers | Natural Earth, GADM, OpenStreetMap | Version, access date |
| Genomic data | GenBank, SRA, ENA | Accession numbers |
| Statistical databases | World Bank, UN, national bureaus | Dataset name, access date, URL |

Common issues:

- Dataset is used in methods but has no reference entry
- DOI or accession number is a placeholder
- Version mismatch between what was downloaded and what is cited

## Output format / 输出格式

Generate a `citation_audit.md` report structured as:

```markdown
# Citation Audit Report / 参考文献审查报告

## 🔴 Must-fix errors / 必须修正
(Ordered: fabricated > missing > bibliographic)

## 🟡 Recommended improvements / 建议改进
(Appropriateness, formatting)

## ✅ Verified entries / 已验证通过
(Full checklist with per-entry status)
```

## Key lessons / 关键经验

1. **Never trust CrossRef alone** — its "best match" is frequently wrong for books, chapters, datasets, non-English literature, and same-surname authors. Always web-search verify.
   CrossRef 返回的"最佳匹配"经常是错误的，必须用 Web 搜索二次验证。

2. **Year discrepancies need judgment** — "Early Online" vs. print dates can differ by 1–2 years; both are acceptable. Differences > 2 years likely indicate a real error.
   年份差异需判断：Early Online 与正式出版差 1–2 年属正常。

3. **Methods must match code** — if the manuscript claims package X was used but the scripts call package Y, this is a reviewable error. Cross-check Methods section against actual scripts line by line.
   稿件方法描述必须与代码一致，需逐行比对。

4. **Data sources need citations too** — remote sensing products, climate databases, and biodiversity data portals all require proper citation with DOI/version/access date.
   数据源也需要规范引用。

## Anti-patterns

| Don't / 不要 | Do instead / 应该 |
| ------------ | ---------------- |
| Trust CrossRef blindly | CrossRef + web search dual verification |
| Ignore recent publications | Extra scrutiny for papers < 2 years old |
| Assume all DOIs are correct | Resolve every DOI and verify the target |
| Only check the reference list | Also cross-check body citations and code |
| Report everything at once | Triage by severity: fatal → critical → improvement |
| Skip data source citations | Verify every dataset, layer, and product is cited |
