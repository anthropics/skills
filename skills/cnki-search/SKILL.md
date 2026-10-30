---
name: cnki-search
description: Use this skill when the user wants to search for academic papers, especially Chinese papers from Wanfang, OpenAlex, or CrossRef. Also use when the user wants to download papers from arXiv, PubMed Central, SSRN, or Unpaywall, or export paper lists to CSV/BibTeX/RIS format. If the user mentions "论文", "文献", "paper search", "literature search", or academic research, use this skill.
---

# Chinese Academic Paper Search & Download

Search and download academic papers from Chinese and international databases.

## Installation

```bash
pip install cnki-search-skill
```

For Wanfang search (requires Selenium):
```bash
pip install selenium webdriver-manager
```

## Quick Start

### Search Papers

```bash
# Search from OpenAlex (recommended, no extra setup)
cnki-search search "knowledge graph" --source openalex --limit 10

# Search from CrossRef (includes Chinese papers)
cnki-search search "知识图谱" --source crossref --limit 10

# Search from Wanfang (requires Selenium)
cnki-search search "知识图谱" --source wanfang --limit 10
```

### Download Papers

```bash
# Download from arXiv
cnki-search download "Attention Is All You Need" --arxiv-id 1706.03762

# Download from PubMed Central
cnki-search download "paper title" --source pmc

# Download from SSRN
cnki-search download "paper title" --source ssrn
```

### Export Papers

```bash
# Export to CSV
cnki-search export "knowledge graph" --format csv --limit 50

# Export to BibTeX
cnki-search export "knowledge graph" --format bibtex --limit 50

# Export to RIS (for EndNote)
cnki-search export "knowledge graph" --format ris --limit 50
```

## Supported Data Sources

### Search Sources

| Source | Status | Description |
|--------|--------|-------------|
| OpenAlex | ✅ Available | Open academic data, mainly English |
| CrossRef | ✅ Available | DOI resolution, includes Chinese papers |
| Wanfang | ✅ Available | Chinese journals (requires Selenium) |

### Download Sources

| Source | Status | Description |
|--------|--------|-------------|
| arXiv | ✅ Available | Preprints, completely free |
| PubMed Central | ✅ Available | Biomedical OA |
| SSRN | ✅ Available | Social science preprints |
| Unpaywall | ✅ Available | Find OA versions via DOI |

## Examples

### Example 1: Search for Chinese papers

```
User: 帮我搜索"知识图谱"相关的论文

AI executes:
cnki-search search "知识图谱" --source crossref --limit 10

Output:
Total: 50600 papers found

1. 课程思政知识图谱的双维比较研究
   Authors: 河山 管, 懿 廖
   Year: 2025

2. 智能时代的红树林知识服务展望: 从植物图谱到知识图谱
   Authors: 志伟 侯, 文龙 荆, 承志 秦
   Year: 2025
```

### Example 2: Download a paper

```
User: 帮我下载"Attention Is All You Need"这篇论文

AI executes:
cnki-search download "Attention Is All You Need" --arxiv-id 1706.03762

Output:
Download successful!
File path: ./downloads/Attention Is All You Need.pdf
File size: 2163.32 KB
```

### Example 3: Export papers to CSV

```
User: 帮我导出"knowledge graph"相关的文献为 CSV 格式

AI executes:
cnki-search export "knowledge graph" --format csv --limit 50

Output:
Export successful!
File path: cnki_export.csv
Exported: 50 papers
```

## Notes

- This tool only searches paper metadata (title, authors, abstract, etc.), it does not bypass paywalls
- Download only supports legally accessible full texts (open access, preprints, etc.)
- Wanfang search requires Selenium: `pip install selenium webdriver-manager`
- For proxy support, add `--proxy http://127.0.0.1:7897`
