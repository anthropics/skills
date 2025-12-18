---
name: data-pipeline
description: Data pipeline toolkit for fetching, validating, and transforming data from 17 integrated sources including Census, arXiv, GitHub, Wikipedia, and news APIs. Use when (1) collecting data from external APIs, (2) validating datasets, (3) building reproducible pipelines, (4) transforming data formats, or (5) aggregating multi-source data.
license: MIT
---

# Data Pipeline Skill

Toolkit for building data collection and validation pipelines with 17 integrated data sources.

## Helper Scripts Available

- `scripts/fetch.py` - Fetch data from any integrated source
- `scripts/validate.py` - Validate datasets (schema, completeness, quality)
- `scripts/transform.py` - Transform data formats (JSON, CSV, markdown)

**Always run scripts with `--help` first** to see usage.

## Integrated Data Sources

| Source | Command | Data Type |
|--------|---------|-----------|
| arxiv | `--source arxiv` | Academic papers, preprints |
| semantic_scholar | `--source semantic_scholar` | Paper metadata, citations |
| pubmed | `--source pubmed` | Medical/biology research |
| wikipedia | `--source wikipedia` | Encyclopedia articles |
| github | `--source github` | Repositories, users, code |
| news | `--source news` | Current headlines, articles |
| youtube | `--source youtube` | Video search, metadata |
| nasa | `--source nasa` | Space, astronomy data |
| weather | `--source weather` | Forecasts, conditions |
| census | `--source census` | Demographics, ACS data |
| finance | `--source finance` | Stock data, markets |
| openlibrary | `--source openlibrary` | Book catalog |
| wolfram | `--source wolfram` | Computation, knowledge |
| archive | `--source archive` | Internet Archive |
| fec | `--source fec` | Election data |
| judiciary | `--source judiciary` | Legal decisions |
| mal | `--source mal` | Anime database |

## Quick Start

### Fetch Data
```bash
# Search arXiv for papers
python scripts/fetch.py --source arxiv "quantum computing" --max 20

# Get GitHub repositories
python scripts/fetch.py --source github "pytorch" --max 10 --output repos.json

# Fetch Census data
python scripts/fetch.py --source census --query "population" --year 2022

# Search news
python scripts/fetch.py --source news "climate change" --max 50
```

### Validate Data
```bash
# Validate a JSON dataset
python scripts/validate.py data.json

# Check for specific issues
python scripts/validate.py data.csv --check completeness,types,ranges

# Generate validation report
python scripts/validate.py data.json --report validation_report.md
```

### Transform Data
```bash
# JSON to CSV
python scripts/transform.py data.json --to csv --output data.csv

# CSV to JSON with schema
python scripts/transform.py data.csv --to json --schema schema.json

# Merge multiple files
python scripts/transform.py file1.json file2.json --merge --output combined.json
```

## Validation Checks

### Schema Validation
- Field presence and types
- Required vs optional fields
- Value constraints

### Completeness
- Missing value detection
- Null/empty field analysis
- Percentage complete per field

### Quality Checks
- Range violations (min/max)
- Outlier detection (IQR method)
- Cross-field consistency
- Duplicate detection

### Format Validation
- Date format consistency
- Email/URL format
- Numeric precision

## Pipeline Pattern

Build reproducible pipelines with multiple stages:

```bash
# 1. Fetch raw data
python scripts/fetch.py --source arxiv "machine learning" \
  --max 100 --output raw_papers.json

# 2. Validate
python scripts/validate.py raw_papers.json \
  --report validation.md

# 3. Transform for visualization
python scripts/transform.py raw_papers.json \
  --to csv --fields title,authors,year,citations \
  --output papers_clean.csv
```

## Configuration

### Environment Variables
```bash
# API Keys (loaded from ~/.env or ~/API_KEYS.md)
CENSUS_API_KEY=...
GITHUB_TOKEN=...
NEWS_API_KEY=...

# Defaults
DATA_CACHE_DIR=~/.data_cache
DATA_CACHE_TTL=3600  # seconds
```

### Common Options
```bash
--source, -s     Data source to use
--query, -q      Search query
--max, -m        Maximum results
--output, -o     Output file path
--format, -f     Output format (json, csv, markdown)
--cache          Use cached results if available
--no-cache       Force fresh fetch
--verbose, -v    Show detailed progress
```

## Output Formats

### JSON (default)
```json
{
  "source": "arxiv",
  "query": "quantum computing",
  "count": 20,
  "timestamp": "2024-01-15T10:30:00Z",
  "results": [
    {
      "id": "2401.12345",
      "title": "Paper Title",
      "authors": ["Author 1", "Author 2"],
      "abstract": "...",
      "url": "https://arxiv.org/abs/2401.12345",
      "published": "2024-01-10"
    }
  ]
}
```

### CSV
```csv
id,title,authors,published,url
2401.12345,"Paper Title","Author 1; Author 2",2024-01-10,https://arxiv.org/...
```

### Markdown
```markdown
# Search Results: quantum computing
Source: arXiv | Count: 20 | Date: 2024-01-15

## Paper Title
**Authors**: Author 1, Author 2
**Published**: 2024-01-10
[View Paper](https://arxiv.org/abs/2401.12345)

> Abstract excerpt...
```

## Validation Report Format

```markdown
# Data Validation Report

## Summary
- **File**: data.json
- **Records**: 1,250
- **Fields**: 12
- **Completeness**: 94.2%
- **Status**: PASS (with warnings)

## Field Analysis

| Field | Type | Complete | Issues |
|-------|------|----------|--------|
| id | string | 100% | - |
| name | string | 98% | 25 missing |
| value | number | 95% | 12 outliers |

## Issues Detected

### High Priority
- Field `email`: 15 invalid formats

### Medium Priority
- Field `value`: 12 outliers detected (IQR method)

### Low Priority
- Field `notes`: 45% empty (consider making optional)

## Recommendations
1. Add default value for `name` field
2. Review outliers in `value` field
3. Consider removing or marking `notes` as optional
```

## Best Practices

1. **Always validate** after fetching external data
2. **Use caching** for expensive API calls during development
3. **Document sources** in output metadata
4. **Handle rate limits** with `--delay` option
5. **Version your schemas** for reproducibility

## Integration

Works with other skills:
- **datavis**: Fetch data → validate → visualize
- **dream-cascade**: Use as data source for research

## Troubleshooting

**"Source not available"**: Check API key configuration

**"Rate limited"**: Use `--delay 1` to add delay between requests

**"Invalid JSON"**: Use `--validate` flag during fetch to catch errors early

**"Schema mismatch"**: Update schema file or use `--infer-schema` to regenerate
