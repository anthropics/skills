# NCBI Database Skill

Quick reference guide for querying NCBI databases via E-utilities API.

## Quick Start

### 1. Search for a Gene

Find human BRCA1 gene:
```
Database: gene
Term: BRCA1[Gene Name] AND Homo sapiens[Organism]
```

### 2. Get Gene Summary

```
Database: gene
ID: 672
```

### 3. Fetch DNA Sequence

```
Database: nucleotide
ID: NM_001385642
Format: fasta
```

### 4. Get Taxonomy

```
Database: taxonomy
ID: 9606
```

### 5. Search PubMed

```
Database: pubmed
Term: CRISPR[Title/Abstract] AND 2023[PDAT]
```

## Common Database IDs

| Database | ID Parameter Value |
|----------|-------------------|
| Nucleotide | `nuccore` |
| Protein | `protein` |
| Gene | `gene` |
| Taxonomy | `taxonomy` |
| PubMed | `pubmed` |
| dbSNP | `snp` |
| ClinVar | `clinvar` |
| Assembly | `assembly` |
| Structure (MMDB) | `structure` |
| GEO | `gds` |
| SRA | `sra` |

## Common Return Formats

| Format | retmode | rettype | Use Case |
|--------|---------|---------|----------|
| JSON | `json` | - | Programmatic parsing |
| XML | `xml` | - | Structured data |
| FASTA | `text` | `fasta` | Sequence data |
| GenBank | `text` | `gb` | Full record |
| Summary | `json` | `summary` | Quick overview |
| Abstract | `text` | `abstract` | PubMed abstract |

## Essential Workflows

### Find Gene → Get Sequence

1. **Search gene**: `esearch -db gene -query "GENE_NAME[Gene Name] AND SPECIES[Organism]"`
2. **Get ID**: Extract ID from result
3. **Find sequences**: `elink -dbfrom gene -linkname gene_nucleotide -id GENE_ID`
4. **Fetch**: `efetch -db nuccore -id SEQ_ID -rettype fasta`

### Find Gene → Find Literature

1. **Search gene**: Get Gene ID
2. **Link to PubMed**: `elink -dbfrom gene -linkname gene_pubmed -id GENE_ID`
3. **Fetch abstracts**: `efetch -db pubmed -id PUBMED_IDS -rettype abstract`

## API Endpoint

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/
```

## Examples (Full URLs)

### Search Gene
```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi?db=gene&term=BRCA1[Gene+Name]+AND+Homo+sapiens[Organism]&retmax=5&retmode=json
```

### Gene Summary
```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esummary.fcgi?db=gene&id=672&retmode=json
```

### Fetch Sequence (FASTA)
```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi?db=nucleotide&id=NM_001385642&rettype=fasta&retmode=text
```

### Fetch Sequence (GenBank)
```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi?db=nucleotide&id=NM_001385642&rettype=gb&retmode=text
```

### Taxonomy
```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi?db=taxonomy&id=9606&rettype=xml&retmode=text
```

### PubMed Search
```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi?db=pubmed&term=CRISPR[Title/Abstract]+AND+2023[PDAT]&retmax=20&retmode=json
```

## Field Tags (for searching)

| Tag | Description | Example |
|-----|-------------|---------|
| [Gene Name] | Gene symbol | BRCA1[Gene Name] |
| [Organism] | Species name | Homo sapiens[Organism] |
| [Title] | Paper title | CRISPR[Title] |
| [Title/Abstract] | Title or abstract | cancer[Title/Abstract] |
| [Author] | Author name | Smith[Author] |
| [Journal] | Journal name | Nature[Journal] |
| [PDAT] | Publication date | 2023[PDAT] |
| [DP] | Date of publication | 2022[DP] |
| [All Fields] | Search all fields | mutation[All Fields] |

## Field Operators

| Operator | Description | Example |
|----------|-------------|---------|
| AND | Both terms | BRCA1 AND TP53 |
| OR | Either term | cancer OR tumor |
| NOT | Exclude term | human NOT mouse |
| [Title] | Field search | CRISPR[Title] |
| * | Truncation | bacter* |
| " " | Phrase search | "breast cancer" |

## Search Modifiers

| Modifier | Description | Example |
|----------|-------------|---------|
| [Organism] | Species filter | Homo sapiens[Organism] |
| [filter] | Results filter | latest[filter] |
| [pt] | Publication type | review[pt] |
| [dp] | Date range | 2020:2023[dp] |

## Rate Limits

- **Without API key**: 3 requests/second
- **With API key**: 10 requests/second

Get API key: https://www.ncbi.nlm.nih.gov/account/

## Tips

1. Always include your email: `email=user@example.com`
2. Use JSON for parsing: `retmode=json`
3. For large queries: use `usehistory=y` + `webenv`
4. Check `retmax` for pagination
5. Use `esummary` for quick checks before `efetch`

## Documentation

- Full documentation: https://www.ncbi.nlm.nih.gov/books/NBK25497/
- API Reference: https://www.ncbi.nlm.nih.gov/books/NBK25501/
- EDirect: https://www.ncbi.nlm.nih.gov/books/NBK25500/
