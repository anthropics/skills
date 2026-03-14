# NCBI E-utilities Detailed Endpoints

Complete reference for all NCBI Entrez E-utilities endpoints.

## E-utilities Overview

| Utility | Purpose | Typical Use |
|---------|---------|-------------|
| `einfo` | Get database metadata | List available fields, links |
| `esearch` | Search and return IDs | Find records matching query |
| `esummary` | Return document summaries | Quick overview of records |
| `efetch` | Retrieve full records | Get detailed data |
| `elink` | Find linked records | Cross-database queries |
| `efilter` | Filter search results | Post-search filtering |
| `espell` | Get spelling suggestions | Spell-check queries |
| `ecitmatch` | Match citations | Citation matching |

---

## 1. einfo - Database Information

### Purpose
Returns metadata about a database, including available fields, link names, and database statistics.

### Endpoint
```
GET https://eutils.ncbi.nlm.nih.gov/entrez/eutils/einfo.fcgi
```

### Parameters

| Parameter | Type | Description |
|-----------|------|-------------|
| db | string | Database name (optional - returns all if omitted) |

### Example

**Request:**
```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/einfo.fcgi?db=gene
```

**Response (XML):**
```xml
<eInfo>
  <DbInfo>
    <DbName>gene</DbName>
    <DbBuild>Build-6.4-240101</DbBuild>
    <DbSize>23245789</DbSize>
    <DbLastUpdate>2024/01/15</DbLastUpdate>
    <FieldList>
      <Field>
        <Name>GBSeq_define</Name>
        <FullName>Full text definition</FullName>
        <Description>Textual definition of a sequence</Description>
        <IsTerm>Y</IsTerm>
        <IsNucleotide>Y</IsNucleotide>
      </Field>
      ...
    </FieldList>
    <LinkList>
      <Link>
        <Name>gene_pubmed</Name>
        <Description>PubMed citations linked to Gene</Description>
      </Link>
      ...
    </LinkList>
  </DbInfo>
</eInfo>
```

---

## 2. esearch - Search Database

### Purpose
Searches a database and returns a list of UIDs (Unique Identifiers) matching the query.

### Endpoint
```
GET https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi
POST https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi
```

### Parameters

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| db | string | Yes | Database to search |
| term | string | Yes | Search term |
| field | string | No | Specific field to search |
| usehistory | string | No | Store results server-side (y/n) |
| rettype | string | No | Return format (uilist/count) |
| retmode | string | No | Return mode (json/xml/text) |
| retmax | int | No | Maximum results (default 20) |
| retstart | int | No | Start position |
| sort | string | No | Sort order |
| datetype | string | No | Date field type (mdat/pdat/edat) |
| mindate | string | No | Start date (YYYY/MM/DD) |
| maxdate | string | No | End date |
| idtype | string | No | ID type (acc/uid) |
| termtoreport | string | No | Term to report in response |

### Field Tags

Common field tags for literature databases:

| Tag | Database | Description |
|-----|----------|-------------|
| [Mesh Heading] | pubmed | MeSH terms |
| [Substance] | pubmed | Substance names |
| [All Fields] | all | Search all fields |
| [Title] | pubmed | Article title |
| [Abstract] | pubmed | Abstract text |
| [Author] | pubmed | Author name |
| [Journal] | pubmed | Journal name |
| [Affiliation] | pubmed | Author affiliation |

### Example - Complex Search

**Request:**
```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi?db=pubmed&term=CRISPR[Title]+AND+(review[pt]+OR+systematic[sb])+AND+2020:2023[dp]+AND+English[lang]&retmax=50&retmode=json&sort=pub+date
```

**Response (JSON):**
```json
{
  "esearchresult": {
    "count": "2847",
    "retmax": "50",
    "retstart": "0",
    "querykey": "1",
    "webenv": "MCID_64a1b2c3d4e5f",
    "idlist": [
      "37123456",
      "37123455",
      ...
    ],
    "translationSet": {
      "from": "\"systematic review\"[Publication Type]",
      "to": "systematic[sb]"
    },
    "querytranslation": "(CRISPR[Title]) AND ((review[pt]) OR (systematic[sb])) AND (2020:2023[dp]) AND (English[lang])"
  }
}
```

---

## 3. esummary - Document Summary

### Purpose
Returns document summaries (metadata) for a list of UIDs.

### Endpoint
```
GET https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esummary.fcgi
POST https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esummary.fcgi
```

### Parameters

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| db | string | Yes | Database name |
| id | string | Yes | Comma-separated UIDs |
| retmode | string | No | Return mode (json/xml) |
| version | string | No | Version (2.0/1.0) |

### Example - Gene Summary

**Request:**
```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esummary.fcgi?db=gene&id=672,7157&retmode=json
```

**Response (JSON):**
```json
{
  "result": {
    "uids": ["672", "7157"],
    "672": {
      "uid": "672",
      "name": "BRCA1",
      "description": "BRCA1 DNA repair associated",
      "status": "Official Symbol",
      "currentid": "672",
      "chromosome": "17",
      "maplocation": "17q21.31",
      "genomicinfo": [
        {
          "chrver": "GRCh38.p14",
          "chraccver": "NC_000017.11",
          "exons": "24",
          "start": "43044295",
          "stop": "43270913",
          "strand": "-",
          "assemblyaccession": "GCF_000001405.40",
          "assemblyname": "GRCh38.p14"
        }
      ],
      "summary": "The BRCA1 gene encodes a nuclear phosphoprotein..."
    },
    "7157": {
      "uid": "7157",
      "name": "TP53",
      "description": "tumor protein p53",
      ...
    }
  }
}
```

### Example - PubMed Summary

**Request:**
```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esummary.fcgi?db=pubmed&id=37123456,37123455&retmode=json
```

---

## 4. efetch - Retrieve Records

### Purpose
Retrieves full records in specified format.

### Endpoint
```
GET https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi
POST https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi
```

### Parameters

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| db | string | Yes | Database name |
| id | string | Yes | Comma-separated UIDs |
| rettype | string | No | Record type |
| retmode | string | No | Return mode |
| strand | int | No | Strand (1=forward, 2=reverse) |
| seqstart | int | No | Start position |
| seqstop | int | No | Stop position |
| seqtotal | int | No | Total bases |
| complexid | int | No | Complex sequence retrieval |
| style | string | No | Citation style |
| moltype | string | No | Molecule type (n/r/a/aa) |

### rettype Options by Database

#### nucleotide (nuccore)

| rettype | Description |
|---------|-------------|
| gb | GenBank flatfile |
| fasta | FASTA sequence |
| gff | GFF3 annotation |
| xml | XML format |
| summary | Brief summary |
| abstract | Abstract only |
| native | Native format |
| html | HTML view |
| docsum | Document summary |
| acc | Accession only |

#### protein

| rettype | Description |
|---------|-------------|
| fasta | FASTA sequence |
| gb | GenPept flatfile |
| gff | GFF3 |
| xml | XML |
| summary | Brief summary |
| native | Native format |

#### gene

| rettype | Description |
|---------|-------------|
| xml | XML format |
| summary | Brief summary |
| native | Native format |
| fasta | FASTA (from linked sequences) |

#### pubmed

| rettype | Description |
|---------|-------------|
| abstract | Abstract only |
| medline | MEDLINE format |
| xml | PubmedArticle XML |
| full | Full citation |
| medline | MEDLINE format |

#### taxonomy

| rettype | Description |
|---------|-------------|
| xml | Taxonomy XML |
| summary | Brief summary |
| native | Native format |

### Example - Fetch Gene Record (XML)

**Request:**
```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi?db=gene&id=672&rettype=xml&retmode=text
```

### Example - Fetch Sequence Region

**Request:**
```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi?db=nucleotide&id=NM_001385642&rettype=fasta&retmode=text&seqstart=1&seqstop=500
```

---

## 5. elink - Find Linked Records

### Purpose
Finds records linked to input records in the same or different database.

### Endpoint
```
GET https://eutils.ncbi.nlm.nih.gov/entrez/eutils/elink.fcgi
POST https://eutils.ncbi.nlm.nih.gov/entrez/eutils/elink.fcgi
```

### Parameters

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| dbfrom | string | Yes | Source database |
| id | string | Yes | Source UIDs |
| db | string | No | Target database |
| linkname | string | No | Specific link set |
| linktype | string | No | Link type (neighbor/parent/children) |
| term | string | No | Filter linked results |
| retmode | string | No | Return mode |

### Common Link Names

#### gene → other databases

| Link Name | Target DB | Description |
|-----------|-----------|-------------|
| gene_pubmed | pubmed | PubMed citations |
| gene_nucleotide | nucleotide | Nucleotide sequences |
| gene_protein | protein | Protein sequences |
| gene_genome | genome | Genome records |
| gene_structure | structure | 3D structures |
| gene_genomic | nuccore | Genomic sequences |
| gene_genomic_gene | gene | Genomic gene records |

#### nucleotide → other databases

| Link Name | Target DB | Description |
|-----------|-----------|-------------|
| nuccore_protein | protein | Protein translations |
| nuccore_pubmed | pubmed | PubMed citations |
| nuccore_genome | genome | Genome assemblies |
| nuccore_structure | structure | 3D structures |

#### pubmed → other databases

| Link Name | Target DB | Description |
|-----------|-----------|-------------|
| pubmed_pubmed | pubmed | Related articles |
| pubmed_abstract | pubmed | Similar abstracts |
| pubmed_mesh | mesh | MeSH headings |
| pubmed_nlmdb | nlmcatalog | NLM catalog |

### Example - Gene to PubMed

**Request:**
```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/elink.fcgi?dbfrom=gene&linkname=gene_pubmed&id=672&retmode=json
```

**Response:**
```json
{
  "linkset": [
    {
      "dbfrom": "gene",
      "id": "672",
      "linksetdbs": [
        {
          "dbname": "pubmed",
          "links": ["12601234", "12601233", ...]
        }
      ]
    }
  ]
}
```

### Example - Find Nucleotide Sequences for Gene

**Request:**
```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/elink.fcgi?dbfrom=gene&linkname=gene_nucleotide&id=672&retmode=json
```

---

## 6. espell - Spelling Suggestions

### Purpose
Returns spelling suggestions for a search term.

### Endpoint
```
GET https://eutils.ncbi.nlm.nih.gov/entrez/eutils/espell.fcgi
```

### Parameters

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| db | string | Yes | Database name |
| term | string | Yes | Search term |

### Example

**Request:**
```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/espell.fcgi?db=pubmed&term=brca+genetics
```

**Response:**
```xml
<eSpell>
  <CorrectedQuery>brca genetics</CorrectedQuery>
  <Suggestions>
    <Suggestion>BRCA1</Suggestion>
    <Suggestion>BRCA2</Suggestion>
  </Suggestions>
</eSpell>
```

---

## 7. ecitmatch - Citation Matching

### Purpose
Matches citations in text against PubMed.

### Endpoint
```
POST https://eutils.ncbi.nlm.nih.gov/entrez/eutils/ecitmatch.fcgi
```

### Parameters

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| db | string | Yes | Database (pubmed) |
| rettype | string | No | Return type (abstract) |
| retmode | string | No | Return mode (text) |
| bdata | string | Yes | Citation data |

### Example

**Request:**
```
POST https://eutils.ncbi.nlm.nih.gov/entrez/eutils/ecitmatch.fcgi
db=pubmed&rettype=abstract&retmode=text&bdata=Smith%20J%20et%20al%20Nature%202023
```

---

## 8. efilter - Filter Results

### Purpose
Applies filters to previous esearch results.

### Endpoint
```
POST https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efilter.fcgi
```

### Parameters

| Parameter | Type | Required | Description |
|-----------|------|----------|-------------|
| db | string | Yes | Database name |
| id | string | Yes | UIDs from previous search |
| rettype | string | No | Return type |
| retmode | string | No | Return mode |
| filter | string | No | Filter expression |

### Filters by Database

#### pubmed filters

| Filter | Description |
|--------|-------------|
| has_abstract | Records with abstracts |
| has_fulltext | Records with full text |
| review | Review articles |
| clinical_trial | Clinical trials |

#### nucleotide filters

| Filter | Description |
|--------|-------------|
| chromosome | Chromosome records |
| genomic | Genomic sequences |
| mrna | mRNA sequences |
| refseq | RefSeq records |

---

## History and WebEnv

For large result sets, use server-side history:

### Step 1: Search with History

**Request:**
```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi?db=gene&term=BRCA1[Gene+Name]&usehistory=y&retmode=json
```

**Response:**
```json
{
  "esearchresult": {
    "count": "523",
    "webenv": "MCID_64a1b2c3d4e5f",
    "querykey": "1"
  }
}
```

### Step 2: Fetch Using WebEnv

**Request:**
```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esummary.fcgi?db=gene&webenv=MCID_64a1b2c3d4e5f&query_key=1&retmode=json
```

---

## Error Codes

| Code | Meaning |
|------|---------|
| 400 | Bad request - check parameters |
| 401 | Unauthorized - check API key |
| 429 | Too many requests - add API key |
| 500 | Server error - retry later |
| 503 | Service unavailable |

---

## Rate Limiting

| API Key | Requests/Second | Daily Limit |
|---------|-----------------|-------------|
| None | 3 | 1,000 |
| With Key | 10 | 10,000 |

Apply for API key: https://www.ncbi.nlm.nih.gov/account/

---

## Source

- E-utilities Documentation: https://www.ncbi.nlm.nih.gov/books/NBK25497/
- API Reference: https://www.ncbi.nlm.nih.gov/books/NBK25501/
- EDirect Manual: https://www.ncbi.nlm.nih.gov/books/NBK25500/
