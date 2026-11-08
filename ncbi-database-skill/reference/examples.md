# NCBI E-utilities Examples

Comprehensive examples for common workflows and use cases.

---

## Table of Contents

1. [Gene Queries](#gene-queries)
2. [Sequence Retrieval](#sequence-retrieval)
3. [Taxonomy Queries](#taxonomy-queries)
4. [Literature Search](#literature-search)
5. [Variant Queries](#variant-queries)
6. [Cross-Database Links](#cross-database-links)
7. [Batch Operations](#batch-operations)
8. [Genome Assembly Queries](#genome-assembly-queries)
9. [Python Examples](#python-examples)
10. [Command Line Examples](#command-line-examples)

---

## Gene Queries

### 1.1 Search Gene by Symbol

Find human BRCA1 gene:

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi?db=gene&term=BRCA1[Gene+Name]+AND+Homo+sapiens[Organism]&retmode=json
```

### 1.2 Get Gene Summary by ID

Get detailed summary for gene ID 672 (BRCA1):

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esummary.fcgi?db=gene&id=672&retmode=json
```

### 1.3 Search Multiple Genes

Find multiple cancer-related genes:

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi?db=gene&term=(BRCA1[Gene+Name]+OR+TP53[Gene+Name]+OR+EGFR[Gene+Name])+AND+Homo+sapiens[Organism]&retmode=json
```

### 1.4 Get Gene Genomic Location

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi?db=gene&id=672&rettype=xml&retmode=text
```

Parse the `<GenomicInfo>` tag from the XML response:
```xml
<GenomicInfo>
  <GenomicInfoType>
    <Chr>17</Chr>
    <ChrStart>43044295</ChrStart>
    <ChrStop>43270913</ChrStop>
    <Orientation>2</Orientation>
    <Assembly>GRCh38.p14</Assembly>
    <AssemblyAccession>GCF_000001405.40</AssemblyAccession>
  </GenomicInfoType>
</GenomicInfo>
```

### 1.5 Search Genes by Chromosome

Find all genes on chromosome 17:

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi?db=gene&term=17[Chromosome]+AND+Homo+sapiens[Organism]&retmax=100&retmode=json
```

---

## Sequence Retrieval

### 2.1 Fetch DNA Sequence (FASTA)

Get FASTA sequence by accession:

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi?db=nucleotide&id=NM_001385642&rettype=fasta&retmode=text
```

### 2.2 Fetch DNA Sequence (GenBank)

Get full GenBank record:

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi?db=nucleotide&id=NM_001385642&rettype=gb&retmode=text
```

### 2.3 Fetch Protein Sequence

Get protein FASTA:

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi?db=protein&id=NP_000492.2&rettype=fasta&retmode=text
```

### 2.4 Fetch Sequence Region

Get nucleotides 100-500:

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi?db=nucleotide&id=NM_001385642&rettype=fasta&retmode=text&seqstart=100&seqstop=500
```

### 2.5 Batch Fetch Multiple Sequences

Get multiple accessions:

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi?db=nucleotide&id=NM_001,NM_002,NM_003&rettype=fasta&retmode=text
```

### 2.6 Search Nucleotide by Gene

Find all nucleotide sequences for BRCA1:

```
# Step 1: Get gene ID
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi?db=gene&term=BRCA1[Gene+Name]+AND+Homo+sapiens[Organism]&retmode=json

# Step 2: Link to nucleotide
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/elink.fcgi?dbfrom=gene&linkname=gene_nucleotide&id=672&retmode=json

# Step 3: Fetch sequences (using IDs from step 2)
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi?db=nucleotide&id=ID1,ID2,ID3&rettype=fasta&retmode=text
```

---

## Taxonomy Queries

### 3.1 Get Taxonomy by ID

Get taxonomy for human (TaxID: 9606):

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi?db=taxonomy&id=9606&rettype=xml&retmode=text
```

### 3.2 Get Taxonomy Summary

Get summary format:

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esummary.fcgi?db=taxonomy&id=9606&retmode=json
```

### 3.3 Search Taxonomy by Name

Find taxon by scientific name:

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi?db=taxonomy&term=Brassica+oleracea[Organism]&retmode=json
```

### 3.4 Get Lineage

From taxonomy XML, parse the `<Lineage>` and `<LineageEx>` tags:
```xml
<Lineage>cellular organisms; Eukaryota; Viridiplantae; Streptophyta; Embryophyta; Tracheophyta; Spermatophyta; Magnoliopsida; Eudicots; Rosids; Brassicales; Brassicaceae; Brassica</Lineage>
<LineageEx>
  <Taxon>
    <TaxId>2759</TaxId>
    <ScientificName> Eukaryota</ScientificName>
  </Taxon>
  ...
</LineageEx>
```

---

## Literature Search

### 4.1 Basic PubMed Search

Search for CRISPR reviews in 2023:

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi?db=pubmed&term=CRISPR[Title/Abstract]+AND+review[pt]+AND+2023[dp]&retmax=20&retmode=json
```

### 4.2 Get PubMed Summaries

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esummary.fcgi?db=pubmed&id=37123456,37123455&retmode=json
```

### 4.3 Fetch PubMed Abstract

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi?db=pubmed&id=37123456&rettype=abstract&retmode=text
```

### 4.4 Complex Search

COVID-19 vaccine efficacy studies:

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi?db=pubmed&term=(COVID-19+vaccine[Title/Abstract]+OR+SARS-CoV-2+vaccine[Title/Abstract])+AND+(efficacy[Title/Abstract]+OR+effectiveness[Title/Abstract])+AND+clinical+trial[pt]+AND+English[lang]+AND+2021:2023[dp]&retmax=50&retmode=json&sort=pub+date
```

### 4.5 Get MeSH Terms for PubMed

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/elink.fcgi?dbfrom=pubmed&linkname=pubmed_mesh&id=37123456&retmode=json
```

### 4.6 Search by Author

Publications by a specific author:

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi?db=pubmed&term=Smith+J[Author]+AND+2022[dp]&retmax=20&retmode=json
```

---

## Variant Queries

### 5.1 Search dbSNP by rsID

Get variant information:

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi?db=snp&term=rs123456&retmode=json
```

### 5.2 Get dbSNP Summary

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esummary.fcgi?db=snp&id=123456&retmode=json
```

### 5.3 Search dbSNP by Gene

Find variants in BRCA1:

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi?db=snp&term=BRCA1[Gene]+AND+9606[TaxID]&retmax=100&retmode=json
```

### 5.4 Search ClinVar

Clinical variants:

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi?db=clinvar&term=BRCA1[Gene]+AND+pathogenic[Clinical+Significance]&retmode=json
```

---

## Cross-Database Links

### 6.1 Gene → PubMed

Get PubMed citations for BRCA1:

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/elink.fcgi?dbfrom=gene&linkname=gene_pubmed&id=672&retmode=json
```

### 6.2 Gene → Protein

Get proteins for gene:

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/elink.fcgi?dbfrom=gene&linkname=gene_protein&id=672&retmode=json
```

### 6.3 Gene → Structure

Get 3D structures:

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/elink.fcgi?dbfrom=gene&linkname=gene_structure&id=672&retmode=json
```

### 6.4 Nucleotide → Protein

Get protein translation:

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/elink.fcgi?dbfrom=nuccore&linkname=nuccore_protein&id=NM_001385642&retmode=json
```

### 6.5 PubMed → Gene

Find genes mentioned in PubMed:

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/elink.fcgi?dbfrom=pubmed&linkname=pubmed_gene&id=37123456&retmode=json
```

---

## Batch Operations

### 7.1 Batch Gene Search

Search 10 genes at once:

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi?db=gene&term=BRCA1[Gene+Name]+OR+TP53[Gene+Name]+OR+EGFR[Gene+Name]+OR+MYC[Gene+Name]+OR+KRAS[Gene+Name]+OR+PIK3CA[Gene+Name]+OR+AKT1[Gene+Name]+OR+PTEN[Gene+Name]+OR+RB1[Gene+Name]+OR+APC[Gene+Name]&retmode=json
```

### 7.2 Batch Summary Fetch

Get summary for multiple genes:

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esummary.fcgi?db=gene&id=672,7157,1956,1029,3845,5728,207,5925,6241,324&retmode=json
```

### 7.3 Batch Sequence Fetch

Get multiple sequences:

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi?db=nucleotide&id=NC_000001.11,NM_001385642,NM_000311&rettype=fasta&retmode=text
```

---

## Genome Assembly Queries

### 8.1 Search Assemblies

Find latest human assembly:

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi?db=assembly&term=Homo+sapiens[Organism]+AND+latest[filter]&retmode=json
```

### 8.2 Get Assembly Summary

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esummary.fcgi?db=assembly&id=GCF_000001405.40&retmode=json
```

### 8.3 Get Assembly Accessions

Search for specific assembly:

```
https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi?db=assembly&term=GRCh38[Assembly+Name]+AND+Homo+sapiens[Organism]&retmode=json
```

---

## Python Examples

### 9.1 Basic Search

```python
import urllib.request
import urllib.parse
import json

def esearch(db, term, retmax=20):
    base = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/"
    params = {
        "db": db,
        "term": term,
        "retmax": retmax,
        "retmode": "json"
    }
    url = base + "esearch.fcgi?" + urllib.parse.urlencode(params)
    
    with urllib.request.urlopen(url) as response:
        return json.loads(response.read())

# Search for BRCA1
result = esearch("gene", "BRCA1[Gene Name] AND Homo sapiens[Organism]")
print(result["esearchresult"]["idlist"])
```

### 9.2 Get Gene Summary

```python
def esummary(db, ids):
    base = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/"
    id_string = ",".join(map(str, ids))
    params = {"db": db, "id": id_string, "retmode": "json"}
    url = base + "esummary.fcgi?" + urllib.parse.urlencode(params)
    
    with urllib.request.urlopen(url) as response:
        return json.loads(response.read())

# Get summary for BRCA1 and TP53
summary = esummary("gene", [672, 7157])
for uid, data in summary["result"].items():
    if uid != "uids":
        print(f"{data['name']}: {data.get('description', 'N/A')}")
```

### 9.3 Fetch Sequence

```python
def efetch(db, ids, rettype="fasta", retmode="text"):
    base = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/"
    id_string = ",".join(ids) if isinstance(ids, list) else str(ids)
    params = {"db": db, "id": id_string, "rettype": rettype, "retmode": retmode}
    url = base + "efetch.fcgi?" + urllib.parse.urlencode(params)
    
    with urllib.request.urlopen(url) as response:
        return response.read().decode("utf-8")

# Fetch BRCA1 sequence
sequence = efetch("nucleotide", ["NM_007294"], rettype="fasta")
print(sequence)
```

### 9.4 Using Biopython

```python
from Bio import Entrez

# Set email (required by NCBI)
Entrez.email = "your.email@example.com"

# Search
handle = Entrez.esearch(db="gene", term="BRCA1[Gene Name] AND Homo sapiens[Organism]")
record = Entrez.read(handle)
gene_ids = record["IdList"]

# Summary
handle = Entrez.esummary(db="gene", id=gene_ids[0])
summaries = Entrez.read(handle)

# Fetch sequence
handle = Entrez.efetch(db="nucleotide", id="NM_007294", rettype="fasta", retmode="text")
sequence = handle.read()
```

### 9.5 Using API Key (Rate Limiting)

```python
def esearch_with_key(db, term, retmax=20, api_key=None):
    base = "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/"
    params = {
        "db": db,
        "term": term,
        "retmax": retmax,
        "retmode": "json"
    }
    if api_key:
        params["api_key"] = api_key
    
    url = base + "esearch.fcgi?" + urllib.parse.urlencode(params)
    
    with urllib.request.urlopen(url) as response:
        return json.loads(response.read())

# With API key (higher rate limits)
result = esearch_with_key("gene", "BRCA1", api_key="YOUR_API_KEY")
```

---

## Command Line Examples

### 10.1 Using curl

```bash
# Search for gene
curl "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esearch.fcgi?db=gene&term=BRCA1[Gene+Name]+AND+Homo+sapiens[Organism]&retmode=json"

# Get summary
curl "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/esummary.fcgi?db=gene&id=672&retmode=json"

# Fetch sequence
curl "https://eutils.ncbi.nlm.nih.gov/entrez/eutils/efetch.fcgi?db=nucleotide&id=NM_007294&rettype=fasta&retmode=text"
```

### 10.2 Using EDirect (NCBI Command Line Tools)

```bash
# Install EDirect
# https://www.ncbi.nlm.nih.gov/books/NBK25500/

# Search gene
esearch -db gene -query "BRCA1[Gene Name] AND Homo sapiens[Organism]"

# With history
esearch -db gene -query "BRCA1[Gene Name]" -usehistory y

# Get summary
esearch -db gene -query "BRCA1[Gene Name] AND Homo sapiens[Organism]" | esummary -db gene

# Fetch sequence
efetch -db nucleotide -id NM_007294 -rettype fasta -format text

# Complete workflow
esearch -db gene -query "BRCA1[Gene Name] AND Homo sapiens[Organism]" | \
efetch -db gene -format xml | \
xtract -pattern Gene-ref -element Gene-ref_locus Gene-ref_desc
```

### 10.3 EDirect Examples

```bash
# Search PubMed
esearch -db pubmed -query "CRISPR[Title] AND 2023[dp]" | \
esummary -db pubmed

# Get abstracts
esearch -db pubmed -query "CRISPR review" -max 10 | \
efetch -db pubmed -format abstract

# Gene to PubMed workflow
esearch -db gene -query "TP53[Gene Name] AND Homo sapiens[Organism]" | \
elink -db gene -linkname gene_pubmed | \
esummary -db pubmed

# Batch download
esearch -db nucleotide -query "BRCA1[Gene] AND Homo sapiens[Organism]" -max 100 | \
efetch -db nucleotide -format fasta
```

---

## Additional Resources

- EDirect Tutorial: https://www.ncbi.nlm.nih.gov/books/NBK25501/
- Python Biopython: https://biopython.org/
- EDirect Commands: https://www.ncbi.nlm.nih.gov/books/NBK25500/
