# JSON Output Structure Reference

The python script `screen_api.py` saves the raw GraphQL response to a temporary
JSON file. The top-level structure is always:

```json
{
  "data": {
    "<QueryName>": <ResultArrayOrObject>
  }
}
```

Below are the standard structures for each command to help you craft efficient
`jq` or `python` parsing queries:

## 1. `search` (`cCRESCREENSearch`)

Returns an array of cCRE objects.

```json
{
  "data": {
    "cCRESCREENSearch": [
      {
        "chrom": "<string>", "start": "<int>", "len": "<int>",
        "pct": "<string>", // Classification: PLS, pELS, dELS, etc.
        "ctcf_zscore": "<float>", "dnase_zscore": "<float>",
        "atac_zscore": "<float>", "enhancer_zscore": "<float>",
        "promoter_zscore": "<float>", "info": { "accession": "<string>" },
        "ctspecific": [
          // Only present if --cellType was specified
          {
            "ct": "<string>",
            "ctcf_zscore": "<float>",
            "dnase_zscore": "<float>",
            "h3k4me3_zscore": "<float>",
            "h3k27ac_zscore": "<float>",
            "atac_zscore": "<float>"
          }
        ]
      }
    ]
  }
}
```

## 2. `nearby-genes` (`cCRESCREENSearch`)

```json
{
  "data": {
    "cCRESCREENSearch": [
      {
        "chrom": "<string>", "start": "<int>", "len": "<int>",
        "pct": "<string>", "info": { "accession": "<string>" },
        "nearestgenes": [
          { "gene": "<string>", "distance": "<int>" }
        ]
      }
    ]
  }
}
```

## 3. `details` (`cCREQuery` and `ccREBiosampleQuery`)

```json
{
  "data": {
    "cCREQuery": [
      {
        "accession": "<string>", "group": "<string>",
        "dnase": "<float>", "h3k4me3": "<float>", "h3k27ac": "<float>",
        "ctcf": "<float>", "atac": "<float>", "coordinates":
        { "chromosome": "<string>", "start": "<int>", "end": "<int>" }
      }
    ],
    "ccREBiosampleQuery": {
      "biosamples": [
        {
          "sampleType": "<string>",
          "name": "<string>",
          "ontology": "<string>",
          "displayname": "<string>",
          "dnase_acc": "<string|null>",
          "h3k4me3_acc": "<string|null>",
          "h3k27ac_acc": "<string|null>",
          "ctcf_acc": "<string|null>",
          "is_type_a": "<bool>",
          "cCREZScores": [
            {
              "score": "<float>",
              "assay": "<string>",
              "experiment_accession": "<string>"
            }
          ]
        }
      ]
    }
  }
}
```

## 4. `biosamples` (`ccREBiosampleQuery`)

```json
{
  "data": {
    "ccREBiosampleQuery": {
      "biosamples": [
        {
          "name": "<string>",
          "ontology": "<string>",
          "lifeStage": "<string>",
          "sampleType": "<string>",
          "displayname": "<string>",
          "dnase": "<string|null>",
          "h3k4me3": "<string|null>",
          "h3k27ac": "<string|null>",
          "ctcf": "<string|null>",
          "is_type_a": "<bool>"
        }
      ]
    }
  }
}
```

## 5. `orthologs` (`orthologQuery`)

```json
{
  "data": {
    "orthologQuery": [
      {
        "assembly": "<string>", "accession": "<string>",
        "ortholog": [
          {
            "stop": "<int>",
            "start": "<int>",
            "chromosome": "<string>",
            "accession": "<string>"
          }
        ]
      }
    ]
  }
}
```

## 6. `linked-genes` (`linkedGenesQuery`)

```json
{
  "data": {
    "linkedGenesQuery": [
      {
        "accession": "<string>", "gene": "<string>", "geneid": "<string>",
        "genetype": "<string>", "method": "<string>", "effectsize": "<float>",
        "assay": "<string>", "celltype": "<string>", "tissue": "<string>",
        "score": "<float>", "displayname": "<string>"
      }
    ]
  }
}
```

## 7. `entex` (`entexQuery` or `entexActiveAnnotationsQuery`)

For `--accession`:

```json
{
  "data": {
    "entexQuery": [
      {
        "assay": "<string>", "accession": "<string>", "hap1_count": "<int>",
        "hap2_count": "<int>", "hap1_allele_ratio": "<float>",
        "p_betabinom": "<float>", "tissue": "<string>", "donor": "<string>",
        "imbalance_significance": "<string>"
      }
    ]
  }
}
```

For `--region`:

```json
{
  "data": {
    "entexActiveAnnotationsQuery": [
      { "tissue": "<string>", "assay_score": "<float>" }
    ]
  }
}
```

## 8. `gene-expression` (combined from `gene`, `gene_quantification`, `gene_dataset`)

The output is post-processed into a flat structure combining gene metadata with
per-experiment TPM values and biosample context.

```json
{
  "data": {
    "gene": {
      "name": "<string>",
      "id": "<string>",
      "coordinates": {
        "start": "<int>", "chromosome": "<string>", "end": "<int>"
      }
    },
    "gene_id_prefix": "<string>",
    "assembly": "<string>",
    "expression": [
      {
        "biosample": "<string|null>",
        "tissue": "<string|null>",
        "cell_compartment": "<string|null>",
        "biosample_type": "<string|null>",
        "assay_term_name": "<string|null>",
        "experiment_accession": "<string>",
        "file_accession": "<string>",
        "tpm": "<float>",
        "fpkm": "<float>"
      }
    ]
  }
}
```

## 9. `gwas`

(`getAllGwasStudies`, `getSNPsforGWASStudies`, `getGWASCtEnrichmentQuery`)

```json
{
  "data": {
    "getAllGwasStudies": [
      {
        "study": "<string>", "totalldblocks": "<int>", "author": "<string>",
        "pubmedid": "<string>", "studyname": "<string>"
      }
    ]
  }
}
// OR for snps: "getSNPsforGWASStudies": [...]
// OR for enrichment: "getGWASCtEnrichmentQuery": [...]
```
