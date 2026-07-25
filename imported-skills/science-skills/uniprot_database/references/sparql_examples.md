# UniProt SPARQL Examples

This document contains curated SPARQL queries for accessing UniProt data.
These examples are optimized for complex discovery and cross-database
federated queries.

## Essential Prefixes

```text
PREFIX up: <http://purl.uniprot.org/core/>
PREFIX taxon: <http://purl.uniprot.org/taxonomy/>
PREFIX rdf: <http://www.w3.org/1999/02/22-rdf-syntax-ns#>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
PREFIX skos: <http://www.w3.org/2004/02/skos/core#>
```

## 1. Retrieve Human Proteins with Gene Names

```text
SELECT ?protein ?mnemonic ?geneName
WHERE {
  ?protein a up:Protein ;
           up:reviewed true ;
           up:organism taxon:9606 ;
           up:mnemonic ?mnemonic .
  OPTIONAL {
    ?protein up:encodedBy ?gene .
    ?gene skos:prefLabel ?geneName .
  }
}
LIMIT 10
```

## 2. Mapping UniProtKB to PDB (3D Structure)

Find reviewed proteins that have an associated 3D structure in PDB.

```text
SELECT ?protein ?pdbLink
WHERE {
  ?protein a up:Protein ;
           up:reviewed true ;
           rdfs:seeAlso ?pdbLink .
  ?pdbLink up:database <http://purl.uniprot.org/database/PDB> .
}
LIMIT 10
```

## 3. Find Proteins by Keyword (e.g., DNA Binding)

```text
SELECT ?protein ?name
WHERE {
  ?protein a up:Protein ;
           up:reviewed true ;
           up:recommendedName/up:fullName ?name ;
           up:classifiedWith <http://purl.uniprot.org/keywords/238> . # DNA-binding
}
```

## 4. Counting Entries Efficiently

### 4.1 Count Reviewed Proteins per Organism
```text
PREFIX up: <http://purl.uniprot.org/core/>
PREFIX taxon: <http://purl.uniprot.org/taxonomy/>
SELECT (COUNT(?protein) AS ?count)
WHERE {
  ?protein a up:Protein ;
           up:reviewed true ;
           up:organism taxon:9606 .
}
```

### 4.2 Count Proteins per Enzyme Class (Top Level)
```text
PREFIX up: <http://purl.uniprot.org/core/>
SELECT ?enzymeClass (COUNT(?protein) AS ?count)
WHERE {
  ?protein a up:Protein ;
           up:enzyme ?enzymeClass .
}
GROUP BY ?enzymeClass
ORDER BY DESC(?count)
```

### 4.3 Count reviewed proteins with PDB structures
```text
PREFIX up: <http://purl.uniprot.org/core/>
PREFIX rdfs: <http://www.w3.org/2000/01/rdf-schema#>
SELECT (COUNT(?protein) AS ?count)
WHERE {
  ?protein a up:Protein ;
           up:reviewed true ;
           rdfs:seeAlso ?pdbLink .
  ?pdbLink up:database <http://purl.uniprot.org/database/PDB> .
}
```

## 5. Federated Query (UniProt + Wikidata)

*Note: This query requires the SPARQL endpoint to support federation
(`SERVICE` keyword).*

```text
SELECT ?protein ?wikidataLabel
WHERE {
  ?protein a up:Protein ;
           up:reviewed true ;
           up:organism taxon:9606 .

  SERVICE <https://query.wikidata.org/sparql> {
    ?wikidataItem wdt:P352 ?uniprotAccession . # P352: UniProt ID in Wikidata
    ?wikidataItem rdfs:label ?wikidataLabel .
    FILTER(LANG(?wikidataLabel) = "en")
  }
}
LIMIT 5
```
