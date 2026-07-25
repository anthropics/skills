# OLS API Reference

Base URL: `https://www.ebi.ac.uk/ols4/api`

## Key Endpoints

### Search & Suggest
| Endpoint | Description |
|---|---|
| `/search?q={query}` | Full-text search across all ontologies |
| `/suggest?q={query}` | Autocomplete suggestions for partial term names |
| `/select?q={query}` | Select endpoint (similar to search with additional filters) |

### Ontologies
| Endpoint | Description |
|---|---|
| `/ontologies` | List all ontologies |
| `/ontologies/{id}` | Get ontology details |

### Terms (Classes)
| Endpoint | Description |
|---|---|
| `/ontologies/{id}/terms` | List/browse terms in an ontology |
| `/ontologies/{id}/terms/{iri}` | Get term by double-encoded IRI |
| `/ontologies/{id}/terms/{iri}/parents` | Direct parents (is-a only) |
| `/ontologies/{id}/terms/{iri}/children` | Direct children (is-a only) |
| `/ontologies/{id}/terms/{iri}/ancestors` | All ancestors (is-a only) |
| `/ontologies/{id}/terms/{iri}/descendants` | All descendants (is-a only) |
| `/ontologies/{id}/terms/{iri}/hierarchicalParents` | Parents including transitive relations (part_of, develops_from) |
| `/ontologies/{id}/terms/{iri}/hierarchicalChildren` | Children including transitive relations |
| `/ontologies/{id}/terms/{iri}/hierarchicalAncestors` | All ancestors including transitive relations |
| `/ontologies/{id}/terms/{iri}/hierarchicalDescendants` | All descendants including transitive relations |
| `/ontologies/{id}/terms/{iri}/graph` | Graph JSON for a term |
| `/ontologies/{id}/terms/roots` | Root terms of an ontology |
| `/ontologies/{id}/terms/preferredRoots` | Preferred root terms |

### Properties
| Endpoint | Description |
|---|---|
| `/ontologies/{id}/properties` | List properties in an ontology |
| `/ontologies/{id}/properties/{iri}` | Get property details |
| `/ontologies/{id}/properties/{iri}/parents` | Property parents |
| `/ontologies/{id}/properties/{iri}/children` | Property children |
| `/ontologies/{id}/properties/{iri}/ancestors` | Property ancestors |
| `/ontologies/{id}/properties/{iri}/descendants` | Property descendants |
| `/ontologies/{id}/properties/roots` | Root properties |

### Individuals (Instances)
| Endpoint | Description |
|---|---|
| `/ontologies/{id}/individuals` | List individuals in an ontology |
| `/ontologies/{id}/individuals/{iri}` | Get individual details |
| `/ontologies/{id}/individuals/{iri}/types` | Get direct types (classes) |
| `/ontologies/{id}/individuals/{iri}/alltypes` | Get all types including ancestors |

### Statistics
| Endpoint | Description |
|---|---|
| `/v2/stats` | Index statistics (ontology/class/property/individual counts) |

## OBO ID Format

OBO IDs follow the pattern `PREFIX:NUMBER`, e.g., `GO:0005634`.

The corresponding IRI is typically:
`http://purl.obolibrary.org/obo/PREFIX_NUMBER` (e.g.,
`http://purl.obolibrary.org/obo/GO_0005634`).

When passing IRIs to the API, they must be **double URL-encoded**.

## Hierarchical vs Regular Relations

- **Regular** (`parents`, `children`, `ancestors`, `descendants`): Follow only
  `subClassOf` (is-a) relationships.
- **Hierarchical** (`hierarchicalParents`, `hierarchicalChildren`, etc.):
  Follow `subClassOf` **plus** transitive properties like `part of`,
  `develops from`, etc. This gives a more complete picture of the ontology
  structure.

## Common Ontology IDs

| ID | Name | Focus |
|---|---|---|
| `go` | Gene Ontology | Molecular function, biological process, cellular component |
| `doid` | Disease Ontology | Human disease classification |
| `efo` | Experimental Factor Ontology | Experimental variables (GWAS, expression) |
| `hp` | Human Phenotype Ontology | Human phenotypic abnormalities |
| `chebi` | Chemical Entities of Biological Interest | Small molecules |
| `mondo` | Mondo Disease Ontology | Cross-species disease integration |
| `ncit` | NCI Thesaurus | Cancer-related terminology |
| `cl` | Cell Ontology | Cell types |
| `uberon` | Uberon | Cross-species anatomical structures |
| `so` | Sequence Ontology | Genomic sequence features |
| `pato` | Phenotype And Trait Ontology | Phenotypic qualities |
| `envo` | Environment Ontology | Environmental biomes and habitats |
| `obi` | Ontology for Biomedical Investigations | Experimental assays and protocols |
| `iao` | Information Artifact Ontology | Information entities |
| `duo` | Data Use Ontology | Data use permissions and conditions |

## Search Parameters

| Parameter | Description |
|---|---|
| `q` | Search query (required) |
| `ontology` | Filter by ontology ID |
| `type` | `class`, `property`, `individual`, or `ontology` |
| `exact` | `true` for exact label match |
| `obsoletes` | `false` to exclude obsolete terms |
| `local` | `true` to only return terms in their defining ontology |
| `childrenOf` | Restrict to children of given IRI(s) |
| `allChildrenOf` | Restrict to all children (incl. transitive relations) |
| `queryFields` | Fields to search in |
| `fieldList` | Fields to return |
| `groupField` | Group results by IRI |
| `isLeaf` | `true` for leaf terms only |
| `rows` | Results per page (default 10, max 500) |
| `start` | Pagination offset |
