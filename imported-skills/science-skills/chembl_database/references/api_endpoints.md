# ChEMBL API Endpoints Reference

Base URL: `https://www.ebi.ac.uk/chembl/api/data`

## Standard Endpoint Patterns

Most endpoints support:

- **List**: `GET /<endpoint>.json?limit=N&offset=M`
- **Single**: `GET /<endpoint>/<ID>.json`
- **Batch**: `GET /<endpoint>/set/<ID1>;<ID2>.json`
- **Search**: `GET /<endpoint>/search.json?q=<query>` (only selected endpoints)

## Searchable Endpoints

Only these endpoints support free-text search (`?q=`):

- `activity`
- `assay`
- `chembl_id_lookup`
- `document`
- `molecule`
- `protein_classification`
- `target`

## Special Endpoints

### Similarity Search

`GET /similarity/<SMILES>/<threshold>.json`

Returns molecules similar to the given SMILES above the threshold (0-100).

### Substructure Search

`GET /substructure/<SMILES>.json`

Returns molecules containing the given substructure.

### Image

`GET /image/<ChEMBL_ID_or_InChI_Key>`

Returns a 2D structure image (SVG). Parameters:

- `engine` — rendering toolkit (default: rdkit)
- `dimensions` — image size in pixels (max 500, default: 500)
- `ignoreCoords` — recompute 2D coordinates

### Status

`GET /status.json`

Returns API status information.

## Filter Operators

ChEMBL supports Django-style filter operators as query parameters:

| Operator | Description | Example |
|---|---|---|
| (none) | Exact match | `molecule_chembl_id=CHEMBL25` |
| `__exact` | Exact match | `pref_name__exact=Aspirin` |
| `__iexact` | Case-insensitive exact | `pref_name__iexact=aspirin` |
| `__contains` | Substring match | `pref_name__contains=aspirin` |
| `__icontains` | Case-insensitive substring | `pref_name__icontains=aspirin` |
| `__startswith` | Prefix match | `pref_name__startswith=Asp` |
| `__endswith` | Suffix match | `pref_name__endswith=rin` |
| `__gt` | Greater than | `standard_value__gt=100` |
| `__gte` | Greater than or equal | `standard_value__gte=100` |
| `__lt` | Less than | `standard_value__lt=100` |
| `__lte` | Less than or equal | `standard_value__lte=100` |
| `__in` | Value in list | `molecule_type__in=Small molecule,Antibody` |
| `__isnull` | Null check | `pchembl_value__isnull=false` |
| `__range` | Value in range | `mw_freebase__range=200,500` |
| `__flexmatch` | SMILES structure match | `canonical_smiles__flexmatch=<SMILES>` |

## Common ID Formats

| Resource | ID Format | Example |
|---|---|---|
| Molecule | CHEMBLNNN | CHEMBL25 |
| Target | CHEMBLNNN | CHEMBL203 |
| Assay | CHEMBLNNN | CHEMBL615819 |
| Document | CHEMBLNNN | CHEMBL1127557 |
| Activity | Numeric | 31863 |
| ATC Class | ATC code | N02BA01 |

## Pagination

All list endpoints return paginated results. Use `limit` and `offset`:

- `?limit=20&offset=0` — first 20 results
- `?limit=20&offset=20` — next 20 results

The response includes `page_meta` with `total_count`, `limit`, `offset`,
`next`, and `previous` links.
