# arXiv Query Syntax Reference

When using `scripts/search_arxiv.py --query "..."`, you can use the following
advanced search features. The script automatically handles URL encoding.

## Field Prefixes

Prefix your search terms to target specific fields:

- `ti:` Title
- `au:` Author
- `abs:` Abstract
- `co:` Comment
- `jr:` Journal Reference
- `cat:` Subject Category (e.g., `cat:cs.AI`)
- `rn:` Report Number
- `all:` All fields

## Boolean Operators

Combine terms using `AND`, `OR`, and `ANDNOT`.
*Example*: `au:del_maestro ANDNOT ti:checkerboard`

## Grouping and Phrases

- **Parentheses `()`**: Group boolean expressions.
  *Example*: `au:del_maestro ANDNOT (ti:checkerboard OR ti:Pyrochlore)`
- **Double Quotes `""`**: Search for exact phrases.
  *Example*: `au:del_maestro AND ti:"quantum criticality"`

## Date Filtering
Filter by the date submitted to arXiv.
Format: `[YYYYMMDDHHMM TO YYYYMMDDHHMM]` (GMT).
*Example*: `au:del_maestro AND submittedDate:[202301010600 TO 202401010600]`
