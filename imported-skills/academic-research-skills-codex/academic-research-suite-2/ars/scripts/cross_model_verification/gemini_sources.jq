# Canonical source-URL extraction — Gemini generateContent (google_search tool).
# CONTRACT: derive SOURCES ONLY from the chunks actually cited by groundingSupports (the
# supported chunk indices), NOT every groundingChunks entry — so a VERIFIED whose text cites no
# chunk leaves SOURCES blank and is downgraded to NOT_SEARCHED at step 5.
#
# FAIL-CLOSED on malformed indices: a model can emit junk groundingChunkIndices. Without a guard,
#   - a negative index (e.g. -1) silently selects a chunk from the END of the array, fabricating a
#     real-but-wrong source URL that would falsely satisfy the "VERIFIED must carry a source" rule
#     and defeat the downgrade;
#   - a string index raises a jq error ("Cannot index array with string").
# The `select(type=="number" and . == floor and . >= 0 and . < ($chunks|length))` admits only
# valid in-range non-negative integer indices; anything else is dropped, so a malformed support set
# yields blank SOURCES (→ NOT_SEARCHED) rather than a fabricated or crashing result.
#
# Every container is normalized to an array first (`arr/1`): `length` and `$chunks[.]` are only
# meaningful on arrays, and a malformed groundingChunks/groundingSupports arriving as a string or
# object would otherwise mis-count length or crash `$chunks[.]`. The top-level `candidates` is
# array-normalized too, so a malformed `candidates` arriving as an object does not crash the
# `[0]` access (`arr(.candidates)[0]` on a non-array yields null → no metadata → blank sources).
# Every value that is then field-dereferenced is object-normalized (`obj/1`): a non-object
# `candidates[0]`, `groundingMetadata`, `groundingSupports` element, cited `groundingChunks` element,
# or its `web` (e.g. `web: 5`) would otherwise crash jq ("Cannot index number with string …")
# instead of yielding blank SOURCES.
# Extracted URIs are filtered to non-empty strings so a malformed `uri` (a number/bool/object)
# never fabricates a source. Indices must be non-negative INTEGERS (`. == floor`): jq does not
# fractional-index, so a `0.5` would yield null anyway, but excluding it keeps this predicate
# identical to the one gemini_is_grounded.jq derives its verdict from. Used with `jq -r`.
#
# NOTE: gemini_is_grounded.jq embeds the SAME extraction (the `$srcs` body below); it passes iff
# this extraction is non-empty AND webSearchQueries is non-empty. So the guard cannot diverge from
# this extractor on candidate selection, index validity, or uri type, and the invariant is
# one-directional — guard-pass ⟹ ≥1 source (NOT the converse: a chunks-but-no-webSearchQueries
# response extracts a source here yet correctly fails the guard). Keep the two in lockstep if
# either is edited.
def arr($x): if ($x | type) == "array" then $x else [] end;
def obj($x): if ($x | type) == "object" then $x else {} end;
(obj(arr(obj(.).candidates)[0]).groundingMetadata | obj(.)) as $meta
| arr($meta.groundingChunks) as $chunks
| [ arr($meta.groundingSupports)[]
    | arr(obj(.).groundingChunkIndices)[]
    | select(type == "number" and . == floor and . >= 0 and . < ($chunks | length)) ]
| unique
| [ .[] | obj(obj($chunks[.]).web).uri | select(type == "string" and length > 0) ]
| unique
| join(", ")
