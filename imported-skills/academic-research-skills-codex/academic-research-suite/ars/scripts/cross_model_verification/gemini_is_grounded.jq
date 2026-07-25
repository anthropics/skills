# Canonical grounding guard — Gemini generateContent (google_search tool).
# CONTRACT (cross_model_verification.md, Gemini block): accept the verdict text only when BOTH
#   - webSearchQueries  (length > 0) — the model actually issued a search, AND
#   - groundingSupports (length > 0) — the verdict TEXT is tied to retrieved chunks.
# webSearchQueries + groundingChunks alone is NOT enough: Gemini can run a search, return chunks,
# then emit an unsupported from-memory verdict whose text references none of them.
# groundingSupports[].groundingChunkIndices is what links answer spans to sources; without it a
# VERIFIED is not actually grounded. Used with `jq -e`: exit 0 = grounded; non-0 = NOT_SEARCHED.
#
# GUARD DERIVES FROM THE EXTRACTOR — by construction, not by a re-implemented predicate. The guard
# embeds the EXACT extraction `gemini_sources.jq` performs (same `candidates[0]` selection, same
# valid-index predicate, same non-empty-string uri filter) and passes iff that extraction yields ≥1
# url AND the model actually issued a search (a non-empty webSearchQueries array on the SAME
# candidate). The safety invariant is **guard-pass ⟹ at least one source extractable**: deriving
# the guard from the extractor — rather than asserting two parallel jq programs agree — makes it
# hold for every input shape (a multi-candidate response where candidate 0 is unsupported, a
# fractional/negative/string/out-of-range index, a non-string uri, AND a malformed NON-OBJECT at any
# dereference point — `candidates[0]`, `groundingMetadata`, a `groundingSupports` element, a cited
# `groundingChunks` element, or its `web` — all leave the extraction empty → guard fails closed →
# an unsupported NOT_FOUND/MISMATCH, which the
# blank-source downgrade does not rescue since it only touches VERIFIED, is never trusted). The
# guard is strictly STRONGER than "has a source": a response carrying chunks but no webSearchQueries
# (sources non-blank, no real search signal) still fails — the converse is intentionally not
# required. Keep this extraction's LOGIC identical to gemini_sources.jq's `$srcs` body — same
# candidate-0 selection, same valid-index predicate, same `obj(obj(chunk).web).uri` non-empty-string
# filter, same order. (The two differ only in how the result is consumed: here it is bound to `$srcs`
# inside a `([ … ]) as $srcs` wrap; there it is piped to `unique | join`, so leading whitespace is
# not byte-for-byte equal — only the extraction operations must stay in lockstep.) Used with
# `jq -e`: exit 0 = grounded; non-0 = NOT_SEARCHED.
#
# `arr/1` array-normalizes every container; `obj/1` object-normalizes every value that is then
# field-dereferenced (`obj(candidates[0]).groundingMetadata`, `obj($meta)`, `obj(support).…Indices`,
# `obj(obj(chunk).web).uri`). Without `obj/1`, a non-object at any of those points (e.g.
# `groundingMetadata: 5`, a `web: 5`) would crash jq ("Cannot index number with string …") instead
# of failing closed — a crash is loud but still violates the crash-free fail-closed contract.
def arr($x): if ($x | type) == "array" then $x else [] end;
def obj($x): if ($x | type) == "object" then $x else {} end;
(obj(arr(obj(.).candidates)[0]).groundingMetadata | obj(.)) as $meta
| arr($meta.groundingChunks) as $chunks
| ([ arr($meta.groundingSupports)[]
     | arr(obj(.).groundingChunkIndices)[]
     | select(type == "number" and . == floor and . >= 0 and . < ($chunks | length)) ]
   | unique
   | [ .[] | obj(obj($chunks[.]).web).uri | select(type == "string" and length > 0) ]) as $srcs
| ((arr($meta.webSearchQueries) | length) > 0) and (($srcs | length) > 0)
