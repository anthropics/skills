# Canonical source-URL extraction — OpenAI Responses API.
# CONTRACT: a VERIFIED verdict must carry at least one source the model actually cited. Sources
# come ONLY from `url_citation` annotations the model attached to its output_text — never
# fabricated. If this returns empty, the caller's SOURCES line is blank and step 5 downgrades a
# VERIFIED with no source to NOT_SEARCHED. Used with `jq -r`.
#
# FAIL-CLOSED on a malformed `url`: filter to non-empty strings so a `url_citation` whose `url` is
# a bool/number/object never fabricates a SOURCES entry (defeating the downgrade) or crashes
# `join` (an object `url` is not addable to a string). EVERY container on the path — `output`,
# `content`, `annotations` — is array-normalized (`arr`), so a malformed response with any of them
# arriving as an object (whose values `[]?` would otherwise iterate, surfacing a url nested in an
# object) yields no sources rather than a fabricated one.
def arr($x): if ($x | type) == "array" then $x else [] end;
[arr(.output)[] | select(type=="object" and .type=="message")
  | arr(.content)[] | select(type=="object" and .type=="output_text")
  | arr(.annotations)[] | select(type=="object" and .type=="url_citation") | .url
  | select(type == "string" and length > 0)] | unique | join(", ")
