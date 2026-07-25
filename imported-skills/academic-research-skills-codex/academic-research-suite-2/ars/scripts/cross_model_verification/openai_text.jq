# Canonical verdict-text extraction — OpenAI Responses API.
# Joins all output_text segments of the message into the verdict text. Not a safety boundary by
# itself (the search guard + the sources filter are); extracted here so the doc and the test
# share one definition. `output` and `content` are array-normalized for consistency with the
# guard/sources filters (a non-array container yields empty text), and `.text` is filtered to
# strings so a malformed non-string `text` (an object) does not crash `join` (`"" + {} ` errors).
# Used with `jq -r`.
def arr($x): if ($x | type) == "array" then $x else [] end;
[arr(.output)[] | select(type=="object" and .type=="message")
  | arr(.content)[] | select(type=="object" and .type=="output_text")
  | .text | select(type == "string")] | join("\n")
