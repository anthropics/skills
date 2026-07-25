# Canonical grounding guard — OpenAI Responses API.
# CONTRACT (cross_model_verification.md, OpenAI block): accept the verdict text only when the
# response proves a hosted web search actually ran. A completed `web_search_call` item is that
# proof. Used with `jq -e`: exit 0 = a search ran (proceed to extract text+sources); exit non-0
# = no search happened → the caller emits NOT_SEARCHED and discards the verdict.
# This is the load-bearing fail-closed boundary: without a completed search the model answered
# from memory and its VERIFIED must never be trusted.
#
# `output` is array-normalized first: a malformed `output` arriving as an object would otherwise be
# iterated by `.output[]?` over its VALUES, letting a `web_search_call` nested in an object falsely
# pass the guard. `arr` makes a non-array `output` yield no items → guard false → NOT_SEARCHED. Each
# element is type-checked as an object before `.type` is read, so a malformed array element (e.g.
# `output: [5]`) is skipped rather than crashing `.type` ("Cannot index number with \"type\"").
def arr($x): if ($x | type) == "array" then $x else [] end;
any(arr(.output)[]; type == "object" and .type == "web_search_call" and .status == "completed")
