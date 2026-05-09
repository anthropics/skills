# Environment Notes

## Claude.ai

Claude.ai follows the same draft, test, review, improve loop, but without subagents.

- Run test cases one at a time yourself after reading the skill.
- Skip baseline runs.
- If you cannot open a browser, present outputs directly in chat and collect feedback inline.
- Skip quantitative benchmarking when it depends on baseline comparisons.
- Description optimization requires the `claude` CLI, so skip it when unavailable.
- Blind comparison also requires subagents, so skip it there.
- When updating an installed skill, preserve the original name, copy it to a writable temp directory before editing, and package from the copy.

## Cowork

Cowork supports the main workflow with subagents, but it is usually headless.

- Use `generate_review.py --static <output_path>` instead of launching a browser server.
- Ask the user to open the generated HTML.
- Read downloaded `feedback.json` back into the workspace after review.
- Packaging still works.
- Description optimization can run there if the `claude -p` based tooling is available.
- When updating an existing skill, follow the same preserve-name and copy-to-writable-temp guidance as in Claude.ai.
