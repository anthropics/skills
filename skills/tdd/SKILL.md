---
name: tdd
description: >
  Red-Green-Refactor TDD workflow. Use when writing tests, implementing
  features test-first, or when the user asks for TDD discipline.
---

# TDD Workflow

Always use Red-Green-Refactor:

1. **Red** — Write a failing test first. Run it. See it fail.
2. **Green** — Write minimum code to pass the test.
3. **Refactor** — Clean up while keeping tests green.

```bash
pytest tests/test_feature.py -v       # RED - must fail
# write code
pytest tests/test_feature.py -v       # GREEN - must pass
# refactor
pytest tests/ -v                      # ALL GREEN - nothing broken
```

Ship the smallest working change. Every line must justify itself.
