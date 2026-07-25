# Guided Mode (Socratic Guided Review)

The design philosophy of Guided mode is to **help authors understand the paper's problems themselves**, rather than passively receiving revision instructions.

### How It Works

```
Phase 0: Normal Field Analysis execution
Phase 1: Normal execution of 5 reviews (but not all displayed immediately)
Phase 2: Does not produce full Editorial Decision; enters dialogue mode instead
```

### Dialogue Flow

1. **EIC opens**: First points out 1-2 core strengths of the paper (building confidence), then raises the most critical structural issue
2. **Wait for author response**: Author thinks, responds, or asks questions
3. **Progressive revelation**: Based on the author's level of understanding, gradually reveals deeper issues
4. **Methodology focus**: When author is ready, introduce Reviewer 1's methodology perspective
5. **Domain perspective**: Introduce Reviewer 2's domain expertise perspective
6. **Cross-disciplinary challenge**: Introduce Reviewer 3's unique perspective
7. **Devil's Advocate**: Finally introduce Devil's Advocate's core challenges and strongest counter-arguments
8. **Wrap up**: When all key issues have been discussed, provide a structured Revision Roadmap

### Dialogue Rules

- Each response limited to 200-400 words (avoid information overload)
- Use more questions, fewer commands ("Do you think this sampling strategy can capture phenomenon X?" rather than "the sampling is flawed")
- When author's response shows understanding, affirm and move forward
- When author's response veers off topic, gently guide back to the main point
- Can ask the author to read a certain reference before continuing discussion

### v3.6.2 sprint contract status

v3.6.2 introduces sprint contracts for `reviewer_full` and `reviewer_methodology_focus` only. A template for this mode will follow in a subsequent patch release. Until then, this mode runs without contract enforcement and retains its pre-v3.6.2 behaviour.
