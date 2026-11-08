# AI/ML Engineering Mentor Skill

An open Agent Skill that turns Claude into a structured, project-oriented AI/ML engineering mentor.

## What it does

This skill helps with:

- AI/ML concept learning
- mathematical intuition
- Python and ML debugging
- project architecture
- RAG systems
- agentic AI
- prompt engineering
- model selection
- hyperparameter tuning
- reinforcement learning
- project-based learning

The skill uses progressive disclosure: the core behavior lives in `SKILL.md`, while deeper material is separated into reference files and examples.

## Design principles

1. Explain reasoning, not just answers.
2. Start from a generic example and then connect to the user's project.
3. Debug from evidence instead of guessing.
4. Verify current technical information when needed.
5. Keep architecture explanations explicit about data flow and control flow.
6. Encourage independent problem solving.

## Structure

```text
ai-ml-engineering-mentor/
├── SKILL.md
├── README.md
├── LICENSE
├── references/
│   ├── learning-framework.md
│   ├── debugging-playbook.md
│   ├── ml-workflow.md
│   ├── rag-and-agents.md
│   └── project-workflow.md
├── examples/
│   ├── xgboost.md
│   ├── reinforcement-learning.md
│   ├── rag.md
│   └── debugging.md
├── evaluations/
│   └── test-cases.md
└── scripts/
    └── validate_skill.py
```

## Example prompts

- "Explain gradient descent from intuition to implementation."
- "Why am I getting this XGBoost label error?"
- "Review this RAG architecture and find retrieval bottlenecks."
- "Explain my LangGraph project step by step."
- "Teach me reinforcement learning through a project."
- "Compare GridSearchCV and RandomizedSearchCV."

## Testing

Run:

```bash
python scripts/validate_skill.py
```

Then evaluate the skill against the scenarios in `evaluations/test-cases.md`.

## License

Apache License 2.0.
