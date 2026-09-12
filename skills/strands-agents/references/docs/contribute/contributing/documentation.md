# Contributing to documentation

Good documentation helps developers succeed with Strands. We welcome contributions that make our docs clearer, more complete, or more helpful. Our documentation lives in the [docs repository](https://github.com/strands-agents/docs).

## What we accept

We're looking for contributions that improve the developer experience. Documentation changes can range from small typo fixes to complete new guides.

| Type | Description |
|------|-------------|
| Typo fixes | Spelling, grammar, and formatting corrections |
| Clarifications | Rewording confusing sections |
| New examples | Code samples and tutorials |
| New guides | Complete tutorials or concept pages |
| Community extensions | Documentation for community-built packages |

## Setup

!!! warning "Migration in progress"
    This section will be rewritten as we migrate to a new CMS.

Let's get the docs running locally so you can preview your changes as you work. The docs are built with [MkDocs Material](https://squidfunk.github.io/mkdocs-material/).

```bash
# Clone the docs repository
git clone https://github.com/strands-agents/docs.git
cd docs

# Create and activate virtual environment
python -m venv .venv
source .venv/bin/activate  # On Windows use: .venv\Scripts\activate

# Install dependencies
pip install -e .

# Start the local development server
mkdocs serve

# Preview at http://localhost:8000
```

The development server automatically reloads when you save changes, so you can see your edits immediately.

## Submission process

The submission process varies based on the size of your change. Small fixes can go straight to PR, while larger changes benefit from discussion first.

1. **Fork the docs repository** on GitHub
2. **Create a branch** with a descriptive name like `docs/clarify-tools-usage` or `docs/fix-typo-agent-loop`
3. **Make your changes** in your favorite editor
4. **Preview locally** with `mkdocs serve` to verify formatting and links work correctly
5. **Submit a pull request** with a clear description of what you changed and why

**For small changes** (typos, grammar fixes, minor clarifications), you can skip local preview and go straight to PR. We'll catch any issues in review.

**For larger changes** (new guides, significant rewrites), we recommend opening a GitHub Discussion first to align on approach and scope.

## Style guidelines

We aim for documentation that teaches, not just describes. A reader finishes understanding the "why" before the "how." This section covers our voice, writing style, and code example conventions.

### Voice and tone

Our documentation uses a collaborative, developer-peer voice. We write as knowledgeable colleagues helping you succeed.

| Principle | Example | Why |
|-----------|---------|-----|
| Use "you" for the reader | "You create an agent by..." not "An agent is created by..." | Direct and personal |
| Use "we" collaboratively | "Let's install the SDK" not "Install the SDK" | Creates partnership |
| Active voice, present tense | "The agent returns a response" not "A response will be returned" | Clear and immediate |
| Explain why before how | Start with the problem, then the solution | Builds understanding |

### Writing style

Keep prose tight and focused. Readers scan documentation looking for answers.

| Do | Don't |
|----|-------|
| Keep sentences under 25 words | Write long, complex sentences with multiple clauses |
| Use "to create an agent, call..." | Use "in order to create an agent, you should call..." |
| Include code examples | Describe without showing |
| Use tables for comparisons | Use long bullet lists for structured data |
| Add lead-in sentences before lists | Jump directly into bulleted lists |

### Code examples

Code examples are critical—they show developers exactly what to do. Always test your examples before submitting.

- Test all code — every example must actually work
- Include both languages — provide Python and TypeScript when both are supported
- Start simple — show the minimal example first, then add complexity
- Add comments — explain non-obvious parts
- Use realistic names — avoid foo/bar, use descriptive names

```python
# Good: Start simple
from strands import Agent
agent = Agent()
agent("Hello, world!")

# Then show configuration
from strands import Agent
from strands.models import BedrockModel

agent = Agent(
    model=BedrockModel(model_id="anthropic.claude-3-sonnet"),
    system_prompt="You are a helpful assistant."
)
agent("What's the weather like?")
```

