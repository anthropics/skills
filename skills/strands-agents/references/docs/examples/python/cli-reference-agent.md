# A CLI reference implementation of a Strands agent

The Strands CLI is a reference implementation built on top of the Strands SDK. It provides a terminal-based interface for interacting with Strands agents, demonstrating how to make a fully interactive streaming application with the Strands SDK. 

The Strands CLI is Open-Source and available [strands-agents/agent-builder](https://github.com/strands-agents/agent-builder#custom-model-provider).

## Prerequisites

In addition to the prerequisites listed for [examples](../README.md), this example requires the following:

- Python package installer (`pip`)
- [pipx](https://github.com/pypa/pipx) for isolated Python package installation
- Git

## Standard Installation

To install the Strands CLI:

```bash
# Install
pipx install strands-agents-builder

# Run Strands CLI
strands
```

## Manual Installation

If you prefer to install manually:

```bash
# Clone repository
git clone https://github.com/strands-agents/agent-builder /path/to/custom/location

# Create virtual environment
cd /path/to/custom/location
python -m venv venv

# Activate virtual environment
source venv/bin/activate

# Install dependencies
pip install -e .

# Create symlink
sudo ln -sf /path/to/custom/location/venv/bin/strands /usr/local/bin/strands
```

## CLI Verification

To verify your CLI installation:

```bash
# Run Strands CLI with a simple query
strands "Hello, Strands!"
```

## Command Line Arguments

| Argument | Description | Example |
|----------|-------------|---------|
| `query` | Question or command for Strands | `strands "What's the current time?"` |
| `--kb`, `--knowledge-base` | `KNOWLEDGE_BASE_ID` | Knowledge base ID to use for retrievals |
| `--model-provider` | `MODEL_PROVIDER` | Model provider to use for inference |
| `--model-config` | `MODEL_CONFIG` | Model config as JSON string or path |

## Interactive Mode Commands

When running Strands in interactive mode, you can use these special commands:

| Command | Description |
|---------|-------------|
| `exit` | Exit Strands CLI |
| `!command` | Execute shell command directly |

## Shell Integration

Strands CLI integrates with your shell in several ways:

### Direct Shell Commands

Execute shell commands directly by prefixing with `!`:

```bash
> !ls -la
> !git status
> !docker ps
```

### Natural Language Shell Commands

Ask Strands to run shell commands using natural language:

```bash
> Show me all running processes
> Create a new directory called "project" and initialize a git repository there
> Find all Python files modified in the last week
```

## Environment Variables

Strands CLI respects these environment variables for basic configuration:

| Variable | Description | Default |
|----------|-------------|---------|
| `STRANDS_SYSTEM_PROMPT` | System instructions for the agent | `You are a helpful agent.` |
| `STRANDS_KNOWLEDGE_BASE_ID` | Knowledge base for memory integration | None |

Example:

```bash
export STRANDS_KNOWLEDGE_BASE_ID="YOUR_KB_ID"
strands "What were our key decisions last week?"
```
## Command Line Arguments

Command line arguments override any configuration from files or environment variables:

```bash
# Enable memory with knowledge base
strands --kb your-kb-id
```

## Custom Model Provider

You can configure strands to use a different model provider with specific settings by passing in the following arguments:

```bash
strands --model-provider <NAME> --model-config <JSON|FILE>
```

As an example, if you wanted to use the packaged Ollama provider with a specific model id, you would run:

```bash
strands --model-provider ollama --model-config '{"model_id": "llama3.3"}'
```

Strands is packaged with `bedrock` and `ollama` as providers.
