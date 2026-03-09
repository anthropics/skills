# Agent Configuration [Experimental]

{{ experimental_feature_warning() }}

The experimental `config_to_agent` function provides a simple way to create agents from configuration files or dictionaries.

## Overview

`config_to_agent` allows you to:

- Create agents from JSON files or dictionaries
- Use a simple functional interface for agent instantiation
- Support both file paths and dictionary configurations
- Leverage the Agent class's built-in tool loading capabilities

## Basic Usage

### Dictionary Configuration

```python
from strands.experimental import config_to_agent

# Create agent from dictionary
agent = config_to_agent({
    "model": "us.anthropic.claude-3-5-sonnet-20241022-v2:0",
    "prompt": "You are a helpful assistant"
})
```

### File Configuration

```python
from strands.experimental import config_to_agent

# Load from JSON file (with or without file:// prefix)
agent = config_to_agent("/path/to/config.json")
# or
agent = config_to_agent("file:///path/to/config.json")
```

#### Simple Agent Example

```json
{
    "prompt": "You are a helpful assistant."
}
```

#### Coding Assistant Example

```json
{
  "model": "us.anthropic.claude-3-5-sonnet-20241022-v2:0",
  "prompt": "You are a coding assistant. Help users write, debug, and improve their code. You have access to file operations and can execute shell commands when needed.",
  "tools": ["strands_tools.file_read", "strands_tools.editor", "strands_tools.shell"]
}
```

## Configuration Options

### Supported Keys

- `model`: Model identifier (string) - [[Only supports AWS Bedrock model provider string](../../quickstart.md#using-a-string-model-id)]
- `prompt`: System prompt for the agent (string)
- `tools`: List of tool specifications (list of strings)
- `name`: Agent name (string)

### Tool Loading

The `tools` configuration supports Python-specific tool loading formats:

```json
{
  "tools": [
    "strands_tools.file_read",           // Python module path
    "my_app.tools.cake_tool",            // Custom module path  
    "/path/to/another_tool.py",          // File path
    "my_module.my_tool_function"         // @tool annotated function
  ]
}
```

The Agent class handles all tool loading internally, including:

- Loading from module paths
- Loading from file paths
- Error handling for missing tools
- Tool validation

!!! note "Tool Loading Limitations"
    Configuration-based agent setup only works for tools that don't require code-based instantiation. For tools that need constructor arguments or complex setup, use the programmatic approach after creating the agent:
    
    ```python
    import http.client
    from sample_module import ToolWithConfigArg
    
    agent = config_to_agent("config.json")
    # Add tools that need code-based instantiation
    agent.process_tools([ToolWithConfigArg(http.client.HTTPSConnection("localhost"))])
    ```

### Model Configurations

The `model` property uses the [string based model id feature](../../quickstart.md#using-a-string-model-id). You can reference [AWS's Model Id's](https://docs.aws.amazon.com/bedrock/latest/userguide/inference-profiles-support.html) to identify a model id to use. If you want to use a different model provider, you can pass in a model as part of the `**kwargs` of the `config_to_agent` function:

```python
from strands.experimental import config_to_agent
from strands.models.openai import OpenAIModel

# Create agent from dictionary
agent = config_to_agent(
  config={"name": "Data Analyst"},
  model=OpenAIModel(
    client_args={
        "api_key": "<KEY>",
    },
    model_id="gpt-4o",
  )
)
```

Additionally, you can override the `agent.model` attribute of an agent to configure a new model provider:

```python
from strands.experimental import config_to_agent
from strands.models.openai import OpenAIModel

# Create agent from dictionary
agent = config_to_agent(
  config={"name": "Data Analyst"}
)

agent.model = OpenAIModel(
  client_args={
      "api_key": "<KEY>",
  },
  model_id="gpt-4o",
)
```

## Function Parameters

The `config_to_agent` function accepts:

- `config`: Either a file path (string) or configuration dictionary
- `**kwargs`: Additional [Agent constructor parameters](../../../api-reference/python/agent/agent.md#strands.agent.agent.Agent.__init__) that override config values

```python
# Override config values with valid agent parameters
agent = config_to_agent(
    "/path/to/config.json",
    name="Data Analyst"
)
```

## Best Practices

1. **Override when needed**: Use kwargs to override configuration values dynamically
2. **Leverage agent defaults**: Only specify configuration values you want to override
3. **Use standard tool formats**: Follow Agent class conventions for tool specifications
4. **Handle errors gracefully**: Catch FileNotFoundError and JSONDecodeError for robust applications

