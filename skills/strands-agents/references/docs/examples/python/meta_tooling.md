# Meta-Tooling Example - Strands Agent's Dynamic Tool Creation

Meta-tooling refers to the ability of an AI system to create new tools at runtime, rather than being limited to a predefined set of capabilities. The following [example](https://github.com/strands-agents/docs/blob/main/docs/examples/python/meta_tooling.py) demonstrates Strands Agents' meta-tooling capabilities - allowing agents to create, load, and use custom tools at runtime.
## Overview

| Feature            | Description                                  |
| ------------------ | -------------------------------------------- |
| **Tools Used**     | load_tool, shell, editor                     |
| **Core Concept**   | Meta-Tooling (Dynamic Tool Creation)         |
| **Complexity**     | Advanced                                     |
| **Interaction**    | Command Line Interface                       |
| **Key Technique**  | Runtime Tool Generation                      |


## Tools Used Overview

The meta-tooling agent uses three primary tools to create and manage dynamic tools:

  1. `load_tool`: enables dynamic loading of Python tools at runtime, registering new tools with the agent's registry, enabling hot-reloading of capabilities, and validating tool specifications before loading.
  2. `editor`: allows creation and modification of tool code files with syntax highlighting, making precise string replacements in existing tools, inserting code at specific locations, finding and navigating to specific sections of code, and creating backups with undo capability before modifications.
  3. `shell`: executes shell commands to debug tool creation and execution problems,supports sequential or parallel command execution, and manages working directory context for proper execution.


## How Strands Agent Implements Meta-Tooling

This example showcases how Strands Agent achieves meta-tooling through key mechanisms:

### Key Components

#### 1. Agent is initialized with existing tools to help build new tools

The agent is initialized with the necessary tools for creating new tools:

```python
agent = Agent(
    system_prompt=TOOL_BUILDER_SYSTEM_PROMPT, tools=[load_tool, shell, editor]
)
```

  - `editor`: Tool used to write code directly to a file named `"custom_tool_X.py"`, where "X" is the index of the tool being created.
  - `load_tool`: Tool used to load the tool so the agent can use it.
  - `shell`: Tool used to execute the tool. 

#### 2. Agent System Prompt outlines a strict guideline for naming, structure, and creation of the new tools.

The system prompt guides the agent in proper tool creation. The [TOOL_BUILDER_SYSTEM_PROMPT](https://github.com/strands-agents/docs/blob/main/docs/examples/python/meta_tooling.py#L17) outlines important elements to enable the agent achieve meta-tooling capabilities:

  -  **Tool Naming Convention**: Provides the naming convention to use when building new custom tools.

  -  **Tool Structure**: Enforces a standardized structure for all tools, making it possible for the agent to generate valid tools based on the `TOOL_SPEC` [provided](../../user-guide/concepts/tools/custom-tools.md#module-based-tools-python-only). 


```python
from typing import Any
from strands.types.tool_types import ToolUse, ToolResult

TOOL_SPEC = {
    "name": "tool_name",
    "description": "What the tool does",
    "inputSchema": { 
        "json": {
            "type": "object",
            "properties": {
                "param_name": {
                    "type": "string",
                    "description": "Parameter description"
                }
            },
            "required": ["param_name"]
        }
    }
}

def tool_name(tool_use: ToolUse, **kwargs: Any) -> ToolResult:
    # Tool function docstring
    tool_use_id = tool_use["toolUseId"]
    param_value = tool_use["input"]["param_name"]
    
    # Process inputs
    result = param_value  # Replace with actual processing
    
    return {
        "toolUseId": tool_use_id,
        "status": "success",
        "content": [{"text": f"Result: {result}"}]
    }
```
  -  **Tool Creation vs. Usage** : Provides instructions for agent to distinguish between creating new tools vs. using existing tools.

#### 2. Tool Creation through Natural Language Processing

By analyzing the natural language description, the agent uses a combination of its existing tools and the instructions in the system prompt to create additional tools dynamically. 

- *"Create a tool that counts characters in text"*
- *"Make a tool that converts between different units of measurement"*

---------

### Example Interaction

**Step 1: Making a Custom Tool**

```
> Create a tool that counts characters in text

Creating a Python tool based on this description: "create a tool that counts characters in text". Load the tool after it is created Handle all steps autonomously including naming and file creation.

I'll create a custom tool that counts characters in text. I'll follow these steps:
1. Determine the next available tool index
2. Create the tool with proper structure
3. Write the file
4. Load the tool

First, let's check if there are any existing custom tools to determine the next index:

I'll create a tool named custom_tool_0.py:

Tool created! Here's the code for custom_tool_0.py:

from typing import Any
from strands.types.tool_types import ToolUse, ToolResult

TOOL_SPEC = {
    "name": "custom_tool_0",
    "description": "Counts characters in a text string",
    "inputSchema": {
        "json": {
            "type": "object",
            "properties": {
                "text": {
                    "type": "string",
                    "description": "The text to count characters in"
                }
            },
            "required": ["text"]
        }
    }
}

def custom_tool_0(tool_use: ToolUse, **kwargs: Any) -> ToolResult:
    """
    Count the number of characters in the provided text.
    
    Args:
        tool_use: Contains the input text to analyze
        
    Returns:
        A ToolResult with the character count statistics
    """
    tool_use_id = tool_use["toolUseId"]
    text = tool_use["input"]["text"]
    
    # Count different types of characters
    total_chars = len(text)
    letters = sum(c.isalpha() for c in text)
    digits = sum(c.isdigit() for c in text)
    spaces = sum(c.isspace() for c in text)
    punctuation = sum(not c.isalnum() and not c.isspace() for c in text)
    
    result = f"The text \"{text}\" contains:\n"
    result += f"- Total characters: {total_chars}\n"
    result += f"- Letters: {letters}\n"
    result += f"- Digits: {digits}\n"
    result += f"- Spaces: {spaces}\n"
    result += f"- Punctuation: {punctuation}"
    
    return {
        "toolUseId": tool_use_id,
        "status": "success",
        "content": [{"text": result}]
    }

Now I'll load this tool so it's immediately available for use:

TOOL_CREATED: custom_tool_0.py

The tool custom_tool_0 has been successfully created and loaded. You can now use it to count characters in text.
```

**Step 2: Using the Custom Tool**

```
> Count the characters in "Hello, Strands! How are you today?" using custom_tool_0

I'll use the custom_tool_0 to count characters in your text.

The text "Hello, Strands! How are you today?" contains:
- Total characters: 35
- Letters: 26
- Digits: 0
- Spaces: 5
- Punctuation: 4
```

## Extending the Example

The Meta-Tooling example demonstrates a Strands agent's ability to extend its capabilities by creating new tools on demand to adapt to individual user needs.

Here are some ways to enhance this example:

1. **Tool Version Control**: Implement versioning for created tools to track changes over time

2. **Tool Testing**: Add automated testing for newly created tools to ensure reliability

3. **Tool Improvement**: Create tools to improve existing capabilities of existing tools.
