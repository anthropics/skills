# Tool Selection Accuracy Evaluator

## Overview

The `ToolSelectionAccuracyEvaluator` evaluates whether tool calls are justified at specific points in the conversation. It assesses if the agent selected the right tool at the right time based on the conversation context and available tools. A complete example can be found [here](https://github.com/strands-agents/docs/blob/main/docs/examples/evals-sdk/tool_selection_accuracy_evaluator.py).

## Key Features

- **Tool-Level Evaluation**: Evaluates each tool call independently
- **Contextual Justification**: Checks if tool selection is appropriate given the conversation state
- **Binary Scoring**: Simple Yes/No evaluation for clear pass/fail criteria
- **Structured Reasoning**: Provides step-by-step reasoning for each evaluation
- **Async Support**: Supports both synchronous and asynchronous evaluation
- **Multiple Evaluations**: Returns one evaluation result per tool call

## When to Use

Use the `ToolSelectionAccuracyEvaluator` when you need to:

- Verify that agents select appropriate tools for given tasks
- Detect unnecessary or premature tool calls
- Ensure agents don't skip necessary tool calls
- Validate tool selection logic in multi-tool scenarios
- Debug issues with incorrect tool selection
- Optimize tool selection strategies

## Evaluation Level

This evaluator operates at the **TOOL_LEVEL**, meaning it evaluates each individual tool call in the trajectory separately. If an agent makes 3 tool calls, you'll receive 3 evaluation results.

## Parameters

### `model` (optional)
- **Type**: `Union[Model, str, None]`
- **Default**: `None` (uses default Bedrock model)
- **Description**: The model to use as the judge. Can be a model ID string or a Model instance.

### `system_prompt` (optional)
- **Type**: `str | None`
- **Default**: `None` (uses built-in template)
- **Description**: Custom system prompt to guide the judge model's behavior.

## Scoring System

The evaluator uses a binary scoring system:

- **Yes (1.0)**: Tool selection is justified and appropriate
- **No (0.0)**: Tool selection is unjustified, premature, or inappropriate

## Basic Usage

!!! warning "Required: Session ID Trace Attributes"
    When using `StrandsInMemorySessionMapper`, you **must** include session ID trace attributes in your agent configuration. This prevents spans from different test cases from being mixed together in the memory exporter.

```python
from strands import Agent, tool
from strands_evals import Case, Experiment
from strands_evals.evaluators import ToolSelectionAccuracyEvaluator
from strands_evals.mappers import StrandsInMemorySessionMapper
from strands_evals.telemetry import StrandsEvalsTelemetry

# Setup telemetry
telemetry = StrandsEvalsTelemetry().setup_in_memory_exporter()
memory_exporter = telemetry.in_memory_exporter

@tool
def search_database(query: str) -> str:
    """Search the database for information."""
    return f"Results for: {query}"

@tool
def send_email(to: str, subject: str, body: str) -> str:
    """Send an email to a recipient."""
    return f"Email sent to {to}"

# Define task function
def user_task_function(case: Case) -> dict:
    memory_exporter.clear()
    
    agent = Agent(
        trace_attributes={
            "gen_ai.conversation.id": case.session_id,
            "session.id": case.session_id
        },
        tools=[search_database, send_email],
        callback_handler=None
    )
    agent_response = agent(case.input)
    
    # Map spans to session
    finished_spans = memory_exporter.get_finished_spans()
    mapper = StrandsInMemorySessionMapper()
    session = mapper.map_to_session(finished_spans, session_id=case.session_id)
    
    return {"output": str(agent_response), "trajectory": session}

# Create test cases
test_cases = [
    Case[str, str](
        name="search-query",
        input="Find information about Python programming",
        metadata={"category": "search", "expected_tool": "search_database"}
    ),
    Case[str, str](
        name="email-request",
        input="Send an email to john@example.com about the meeting",
        metadata={"category": "email", "expected_tool": "send_email"}
    ),
]

# Create evaluator
evaluator = ToolSelectionAccuracyEvaluator()

# Run evaluation
experiment = Experiment[str, str](cases=test_cases, evaluators=[evaluator])
reports = experiment.run_evaluations(user_task_function)
reports[0].run_display()
```

## Evaluation Output

The `ToolSelectionAccuracyEvaluator` returns a list of `EvaluationOutput` objects (one per tool call) with:

- **score**: `1.0` (Yes) or `0.0` (No)
- **test_pass**: `True` if score is 1.0, `False` otherwise
- **reason**: Step-by-step reasoning explaining the evaluation
- **label**: "Yes" or "No"

## What Gets Evaluated

The evaluator examines:

1. **Available Tools**: All tools that were available to the agent
2. **Previous Conversation History**: All prior messages and tool executions
3. **Target Tool Call**: The specific tool call being evaluated, including:
   - Tool name
   - Tool arguments
   - Timing of the call

The judge determines if the tool selection was appropriate given the context and whether the timing was correct.

## Best Practices

1. **Use with Proper Telemetry Setup**: The evaluator requires trajectory information captured via OpenTelemetry
2. **Provide Clear Tool Descriptions**: Ensure tools have clear, descriptive names and documentation
3. **Test Multiple Scenarios**: Include cases where tool selection is obvious and cases where it's ambiguous
4. **Combine with Parameter Evaluator**: Use alongside `ToolParameterAccuracyEvaluator` for complete tool usage assessment
5. **Review Reasoning**: Always review the reasoning to understand selection decisions

## Common Patterns

### Pattern 1: Validating Tool Choice
Ensure agents select the most appropriate tool from multiple options.

### Pattern 2: Detecting Premature Tool Calls
Identify cases where agents call tools before gathering necessary information.

### Pattern 3: Identifying Missing Tool Calls
Detect when agents should have used a tool but didn't.

## Common Issues and Solutions

### Issue 1: No Evaluations Returned
**Problem**: Evaluator returns empty list or no results.
**Solution**: Ensure trajectory is properly captured and includes tool calls.

### Issue 2: Ambiguous Tool Selection
**Problem**: Multiple tools could be appropriate for a given task.
**Solution**: Refine tool descriptions and system prompts to clarify tool purposes.

### Issue 3: Context-Dependent Selection
**Problem**: Tool selection appropriateness depends on conversation history.
**Solution**: Ensure full conversation history is captured in traces.

## Related Evaluators

- [**ToolParameterAccuracyEvaluator**](tool_parameter_evaluator.md): Evaluates if tool parameters are correct
- [**TrajectoryEvaluator**](trajectory_evaluator.md): Evaluates the overall sequence of tool calls
- [**OutputEvaluator**](output_evaluator.md): Evaluates the quality of final outputs
- [**GoalSuccessRateEvaluator**](goal_success_rate_evaluator.md): Evaluates if overall goals were achieved
