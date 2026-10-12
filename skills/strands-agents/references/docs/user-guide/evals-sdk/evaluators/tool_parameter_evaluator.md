# Tool Parameter Accuracy Evaluator

## Overview

The `ToolParameterAccuracyEvaluator` is a specialized evaluator that assesses whether tool call parameters faithfully use information from the preceding conversation context. It evaluates each tool call individually to ensure parameters are grounded in available information rather than hallucinated or incorrectly inferred. A complete example can be found [here](https://github.com/strands-agents/docs/blob/main/docs/examples/evals-sdk/tool_parameter_accuracy_evaluator.py).

## Key Features

- **Tool-Level Evaluation**: Evaluates each tool call independently
- **Context Faithfulness**: Checks if parameters are derived from conversation history
- **Binary Scoring**: Simple Yes/No evaluation for clear pass/fail criteria
- **Structured Reasoning**: Provides step-by-step reasoning for each evaluation
- **Async Support**: Supports both synchronous and asynchronous evaluation
- **Multiple Evaluations**: Returns one evaluation result per tool call

## When to Use

Use the `ToolParameterAccuracyEvaluator` when you need to:

- Verify that tool parameters are based on actual conversation context
- Detect hallucinated or fabricated parameter values
- Ensure agents don't make assumptions beyond available information
- Validate that agents correctly extract information for tool calls
- Debug issues with incorrect tool parameter usage
- Ensure data integrity in tool-based workflows

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

- **Yes (1.0)**: Parameters faithfully use information from the context
- **No (0.0)**: Parameters contain hallucinated, fabricated, or incorrectly inferred values

## Basic Usage

!!! warning "Required: Session ID Trace Attributes"
    When using `StrandsInMemorySessionMapper`, you **must** include session ID trace attributes in your agent configuration. This prevents spans from different test cases from being mixed together in the memory exporter.

```python
from strands import Agent
from strands_tools import calculator
from strands_evals import Case, Experiment
from strands_evals.evaluators import ToolParameterAccuracyEvaluator
from strands_evals.mappers import StrandsInMemorySessionMapper
from strands_evals.telemetry import StrandsEvalsTelemetry

# Setup telemetry
telemetry = StrandsEvalsTelemetry().setup_in_memory_exporter()
memory_exporter = telemetry.in_memory_exporter

# Define task function
def user_task_function(case: Case) -> dict:
    memory_exporter.clear()
    
    agent = Agent(
        trace_attributes={
            "gen_ai.conversation.id": case.session_id,
            "session.id": case.session_id
        },
        tools=[calculator],
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
        name="simple-calculation",
        input="Calculate the square root of 144",
        metadata={"category": "math", "difficulty": "easy"}
    ),
]

# Create evaluator
evaluator = ToolParameterAccuracyEvaluator()

# Run evaluation
experiment = Experiment[str, str](cases=test_cases, evaluators=[evaluator])
reports = experiment.run_evaluations(user_task_function)
reports[0].run_display()
```

## Evaluation Output

The `ToolParameterAccuracyEvaluator` returns a list of `EvaluationOutput` objects (one per tool call) with:

- **score**: `1.0` (Yes) or `0.0` (No)
- **test_pass**: `True` if score is 1.0, `False` otherwise
- **reason**: Step-by-step reasoning explaining the evaluation
- **label**: "Yes" or "No"

## What Gets Evaluated

The evaluator examines:

1. **Available Tools**: The tools that were available to the agent
2. **Previous Conversation History**: All prior messages and tool executions
3. **Target Tool Call**: The specific tool call being evaluated, including:
   - Tool name
   - All parameter values

The judge determines if each parameter value can be traced back to information in the conversation history.

## Best Practices

1. **Use with Proper Telemetry Setup**: The evaluator requires trajectory information captured via OpenTelemetry
2. **Test Edge Cases**: Include test cases that challenge parameter accuracy (missing info, ambiguous info, etc.)
3. **Combine with Other Evaluators**: Use alongside tool selection and output evaluators for comprehensive assessment
4. **Review Reasoning**: Always review the reasoning provided in evaluation results
5. **Use Appropriate Models**: Consider using stronger models for evaluation

## Common Issues and Solutions

### Issue 1: No Evaluations Returned
**Problem**: Evaluator returns empty list or no results.
**Solution**: Ensure trajectory is properly captured and includes tool calls.

### Issue 2: False Negatives
**Problem**: Evaluator marks valid parameters as inaccurate.
**Solution**: Ensure conversation history is complete and context is clear.

### Issue 3: Inconsistent Results
**Problem**: Same test case produces different evaluation results.
**Solution**: This is expected due to LLM non-determinism. Run multiple times and aggregate.

## Related Evaluators

- [**ToolSelectionAccuracyEvaluator**](tool_selection_evaluator.md): Evaluates if correct tools were selected
- [**TrajectoryEvaluator**](trajectory_evaluator.md): Evaluates the overall sequence of tool calls
- [**FaithfulnessEvaluator**](faithfulness_evaluator.md): Evaluates if responses are grounded in context
- [**OutputEvaluator**](output_evaluator.md): Evaluates the quality of final outputs
