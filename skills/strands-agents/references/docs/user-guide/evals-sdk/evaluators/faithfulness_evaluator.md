# Faithfulness Evaluator

## Overview

The `FaithfulnessEvaluator` evaluates whether agent responses are grounded in the conversation history. It assesses if the agent's statements are faithful to the information available in the preceding context, helping detect hallucinations and unsupported claims. A complete example can be found [here](https://github.com/strands-agents/docs/blob/main/docs/examples/evals-sdk/faithfulness_evaluator.py).

## Key Features

- **Trace-Level Evaluation**: Evaluates the most recent turn in the conversation
- **Context Grounding**: Checks if responses are based on conversation history
- **Categorical Scoring**: Five-level scale from "Not At All" to "Completely Yes"
- **Structured Reasoning**: Provides step-by-step reasoning for each evaluation
- **Async Support**: Supports both synchronous and asynchronous evaluation
- **Hallucination Detection**: Identifies fabricated or unsupported information

## When to Use

Use the `FaithfulnessEvaluator` when you need to:

- Detect hallucinations in agent responses
- Verify that responses are grounded in available context
- Ensure agents don't fabricate information
- Validate that claims are supported by conversation history
- Assess information accuracy in multi-turn conversations
- Debug issues with context adherence

## Evaluation Level

This evaluator operates at the **TRACE_LEVEL**, meaning it evaluates the most recent turn in the conversation (the last agent response and its context).

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

The evaluator uses a five-level categorical scoring system:

- **Not At All (0.0)**: Response contains significant fabrications or unsupported claims
- **Not Generally (0.25)**: Response is mostly unfaithful with some grounded elements
- **Neutral/Mixed (0.5)**: Response has both faithful and unfaithful elements
- **Generally Yes (0.75)**: Response is mostly faithful with minor issues
- **Completely Yes (1.0)**: Response is completely grounded in conversation history

A response passes the evaluation if the score is >= 0.5.

## Basic Usage

!!! warning "Required: Session ID Trace Attributes"
    When using `StrandsInMemorySessionMapper`, you **must** include session ID trace attributes in your agent configuration. This prevents spans from different test cases from being mixed together in the memory exporter.

```python
from strands import Agent
from strands_evals import Case, Experiment
from strands_evals.evaluators import FaithfulnessEvaluator
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
        name="knowledge-1",
        input="What is the capital of France?",
        metadata={"category": "knowledge"}
    ),
    Case[str, str](
        name="knowledge-2",
        input="What color is the ocean?",
        metadata={"category": "knowledge"}
    ),
]

# Create evaluator
evaluator = FaithfulnessEvaluator()

# Run evaluation
experiment = Experiment[str, str](cases=test_cases, evaluators=[evaluator])
reports = experiment.run_evaluations(user_task_function)
reports[0].run_display()
```

## Evaluation Output

The `FaithfulnessEvaluator` returns `EvaluationOutput` objects with:

- **score**: Float between 0.0 and 1.0 (0.0, 0.25, 0.5, 0.75, or 1.0)
- **test_pass**: `True` if score >= 0.5, `False` otherwise
- **reason**: Step-by-step reasoning explaining the evaluation
- **label**: One of the categorical labels (e.g., "Completely Yes", "Neutral/Mixed")

## What Gets Evaluated

The evaluator examines:

1. **Conversation History**: All prior messages and tool executions
2. **Assistant's Response**: The most recent agent response
3. **Context Grounding**: Whether claims in the response are supported by the history

The judge determines if the agent's statements are faithful to the available information or if they contain fabrications, assumptions, or unsupported claims.

## Best Practices

1. **Use with Proper Telemetry Setup**: The evaluator requires trajectory information captured via OpenTelemetry
2. **Provide Complete Context**: Ensure full conversation history is captured in traces
3. **Test with Known Facts**: Include test cases with verifiable information
4. **Monitor Hallucination Patterns**: Track which types of queries lead to unfaithful responses
5. **Combine with Other Evaluators**: Use alongside output quality evaluators for comprehensive assessment

## Common Patterns

### Pattern 1: Detecting Fabrications
Identify when agents make up information not present in the context.

### Pattern 2: Validating Tool Results
Ensure agents accurately represent information from tool calls.

### Pattern 3: Multi-Turn Consistency
Check that agents maintain consistency across conversation turns.

## Example Scenarios

### Scenario 1: Faithful Response
```
User: "What did the search results say about Python?"
Agent: "The search results indicated that Python is a high-level programming language."
Evaluation: Completely Yes (1.0) - Response accurately reflects search results
```

### Scenario 2: Unfaithful Response
```
User: "What did the search results say about Python?"
Agent: "Python was created in 1991 by Guido van Rossum and is the most popular language."
Evaluation: Not Generally (0.25) - Response adds information not in search results
```

### Scenario 3: Mixed Response
```
User: "What did the search results say about Python?"
Agent: "The search results showed Python is a programming language. It's also the fastest language."
Evaluation: Neutral/Mixed (0.5) - First part faithful, second part unsupported
```

## Common Issues and Solutions

### Issue 1: No Evaluation Returned
**Problem**: Evaluator returns empty results.
**Solution**: Ensure trajectory contains at least one agent invocation span.

### Issue 2: Overly Strict Evaluation
**Problem**: Evaluator marks reasonable inferences as unfaithful.
**Solution**: Review system prompt and consider if agent is expected to make reasonable inferences.

### Issue 3: Context Not Captured
**Problem**: Evaluation doesn't consider full conversation history.
**Solution**: Verify telemetry setup captures all messages and tool executions.

## Related Evaluators

- [**HelpfulnessEvaluator**](helpfulness_evaluator.md): Evaluates helpfulness from user perspective
- [**OutputEvaluator**](output_evaluator.md): Evaluates overall output quality
- [**ToolParameterAccuracyEvaluator**](tool_parameter_evaluator.md): Evaluates if tool parameters are grounded in context
- [**GoalSuccessRateEvaluator**](goal_success_rate_evaluator.md): Evaluates if overall goals were achieved
