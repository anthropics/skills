# Goal Success Rate Evaluator

## Overview

The `GoalSuccessRateEvaluator` evaluates whether all user goals were successfully achieved in a conversation. It provides a holistic assessment of whether the agent accomplished what the user set out to do, considering the entire conversation session. A complete example can be found [here](https://github.com/strands-agents/docs/blob/main/docs/examples/evals-sdk/goal_success_rate_evaluator.py).

## Key Features

- **Session-Level Evaluation**: Evaluates the entire conversation session
- **Goal-Oriented Assessment**: Focuses on whether user objectives were met
- **Binary Scoring**: Simple Yes/No evaluation for clear success/failure determination
- **Structured Reasoning**: Provides step-by-step reasoning for the evaluation
- **Async Support**: Supports both synchronous and asynchronous evaluation
- **Holistic View**: Considers all interactions in the session

## When to Use

Use the `GoalSuccessRateEvaluator` when you need to:

- Measure overall task completion success
- Evaluate if user objectives were fully achieved
- Assess end-to-end conversation effectiveness
- Track success rates across different scenarios
- Identify patterns in successful vs. unsuccessful interactions
- Optimize agents for goal achievement

## Evaluation Level

This evaluator operates at the **SESSION_LEVEL**, meaning it evaluates the entire conversation session as a whole, not individual turns or tool calls.

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

- **Yes (1.0)**: All user goals were successfully achieved
- **No (0.0)**: User goals were not fully achieved

A session passes the evaluation only if the score is 1.0 (all goals achieved).

## Basic Usage

!!! warning "Required: Session ID Trace Attributes"
    When using `StrandsInMemorySessionMapper`, you **must** include session ID trace attributes in your agent configuration. This prevents spans from different test cases from being mixed together in the memory exporter.

```python
from strands import Agent
from strands_evals import Case, Experiment
from strands_evals.evaluators import GoalSuccessRateEvaluator
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
        name="math-1",
        input="What is 25 * 4?",
        metadata={"category": "math", "goal": "calculate_result"}
    ),
    Case[str, str](
        name="math-2",
        input="Calculate the square root of 144",
        metadata={"category": "math", "goal": "calculate_result"}
    ),
]

# Create evaluator
evaluator = GoalSuccessRateEvaluator()

# Run evaluation
experiment = Experiment[str, str](cases=test_cases, evaluators=[evaluator])
reports = experiment.run_evaluations(user_task_function)
reports[0].run_display()
```

## Evaluation Output

The `GoalSuccessRateEvaluator` returns `EvaluationOutput` objects with:

- **score**: `1.0` (Yes) or `0.0` (No)
- **test_pass**: `True` if score >= 1.0, `False` otherwise
- **reason**: Step-by-step reasoning explaining the evaluation
- **label**: "Yes" or "No"

## What Gets Evaluated

The evaluator examines:

1. **Available Tools**: Tools that were available to the agent
2. **Conversation Record**: Complete history of all messages and tool executions
3. **User Goals**: Implicit or explicit goals from the user's queries
4. **Final Outcome**: Whether the conversation achieved the user's objectives

The judge determines if the agent successfully helped the user accomplish their goals by the end of the session.

## Best Practices

1. **Use with Proper Telemetry Setup**: The evaluator requires trajectory information captured via OpenTelemetry
2. **Define Clear Goals**: Ensure test cases have clear, measurable objectives
3. **Capture Complete Sessions**: Include all conversation turns in the trajectory
4. **Test Various Complexity Levels**: Include simple and complex goal scenarios
5. **Combine with Other Evaluators**: Use alongside helpfulness and trajectory evaluators

## Common Patterns

### Pattern 1: Task Completion
Evaluate if specific tasks were completed successfully.

### Pattern 2: Multi-Step Goals
Assess achievement of goals requiring multiple steps.

### Pattern 3: Information Retrieval
Determine if users obtained the information they needed.

## Example Scenarios

### Scenario 1: Successful Goal Achievement
```
User: "I need to book a flight from NYC to LA for next Monday"
Agent: [Searches flights, shows options, books selected flight]
Final: "Your flight is booked! Confirmation number: ABC123"
Evaluation: Yes (1.0) - Goal fully achieved
```

### Scenario 2: Partial Achievement
```
User: "I need to book a flight from NYC to LA for next Monday"
Agent: [Searches flights, shows options]
Final: "Here are available flights. Would you like me to book one?"
Evaluation: No (0.0) - Goal not completed (booking not finalized)
```

### Scenario 3: Failed Goal
```
User: "I need to book a flight from NYC to LA for next Monday"
Agent: "I can help with general travel information."
Evaluation: No (0.0) - Goal not achieved
```

### Scenario 4: Complex Multi-Goal Success
```
User: "Find the cheapest flight to Paris, book it, and send confirmation to my email"
Agent: [Searches flights, compares prices, books cheapest option, sends email]
Final: "Booked the €450 flight and sent confirmation to your email"
Evaluation: Yes (1.0) - All goals achieved
```

## Common Issues and Solutions

### Issue 1: No Evaluation Returned
**Problem**: Evaluator returns empty results.
**Solution**: Ensure trajectory contains a complete session with at least one agent invocation span.

### Issue 2: Ambiguous Goals
**Problem**: Unclear what constitutes "success" for a given query.
**Solution**: Provide clearer test case descriptions or expected outcomes in metadata.

### Issue 3: Partial Success Scoring
**Problem**: Agent partially achieves goals but evaluator marks as failure.
**Solution**: This is by design - the evaluator requires full goal achievement. Consider using HelpfulnessEvaluator for partial success assessment.

## Differences from Other Evaluators

- **vs. HelpfulnessEvaluator**: Goal success is binary (achieved/not achieved), helpfulness is graduated
- **vs. OutputEvaluator**: Goal success evaluates overall achievement, output evaluates response quality
- **vs. TrajectoryEvaluator**: Goal success evaluates outcome, trajectory evaluates the path taken

## Use Cases

### Use Case 1: Customer Service
Evaluate if customer issues were fully resolved.

### Use Case 2: Task Automation
Measure success rate of automated task completion.

### Use Case 3: Information Retrieval
Assess if users obtained all needed information.

### Use Case 4: Multi-Step Workflows
Evaluate completion of complex, multi-step processes.

## Related Evaluators

- [**HelpfulnessEvaluator**](helpfulness_evaluator.md): Evaluates helpfulness of individual responses
- [**TrajectoryEvaluator**](trajectory_evaluator.md): Evaluates the sequence of actions taken
- [**OutputEvaluator**](output_evaluator.md): Evaluates overall output quality with custom criteria
- [**FaithfulnessEvaluator**](faithfulness_evaluator.md): Evaluates if responses are grounded in context
