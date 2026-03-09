# Helpfulness Evaluator

## Overview

The `HelpfulnessEvaluator` evaluates the helpfulness of agent responses from the user's perspective. It assesses whether responses effectively address user needs, provide useful information, and contribute positively to achieving the user's goals. A complete example can be found [here](https://github.com/strands-agents/docs/blob/main/docs/examples/evals-sdk/helpfulness_evaluator.py).

## Key Features

- **Trace-Level Evaluation**: Evaluates the most recent turn in the conversation
- **User-Centric Assessment**: Focuses on helpfulness from the user's point of view
- **Seven-Level Scoring**: Detailed scale from "Not helpful at all" to "Above and beyond"
- **Structured Reasoning**: Provides step-by-step reasoning for each evaluation
- **Async Support**: Supports both synchronous and asynchronous evaluation
- **Context-Aware**: Considers conversation history when evaluating helpfulness

## When to Use

Use the `HelpfulnessEvaluator` when you need to:

- Assess user satisfaction with agent responses
- Evaluate if responses effectively address user queries
- Measure the practical value of agent outputs
- Compare helpfulness across different agent configurations
- Identify areas where agents could be more helpful
- Optimize agent behavior for user experience

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

### `include_inputs` (optional)
- **Type**: `bool`
- **Default**: `True`
- **Description**: Whether to include the input prompt in the evaluation context.

## Scoring System

The evaluator uses a seven-level categorical scoring system:

- **Not helpful at all (0.0)**: Response is completely unhelpful or counterproductive
- **Very unhelpful (0.167)**: Response provides minimal or misleading value
- **Somewhat unhelpful (0.333)**: Response has some issues that limit helpfulness
- **Neutral/Mixed (0.5)**: Response is adequate but not particularly helpful
- **Somewhat helpful (0.667)**: Response is useful and addresses the query
- **Very helpful (0.833)**: Response is highly useful and well-crafted
- **Above and beyond (1.0)**: Response exceeds expectations with exceptional value

A response passes the evaluation if the score is >= 0.5.

## Basic Usage

!!! warning "Required: Session ID Trace Attributes"
    When using `StrandsInMemorySessionMapper`, you **must** include session ID trace attributes in your agent configuration. This prevents spans from different test cases from being mixed together in the memory exporter.

```python
from strands import Agent
from strands_evals import Case, Experiment
from strands_evals.evaluators import HelpfulnessEvaluator
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
evaluator = HelpfulnessEvaluator()

# Run evaluation
experiment = Experiment[str, str](cases=test_cases, evaluators=[evaluator])
reports = experiment.run_evaluations(user_task_function)
reports[0].run_display()
```

## Evaluation Output

The `HelpfulnessEvaluator` returns `EvaluationOutput` objects with:

- **score**: Float between 0.0 and 1.0 (0.0, 0.167, 0.333, 0.5, 0.667, 0.833, or 1.0)
- **test_pass**: `True` if score >= 0.5, `False` otherwise
- **reason**: Step-by-step reasoning explaining the evaluation
- **label**: One of the categorical labels (e.g., "Very helpful", "Somewhat helpful")

## What Gets Evaluated

The evaluator examines:

1. **Previous Turns**: Earlier conversation context (if available)
2. **Target Turn**: The user's query and the agent's response
3. **Helpfulness Factors**:
   - Relevance to the user's query
   - Completeness of the answer
   - Clarity and understandability
   - Actionability of the information
   - Tone and professionalism

The judge determines how helpful the response is from the user's perspective.

## Best Practices

1. **Use with Proper Telemetry Setup**: The evaluator requires trajectory information captured via OpenTelemetry
2. **Provide User Context**: Include conversation history for context-aware evaluation
3. **Test Diverse Scenarios**: Include various query types and complexity levels
4. **Consider Domain-Specific Needs**: Adjust expectations based on your use case
5. **Combine with Other Evaluators**: Use alongside accuracy and faithfulness evaluators

## Common Patterns

### Pattern 1: Customer Service Evaluation
Assess helpfulness of customer support responses.

### Pattern 2: Information Retrieval
Evaluate if search or query responses meet user needs.

### Pattern 3: Task Assistance
Measure how well agents help users complete tasks.

## Example Scenarios

### Scenario 1: Very Helpful Response
```
User: "How do I reset my password?"
Agent: "To reset your password: 1) Click 'Forgot Password' on the login page, 2) Enter your email, 3) Check your inbox for a reset link, 4) Follow the link and create a new password. The link expires in 24 hours."
Evaluation: Very helpful (0.833) - Clear, complete, actionable steps
```

### Scenario 2: Somewhat Helpful Response
```
User: "How do I reset my password?"
Agent: "You can reset your password through the login page."
Evaluation: Somewhat helpful (0.667) - Correct but lacks detail
```

### Scenario 3: Not Helpful Response
```
User: "How do I reset my password?"
Agent: "Passwords are important for security."
Evaluation: Not helpful at all (0.0) - Doesn't address the question
```

### Scenario 4: Above and Beyond Response
```
User: "How do I reset my password?"
Agent: "I'll help you reset your password. Here are the steps: 1) Click 'Forgot Password' on the login page, 2) Enter your email, 3) Check your inbox for a reset link (check spam if not found), 4) Follow the link and create a new password. Tips: Use a strong password with 12+ characters, mix of letters/numbers/symbols. If you don't receive the email within 5 minutes, let me know and I can help troubleshoot."
Evaluation: Above and beyond (1.0) - Comprehensive, proactive, anticipates issues
```

## Common Issues and Solutions

### Issue 1: No Evaluation Returned
**Problem**: Evaluator returns empty results.
**Solution**: Ensure trajectory contains at least one agent invocation span.

### Issue 2: Inconsistent Scoring
**Problem**: Similar responses get different scores.
**Solution**: This is expected due to LLM non-determinism. Run multiple evaluations and aggregate.

### Issue 3: Context Not Considered
**Problem**: Evaluation doesn't account for conversation history.
**Solution**: Verify telemetry captures full conversation and `include_inputs=True`.

## Differences from Other Evaluators

- **vs. FaithfulnessEvaluator**: Helpfulness focuses on user value, faithfulness on factual grounding
- **vs. OutputEvaluator**: Helpfulness is user-centric, output evaluator uses custom rubrics
- **vs. GoalSuccessRateEvaluator**: Helpfulness evaluates individual turns, goal success evaluates overall achievement

## Related Evaluators

- [**FaithfulnessEvaluator**](faithfulness_evaluator.md): Evaluates if responses are grounded in context
- [**OutputEvaluator**](output_evaluator.md): Evaluates overall output quality with custom criteria
- [**GoalSuccessRateEvaluator**](goal_success_rate_evaluator.md): Evaluates if overall user goals were achieved
- [**TrajectoryEvaluator**](trajectory_evaluator.md): Evaluates the sequence of actions taken
