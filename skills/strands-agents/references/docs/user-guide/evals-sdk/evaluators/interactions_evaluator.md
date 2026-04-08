# Interactions Evaluator

## Overview

The `InteractionsEvaluator` is designed for evaluating interactions between agents or components in multi-agent systems or complex workflows. It assesses each interaction step-by-step, considering dependencies, message flow, and the overall sequence of interactions.

## Key Features

- **Interaction-Level Evaluation**: Evaluates each interaction in a sequence
- **Multi-Agent Support**: Designed for evaluating multi-agent systems and workflows
- **Node-Specific Rubrics**: Supports different evaluation criteria for different nodes/agents
- **Sequential Context**: Maintains context across interactions using sliding window
- **Dependency Tracking**: Considers dependencies between interactions
- **Async Support**: Supports both synchronous and asynchronous evaluation

## When to Use

Use the `InteractionsEvaluator` when you need to:

- Evaluate multi-agent system interactions
- Assess workflow execution across multiple components
- Validate message passing between agents
- Ensure proper dependency handling in complex systems
- Track interaction quality in agent orchestration
- Debug multi-agent coordination issues

## Parameters

### `rubric` (required)
- **Type**: `str | dict[str, str]`
- **Description**: Evaluation criteria. Can be a single string for all nodes or a dictionary mapping node names to specific rubrics.

### `interaction_description` (optional)
- **Type**: `dict | None`
- **Default**: `None`
- **Description**: A dictionary describing available interactions. Can be updated dynamically using `update_interaction_description()`.

### `model` (optional)
- **Type**: `Union[Model, str, None]`
- **Default**: `None` (uses default Bedrock model)
- **Description**: The model to use as the judge. Can be a model ID string or a Model instance.

### `system_prompt` (optional)
- **Type**: `str`
- **Default**: Built-in template
- **Description**: Custom system prompt to guide the judge model's behavior.

### `include_inputs` (optional)
- **Type**: `bool`
- **Default**: `True`
- **Description**: Whether to include inputs in the evaluation context.

## Interaction Structure

Each interaction should contain:

- **node_name**: Name of the agent/component involved
- **dependencies**: List of nodes this interaction depends on
- **messages**: Messages exchanged in this interaction

## Basic Usage

```python
from strands_evals import Case, Experiment
from strands_evals.evaluators import InteractionsEvaluator

# Define task function that returns interactions
def multi_agent_task(case: Case) -> dict:
    # Execute multi-agent workflow
    # ...
    
    # Return interactions
    interactions = [
        {
            "node_name": "planner",
            "dependencies": [],
            "messages": "Created execution plan"
        },
        {
            "node_name": "executor",
            "dependencies": ["planner"],
            "messages": "Executed plan steps"
        },
        {
            "node_name": "validator",
            "dependencies": ["executor"],
            "messages": "Validated results"
        }
    ]
    
    return {
        "output": "Task completed",
        "interactions": interactions
    }

# Create test cases
test_cases = [
    Case[str, str](
        name="workflow-1",
        input="Process data pipeline",
        expected_interactions=[
            {"node_name": "planner", "dependencies": [], "messages": "Plan created"},
            {"node_name": "executor", "dependencies": ["planner"], "messages": "Executed"},
            {"node_name": "validator", "dependencies": ["executor"], "messages": "Validated"}
        ],
        metadata={"category": "workflow"}
    ),
]

# Create evaluator with single rubric for all nodes
evaluator = InteractionsEvaluator(
    rubric="""
    Evaluate the interaction based on:
    1. Correct node execution order
    2. Proper dependency handling
    3. Clear message communication
    
    Score 1.0 if all criteria are met.
    Score 0.5 if some issues exist.
    Score 0.0 if interaction is incorrect.
    """
)

# Or use node-specific rubrics
evaluator = InteractionsEvaluator(
    rubric={
        "planner": "Evaluate if planning is thorough and logical",
        "executor": "Evaluate if execution follows the plan correctly",
        "validator": "Evaluate if validation is comprehensive"
    }
)

# Run evaluation
experiment = Experiment[str, str](cases=test_cases, evaluators=[evaluator])
reports = experiment.run_evaluations(multi_agent_task)
reports[0].run_display()
```

## Evaluation Output

The `InteractionsEvaluator` returns a list of `EvaluationOutput` objects (one per interaction) with:

- **score**: Float between 0.0 and 1.0 for each interaction
- **test_pass**: Boolean indicating if the interaction passed
- **reason**: Step-by-step reasoning for the evaluation
- **label**: Optional label categorizing the result

The final interaction's evaluation includes context from all previous interactions.

## What Gets Evaluated

For each interaction, the evaluator examines:

1. **Current Interaction**: Node name, dependencies, and messages
2. **Expected Sequence**: Overview of the expected interaction sequence
3. **Relevant Expected Interactions**: Window of expected interactions around current position
4. **Previous Evaluations**: Context from earlier interactions (for later interactions)
5. **Final Output**: Overall output (only for the last interaction)

## Best Practices

1. **Define Clear Interaction Structure**: Ensure interactions have consistent node_name, dependencies, and messages
2. **Use Node-Specific Rubrics**: Provide tailored evaluation criteria for different agent types
3. **Track Dependencies**: Clearly specify which nodes depend on others
4. **Update Descriptions**: Use `update_interaction_description()` to provide context about available interactions
5. **Test Sequences**: Include test cases with various interaction patterns

## Common Patterns

### Pattern 1: Linear Workflow
```python
interactions = [
    {"node_name": "input_validator", "dependencies": [], "messages": "Input validated"},
    {"node_name": "processor", "dependencies": ["input_validator"], "messages": "Data processed"},
    {"node_name": "output_formatter", "dependencies": ["processor"], "messages": "Output formatted"}
]
```

### Pattern 2: Parallel Execution
```python
interactions = [
    {"node_name": "coordinator", "dependencies": [], "messages": "Tasks distributed"},
    {"node_name": "worker_1", "dependencies": ["coordinator"], "messages": "Task 1 completed"},
    {"node_name": "worker_2", "dependencies": ["coordinator"], "messages": "Task 2 completed"},
    {"node_name": "aggregator", "dependencies": ["worker_1", "worker_2"], "messages": "Results aggregated"}
]
```

### Pattern 3: Conditional Flow
```python
interactions = [
    {"node_name": "analyzer", "dependencies": [], "messages": "Analysis complete"},
    {"node_name": "decision_maker", "dependencies": ["analyzer"], "messages": "Decision: proceed"},
    {"node_name": "executor", "dependencies": ["decision_maker"], "messages": "Action executed"}
]
```

## Example Scenarios

### Scenario 1: Successful Multi-Agent Workflow
```python
# Task: Research and summarize a topic
interactions = [
    {
        "node_name": "researcher",
        "dependencies": [],
        "messages": "Found 5 relevant sources"
    },
    {
        "node_name": "analyzer",
        "dependencies": ["researcher"],
        "messages": "Extracted key points from sources"
    },
    {
        "node_name": "writer",
        "dependencies": ["analyzer"],
        "messages": "Created comprehensive summary"
    }
]
# Evaluation: Each interaction scored based on quality and dependency adherence
```

### Scenario 2: Failed Dependency
```python
# Task: Process data pipeline
interactions = [
    {
        "node_name": "validator",
        "dependencies": [],
        "messages": "Validation skipped"  # Should depend on data_loader
    },
    {
        "node_name": "processor",
        "dependencies": ["validator"],
        "messages": "Processing failed"
    }
]
# Evaluation: Low scores due to incorrect dependency handling
```

## Common Issues and Solutions

### Issue 1: Missing Interaction Keys
**Problem**: Interactions missing required keys (node_name, dependencies, messages).
**Solution**: Ensure all interactions include all three required fields.

### Issue 2: Incorrect Dependency Specification
**Problem**: Dependencies don't match actual execution order.
**Solution**: Verify dependency lists accurately reflect the workflow.

### Issue 3: Rubric Key Mismatch
**Problem**: Node-specific rubric dictionary missing keys for some nodes.
**Solution**: Ensure rubric dictionary contains entries for all node names, or use a single string rubric.

## Use Cases

### Use Case 1: Multi-Agent Orchestration
Evaluate coordination between multiple specialized agents.

### Use Case 2: Workflow Validation
Assess execution of complex, multi-step workflows.

### Use Case 3: Agent Handoff Quality
Measure quality of information transfer between agents.

### Use Case 4: Dependency Compliance
Verify that agents respect declared dependencies.

## Related Evaluators

- [**TrajectoryEvaluator**](trajectory_evaluator.md): Evaluates tool call sequences (single agent)
- [**GoalSuccessRateEvaluator**](goal_success_rate_evaluator.md): Evaluates overall goal achievement
- [**OutputEvaluator**](output_evaluator.md): Evaluates final output quality
- [**HelpfulnessEvaluator**](helpfulness_evaluator.md): Evaluates individual response helpfulness
