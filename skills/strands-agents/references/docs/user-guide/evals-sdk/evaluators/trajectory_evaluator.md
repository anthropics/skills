# Trajectory Evaluator

## Overview

The `TrajectoryEvaluator` is an LLM-based evaluator that assesses the sequence of actions or tool calls made by an agent during task execution. It evaluates whether the agent followed an appropriate path to reach its goal, making it ideal for evaluating multi-step reasoning and tool usage patterns. A complete example can be found [here](https://github.com/strands-agents/docs/blob/main/docs/examples/evals-sdk/trajectory_evaluator.py).

## Key Features

- **Action Sequence Evaluation**: Assesses the order and appropriateness of actions taken
- **Tool Usage Analysis**: Evaluates whether correct tools were selected and used
- **Built-in Scoring Tools**: Includes helper tools for exact, in-order, and any-order matching
- **Flexible Rubric System**: Define custom criteria for trajectory evaluation
- **LLM-as-a-Judge**: Uses a language model to perform nuanced trajectory assessments
- **Async Support**: Supports both synchronous and asynchronous evaluation

## When to Use

Use the `TrajectoryEvaluator` when you need to:

- Evaluate the sequence of tool calls or actions taken by an agent
- Verify that agents follow expected workflows or procedures
- Assess whether agents use tools in the correct order
- Compare different agent strategies for solving the same problem
- Ensure agents don't skip critical steps in multi-step processes
- Evaluate reasoning chains and decision-making patterns

## Parameters

### `rubric` (required)
- **Type**: `str`
- **Description**: The evaluation criteria for assessing trajectories. Should specify what constitutes a good action sequence.

### `trajectory_description` (optional)
- **Type**: `dict | None`
- **Default**: `None`
- **Description**: A dictionary describing available trajectory types (e.g., tool descriptions). Can be updated dynamically using `update_trajectory_description()`.

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
- **Description**: Whether to include the input prompt in the evaluation context.

## Built-in Scoring Tools

The `TrajectoryEvaluator` comes with three helper tools that the judge can use:

1. **`exact_match_scorer`**: Checks if actual trajectory exactly matches expected trajectory
2. **`in_order_match_scorer`**: Checks if expected actions appear in order (allows extra actions)
3. **`any_order_match_scorer`**: Checks if all expected actions are present (order doesn't matter)

These tools help the judge make consistent scoring decisions based on trajectory matching.

## Using Extractors to Prevent Overflow

When working with trajectories, it's important to use extractors to efficiently extract tool usage information without overwhelming the evaluation context. The `tools_use_extractor` module provides utility functions for this purpose.

### Available Extractor Functions

#### `extract_agent_tools_used_from_messages(agent_messages)`
Extracts tool usage information from agent message history. Returns a list of tools used with their names, inputs, and results.

```python
from strands_evals.extractors import tools_use_extractor

# Extract tools from agent messages
trajectory = tools_use_extractor.extract_agent_tools_used_from_messages(
    agent.messages
)
# Returns: [{"name": "tool_name", "input": {...}, "tool_result": "..."}, ...]
```

#### `extract_agent_tools_used_from_metrics(agent_result)`
Extracts tool usage metrics from agent execution result, including call counts and timing information.

```python
# Extract tools from agent metrics
tools_metrics = tools_use_extractor.extract_agent_tools_used_from_metrics(
    agent_result
)
# Returns: [{"name": "tool_name", "call_count": 3, "success_count": 3, ...}, ...]
```

#### `extract_tools_description(agent, is_short=True)`
Extracts tool descriptions from the agent's tool registry. Use this to update the trajectory description dynamically.

```python
# Extract tool descriptions
tool_descriptions = tools_use_extractor.extract_tools_description(
    agent, 
    is_short=True  # Returns only descriptions, not full config
)
# Returns: {"tool_name": "tool description", ...}

# Update evaluator with tool descriptions
evaluator.update_trajectory_description(tool_descriptions)
```

## Basic Usage

```python
from strands import Agent, tool
from strands_evals import Case, Experiment
from strands_evals.evaluators import TrajectoryEvaluator
from strands_evals.extractors import tools_use_extractor
from strands_evals.types import TaskOutput

# Define tools
@tool
def search_database(query: str) -> str:
    """Search the database for information."""
    return f"Results for: {query}"

@tool
def format_results(data: str) -> str:
    """Format search results for display."""
    return f"Formatted: {data}"

# Define task function
def get_response(case: Case) -> dict:
    agent = Agent(
        tools=[search_database, format_results],
        system_prompt="Search and format results.",
        callback_handler=None
    )
    response = agent(case.input)
    
    # Use extractor to get trajectory efficiently
    trajectory = tools_use_extractor.extract_agent_tools_used_from_messages(
        agent.messages
    )
    
    # Update evaluator with tool descriptions to prevent overflow
    evaluator.update_trajectory_description(
        tools_use_extractor.extract_tools_description(agent)
    )
    
    return TaskOutput(
        output=str(response),
        trajectory=trajectory
    )

# Create test cases with expected trajectories
test_cases = [
    Case[str, str](
        name="search-and-format",
        input="Find information about Python",
        expected_trajectory=["search_database", "format_results"],
        metadata={"category": "search"}
    ),
]

# Create evaluator
evaluator = TrajectoryEvaluator(
    rubric="""
    The trajectory should follow the correct sequence:
    1. Search the database first
    2. Format the results second
    
    Score 1.0 if the sequence is correct.
    Score 0.5 if tools are used but in wrong order.
    Score 0.0 if wrong tools are used or steps are missing.
    """,
    include_inputs=True
)

# Run evaluation
experiment = Experiment[str, str](cases=test_cases, evaluators=[evaluator])
reports = experiment.run_evaluations(get_response)
reports[0].run_display()
```

## Preventing Context Overflow

When evaluating trajectories with many tool calls or complex tool configurations, use extractors to keep the evaluation context manageable:

```python
def task_with_many_tools(case: Case) -> dict:
    agent = Agent(
        tools=[tool1, tool2, tool3, tool4, tool5],  # Many tools
        callback_handler=None
    )
    response = agent(case.input)
    
    # Extract short descriptions only (prevents overflow)
    tool_descriptions = tools_use_extractor.extract_tools_description(
        agent, 
        is_short=True  # Only descriptions, not full config
    )
    evaluator.update_trajectory_description(tool_descriptions)
    
    return TaskOutput(output=str(response), trajectory=trajectory=tools_use_extractor.extract_agent_tools_used_from_messages(agent.messages))
```

## Evaluation Output

The `TrajectoryEvaluator` returns `EvaluationOutput` objects with:

- **score**: Float between 0.0 and 1.0 representing trajectory quality
- **test_pass**: Boolean indicating if the trajectory passed evaluation
- **reason**: String containing the judge's reasoning
- **label**: Optional label categorizing the result

## Best Practices

1. **Use Extractors**: Always use `tools_use_extractor` functions to efficiently extract trajectory information
2. **Update Descriptions Dynamically**: Call `update_trajectory_description()` with extracted tool descriptions
3. **Keep Trajectories Concise**: Extract only necessary information (e.g., tool names) to prevent context overflow
4. **Define Clear Expected Trajectories**: Specify exact sequences of expected actions
5. **Choose Appropriate Matching**: Select between exact, in-order, or any-order matching based on your needs

## Common Patterns

### Pattern 1: Workflow Validation
```python
evaluator = TrajectoryEvaluator(
    rubric="""
    Required workflow:
    1. Authenticate user
    2. Validate input
    3. Process request
    4. Log action
    
    Score 1.0 if all steps present in order.
    Score 0.0 if any step is missing.
    """
)
```

### Pattern 2: Efficiency Evaluation
```python
evaluator = TrajectoryEvaluator(
    rubric="""
    Evaluate efficiency:
    - Minimum necessary steps: Score 1.0
    - Some redundant steps: Score 0.7
    - Many redundant steps: Score 0.4
    - Inefficient approach: Score 0.0
    """
)
```

### Pattern 3: Using Metrics for Analysis
```python
def task_with_metrics(case: Case) -> dict:
    agent = Agent(tools=[...], callback_handler=None)
    response = agent(case.input)
    
    # Get both trajectory and metrics
    trajectory = tools_use_extractor.extract_agent_tools_used_from_messages(agent.messages)
    metrics = tools_use_extractor.extract_agent_tools_used_from_metrics(response)
    
    # Use metrics for additional analysis
    print(f"Total tool calls: {sum(m['call_count'] for m in metrics)}")
    
    return TaskOutput(output=str(response), trajectory=trajectory)
```

## Related Evaluators

- [**OutputEvaluator**](output_evaluator.md): Evaluates the quality of final outputs
- [**ToolParameterAccuracyEvaluator**](tool_parameter_evaluator.md): Evaluates if tool parameters are correct
- [**ToolSelectionAccuracyEvaluator**](tool_selection_evaluator.md): Evaluates if correct tools were selected
- [**GoalSuccessRateEvaluator**](goal_success_rate_evaluator.md): Evaluates if overall goals were achieved
