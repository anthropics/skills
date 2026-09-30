# Output Evaluator

## Overview

The `OutputEvaluator` is an LLM-based evaluator that assesses the quality of agent outputs against custom criteria. It uses a judge LLM to evaluate responses based on a user-defined rubric, making it ideal for evaluating subjective qualities like safety, relevance, accuracy, and completeness. A complete example can be found [here](https://github.com/strands-agents/docs/blob/main/docs/examples/evals-sdk/output_evaluator.py).

## Key Features

- **Flexible Rubric System**: Define custom evaluation criteria tailored to your use case
- **LLM-as-a-Judge**: Leverages a language model to perform nuanced evaluations
- **Structured Output**: Returns standardized evaluation results with scores and reasoning
- **Async Support**: Supports both synchronous and asynchronous evaluation
- **Input Context**: Optionally includes input prompts in the evaluation for context-aware scoring

## When to Use

Use the `OutputEvaluator` when you need to:

- Evaluate subjective qualities of agent responses (e.g., helpfulness, safety, tone)
- Assess whether outputs meet specific business requirements
- Check for policy compliance or content guidelines
- Compare different agent configurations or prompts
- Evaluate responses where ground truth is not available or difficult to define

## Parameters

### `rubric` (required)
- **Type**: `str`
- **Description**: The evaluation criteria that defines what constitutes a good response. Should include scoring guidelines (e.g., "Score 1 if..., 0.5 if..., 0 if...").

### `model` (optional)
- **Type**: `Union[Model, str, None]`
- **Default**: `None` (uses default Bedrock model)
- **Description**: The model to use as the judge. Can be a model ID string or a Model instance.

### `system_prompt` (optional)
- **Type**: `str`
- **Default**: Built-in template
- **Description**: Custom system prompt to guide the judge model's behavior. If not provided, uses a default template optimized for evaluation.

### `include_inputs` (optional)
- **Type**: `bool`
- **Default**: `True`
- **Description**: Whether to include the input prompt in the evaluation context. Set to `False` if you only want to evaluate the output in isolation.

## Basic Usage

```python
from strands import Agent
from strands_evals import Case, Experiment
from strands_evals.evaluators import OutputEvaluator

# Define your task function
def get_response(case: Case) -> str:
    agent = Agent(
        system_prompt="You are a helpful assistant.",
        callback_handler=None
    )
    response = agent(case.input)
    return str(response)

# Create test cases
test_cases = [
    Case[str, str](
        name="greeting",
        input="Hello, how are you?",
        expected_output="A friendly greeting response",
        metadata={"category": "conversation"}
    ),
]

# Create evaluator with custom rubric
evaluator = OutputEvaluator(
    rubric="""
    Evaluate the response based on:
    1. Accuracy - Is the information correct?
    2. Completeness - Does it fully answer the question?
    3. Clarity - Is it easy to understand?
    
    Score 1.0 if all criteria are met excellently.
    Score 0.5 if some criteria are partially met.
    Score 0.0 if the response is inadequate.
    """,
    include_inputs=True
)

# Create and run experiment
experiment = Experiment[str, str](cases=test_cases, evaluators=[evaluator])
reports = experiment.run_evaluations(get_response)
reports[0].run_display()
```

## Evaluation Output

The `OutputEvaluator` returns `EvaluationOutput` objects with:

- **score**: Float between 0.0 and 1.0 representing the evaluation score
- **test_pass**: Boolean indicating if the test passed (based on score threshold)
- **reason**: String containing the judge's reasoning for the score
- **label**: Optional label categorizing the result

## Best Practices

1. **Write Clear, Specific Rubrics**: Include explicit scoring criteria and examples
2. **Use Appropriate Judge Models**: Consider using stronger models for complex evaluations
3. **Include Input Context When Relevant**: Set `include_inputs=True` for context-dependent evaluation
4. **Validate Your Rubric**: Test with known good and bad examples to ensure expected scores
5. **Combine with Other Evaluators**: Use alongside trajectory and tool evaluators for comprehensive assessment

## Related Evaluators

- [**TrajectoryEvaluator**](trajectory_evaluator.md): Evaluates the sequence of actions/tools used
- [**FaithfulnessEvaluator**](faithfulness_evaluator.md): Checks if responses are grounded in conversation history
- [**HelpfulnessEvaluator**](helpfulness_evaluator.md): Specifically evaluates helpfulness from user perspective
- [**GoalSuccessRateEvaluator**](goal_success_rate_evaluator.md): Evaluates if user goals were achieved
