# Custom Evaluator

## Overview

The Strands Evals SDK allows you to create custom evaluators by extending the base `Evaluator` class. This enables you to implement domain-specific evaluation logic tailored to your unique requirements. A complete example can be found [here](https://github.com/strands-agents/docs/blob/main/docs/examples/evals-sdk/custom_evaluator.py).

## When to Create a Custom Evaluator

Create a custom evaluator when:

- Built-in evaluators don't meet your specific needs
- You need specialized evaluation logic for your domain
- You want to integrate external evaluation services
- You need custom scoring algorithms
- You require specific data processing or analysis

## Base Evaluator Class

All evaluators inherit from the base `Evaluator` class, which provides the structure for evaluation:

```python
from strands_evals.evaluators import Evaluator
from strands_evals.types.evaluation import EvaluationData, EvaluationOutput
from typing_extensions import TypeVar

InputT = TypeVar("InputT")
OutputT = TypeVar("OutputT")

class CustomEvaluator(Evaluator[InputT, OutputT]):
    def __init__(self, custom_param: str):
        super().__init__()
        self.custom_param = custom_param
    
    def evaluate(self, evaluation_case: EvaluationData[InputT, OutputT]) -> list[EvaluationOutput]:
        """Synchronous evaluation implementation"""
        # Your evaluation logic here
        pass
    
    async def evaluate_async(self, evaluation_case: EvaluationData[InputT, OutputT]) -> list[EvaluationOutput]:
        """Asynchronous evaluation implementation"""
        # Your async evaluation logic here
        pass
```

## Required Methods

### `evaluate(evaluation_case: EvaluationData) -> list[EvaluationOutput]`
Synchronous evaluation method that must be implemented.

**Parameters:**

- `evaluation_case`: Contains input, output, expected values, and trajectory

**Returns:**

- List of `EvaluationOutput` objects with scores and reasoning

### `evaluate_async(evaluation_case: EvaluationData) -> list[EvaluationOutput]`
Asynchronous evaluation method that must be implemented.

**Parameters:**

- Same as `evaluate()`

**Returns:**

- Same as `evaluate()`

## EvaluationData Structure

The `evaluation_case` parameter provides:

- `input`: The input to the task
- `actual_output`: The actual output from the agent
- `expected_output`: The expected output (if provided)
- `actual_trajectory`: The execution trajectory (if captured)
- `expected_trajectory`: The expected trajectory (if provided)
- `actual_interactions`: Interactions between agents (if applicable)
- `expected_interactions`: Expected interactions (if provided)

## EvaluationOutput Structure

Your evaluator should return `EvaluationOutput` objects with:

- `score`: Float between 0.0 and 1.0
- `test_pass`: Boolean indicating pass/fail
- `reason`: String explaining the evaluation
- `label`: Optional categorical label

## Example: Simple Custom Evaluator

```python
from strands_evals.evaluators import Evaluator
from strands_evals.types.evaluation import EvaluationData, EvaluationOutput
from typing_extensions import TypeVar

InputT = TypeVar("InputT")
OutputT = TypeVar("OutputT")

class LengthEvaluator(Evaluator[InputT, OutputT]):
    """Evaluates if output length is within acceptable range."""
    
    def __init__(self, min_length: int, max_length: int):
        super().__init__()
        self.min_length = min_length
        self.max_length = max_length
    
    def evaluate(self, evaluation_case: EvaluationData[InputT, OutputT]) -> list[EvaluationOutput]:
        output_text = str(evaluation_case.actual_output)
        length = len(output_text)
        
        if self.min_length <= length <= self.max_length:
            score = 1.0
            test_pass = True
            reason = f"Output length {length} is within acceptable range [{self.min_length}, {self.max_length}]"
        else:
            score = 0.0
            test_pass = False
            reason = f"Output length {length} is outside acceptable range [{self.min_length}, {self.max_length}]"
        
        return [EvaluationOutput(score=score, test_pass=test_pass, reason=reason)]
    
    async def evaluate_async(self, evaluation_case: EvaluationData[InputT, OutputT]) -> list[EvaluationOutput]:
        # For simple evaluators, async can just call sync version
        return self.evaluate(evaluation_case)
```

## Example: LLM-Based Custom Evaluator

```python
from strands import Agent
from strands_evals.evaluators import Evaluator
from strands_evals.types.evaluation import EvaluationData, EvaluationOutput
from typing_extensions import TypeVar

InputT = TypeVar("InputT")
OutputT = TypeVar("OutputT")

class ToneEvaluator(Evaluator[InputT, OutputT]):
    """Evaluates the tone of agent responses."""
    
    def __init__(self, expected_tone: str, model: str = None):
        super().__init__()
        self.expected_tone = expected_tone
        self.model = model
    
    def evaluate(self, evaluation_case: EvaluationData[InputT, OutputT]) -> list[EvaluationOutput]:
        judge = Agent(
            model=self.model,
            system_prompt=f"""
            Evaluate if the response has a {self.expected_tone} tone.
            Score 1.0 if tone matches perfectly.
            Score 0.5 if tone is partially appropriate.
            Score 0.0 if tone is inappropriate.
            """,
            callback_handler=None
        )
        
        prompt = f"""
        Input: {evaluation_case.input}
        Response: {evaluation_case.actual_output}
        
        Evaluate the tone of the response.
        """
        
        result = judge.structured_output(EvaluationOutput, prompt)
        return [result]
    
    async def evaluate_async(self, evaluation_case: EvaluationData[InputT, OutputT]) -> list[EvaluationOutput]:
        judge = Agent(
            model=self.model,
            system_prompt=f"""
            Evaluate if the response has a {self.expected_tone} tone.
            Score 1.0 if tone matches perfectly.
            Score 0.5 if tone is partially appropriate.
            Score 0.0 if tone is inappropriate.
            """,
            callback_handler=None
        )
        
        prompt = f"""
        Input: {evaluation_case.input}
        Response: {evaluation_case.actual_output}
        
        Evaluate the tone of the response.
        """
        
        result = await judge.structured_output_async(EvaluationOutput, prompt)
        return [result]
```

## Example: Metric-Based Custom Evaluator

```python
from strands_evals.evaluators import Evaluator
from strands_evals.types.evaluation import EvaluationData, EvaluationOutput
from typing_extensions import TypeVar
import re

InputT = TypeVar("InputT")
OutputT = TypeVar("OutputT")

class KeywordPresenceEvaluator(Evaluator[InputT, OutputT]):
    """Evaluates if required keywords are present in output."""
    
    def __init__(self, required_keywords: list[str], case_sensitive: bool = False):
        super().__init__()
        self.required_keywords = required_keywords
        self.case_sensitive = case_sensitive
    
    def evaluate(self, evaluation_case: EvaluationData[InputT, OutputT]) -> list[EvaluationOutput]:
        output_text = str(evaluation_case.actual_output)
        if not self.case_sensitive:
            output_text = output_text.lower()
            keywords = [k.lower() for k in self.required_keywords]
        else:
            keywords = self.required_keywords
        
        found_keywords = [kw for kw in keywords if kw in output_text]
        missing_keywords = [kw for kw in keywords if kw not in output_text]
        
        score = len(found_keywords) / len(keywords) if keywords else 1.0
        test_pass = score == 1.0
        
        if test_pass:
            reason = f"All required keywords found: {found_keywords}"
        else:
            reason = f"Missing keywords: {missing_keywords}. Found: {found_keywords}"
        
        return [EvaluationOutput(
            score=score,
            test_pass=test_pass,
            reason=reason,
            label=f"{len(found_keywords)}/{len(keywords)} keywords"
        )]
    
    async def evaluate_async(self, evaluation_case: EvaluationData[InputT, OutputT]) -> list[EvaluationOutput]:
        return self.evaluate(evaluation_case)
```

## Using Custom Evaluators

```python
from strands_evals import Case, Experiment

# Create test cases
test_cases = [
    Case[str, str](
        name="test-1",
        input="Write a professional email",
        metadata={"category": "email"}
    ),
]

# Use custom evaluator
evaluator = ToneEvaluator(expected_tone="professional")

# Run evaluation
experiment = Experiment[str, str](cases=test_cases, evaluators=[evaluator])
reports = experiment.run_evaluations(task_function)
reports[0].run_display()
```

## Best Practices

1. **Inherit from Base Evaluator**: Always extend the `Evaluator` class
2. **Implement Both Methods**: Provide both sync and async implementations
3. **Return List**: Always return a list of `EvaluationOutput` objects
4. **Provide Clear Reasoning**: Include detailed explanations in the `reason` field
5. **Use Appropriate Scores**: Keep scores between 0.0 and 1.0
6. **Handle Edge Cases**: Account for missing or malformed data
7. **Document Parameters**: Clearly document what your evaluator expects
8. **Test Thoroughly**: Validate your evaluator with diverse test cases

## Advanced: Multi-Level Evaluation

```python
class MultiLevelEvaluator(Evaluator[InputT, OutputT]):
    """Evaluates at multiple levels (e.g., per tool call)."""
    
    def evaluate(self, evaluation_case: EvaluationData[InputT, OutputT]) -> list[EvaluationOutput]:
        results = []
        
        # Evaluate each tool call in trajectory
        if evaluation_case.actual_trajectory:
            for tool_call in evaluation_case.actual_trajectory:
                # Evaluate this tool call
                score = self._evaluate_tool_call(tool_call)
                results.append(EvaluationOutput(
                    score=score,
                    test_pass=score >= 0.5,
                    reason=f"Tool call evaluation: {tool_call}"
                ))
        
        return results
    
    def _evaluate_tool_call(self, tool_call):
        # Your tool call evaluation logic
        return 1.0
```

## Related Documentation

- [**OutputEvaluator**](output_evaluator.md): LLM-based output evaluation with custom rubrics
- [**TrajectoryEvaluator**](trajectory_evaluator.md): Sequence-based evaluation
- [**Evaluator Base Class**](https://github.com/strands-agents/evals/blob/main/src/strands_evals/evaluators/evaluator.py#L19): Core evaluator interface
