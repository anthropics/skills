# Strands Evaluation Quickstart

Strands Evaluation is a framework for evaluating AI agents and LLM applications. From simple output validation to complex multi-agent interaction analysis, trajectory evaluation, and automated experiment generation, Strands Evaluation provides features to measure and improve your AI systems.

## What Strands Evaluation Provides

- **Multiple Evaluation Types**: Output evaluation, trajectory analysis, tool usage assessment, and interaction evaluation
- **Dynamic Simulators**: Multi-turn conversation simulation with realistic user behavior and goal-oriented interactions
- **LLM-as-a-Judge**: Built-in evaluators using language models for sophisticated assessment with structured scoring
- **Trace-based Evaluation**: Analyze agent behavior through OpenTelemetry execution traces
- **Automated Experiment Generation**: Generate comprehensive test suites from context descriptions
- **Custom Evaluators**: Extensible framework for domain-specific evaluation logic
- **Experiment Management**: Save, load, and version your evaluation experiments with JSON serialization
- **Built-in Scoring Tools**: Helper functions for exact, in-order, and any-order trajectory matching

This quickstart guide shows you how to create your first evaluation experiment, use built-in evaluators to assess agent performance, generate test cases automatically, and analyze results. After completing this guide you can create custom evaluators, implement trace-based evaluation, build comprehensive test suites, and integrate evaluation into your development workflow.

## Install the SDK

First, ensure that you have Python 3.10+ installed.

We'll create a virtual environment to install the Strands Evaluation SDK and its dependencies.

```bash
python -m venv .venv
```

And activate the virtual environment:

* macOS / Linux: `source .venv/bin/activate`
* Windows (CMD): `.venv\Scripts\activate.bat`
* Windows (PowerShell): `.venv\Scripts\Activate.ps1`

Next we'll install the `strands-agents-evals` SDK package:

```bash
pip install strands-agents-evals
```

You'll also need the core Strands Agents SDK and tools for this guide:

```bash
pip install strands-agents strands-agents-tools
```

## Configuring Credentials

Strands Evaluation uses the same model providers as Strands Agents. By default, evaluators use Amazon Bedrock with Claude 4 as the judge model.

To use the examples in this guide, configure your AWS credentials with permissions to invoke Claude 4. You can set up credentials using:

1. **Environment variables**: Set `AWS_ACCESS_KEY_ID`, `AWS_SECRET_ACCESS_KEY`, and optionally `AWS_SESSION_TOKEN`
2. **AWS credentials file**: Configure credentials using `aws configure` CLI command
3. **IAM roles**: If running on AWS services like EC2, ECS, or Lambda

Make sure to enable model access in the Amazon Bedrock console following the [AWS documentation](https://docs.aws.amazon.com/bedrock/latest/userguide/model-access-modify.html).

## Project Setup

Create a directory structure for your evaluation project:

```
my_evaluation/
├── __init__.py
├── basic_eval.py
├── trajectory_eval.py
└── requirements.txt
```

Create the directory: `mkdir my_evaluation`

Create `my_evaluation/requirements.txt`:

```
strands-agents>=1.0.0
strands-agents-tools>=0.2.0
strands-agents-evals>=1.0.0
```

Create the `my_evaluation/__init__.py` file:

```python
from . import basic_eval, trajectory_eval
```

## Basic Output Evaluation

Let's start with a simple output evaluation using the `OutputEvaluator`. Create `my_evaluation/basic_eval.py`:

```python
from strands import Agent
from strands_evals import Case, Experiment
from strands_evals.evaluators import OutputEvaluator

# Define your task function
def get_response(case: Case) -> str:
    agent = Agent(
        system_prompt="You are a helpful assistant that provides accurate information.",
        callback_handler=None  # Disable console output for cleaner evaluation
    )
    response = agent(case.input)
    return str(response)

# Create test cases
test_cases = [
    Case[str, str](
        name="knowledge-1",
        input="What is the capital of France?",
        expected_output="The capital of France is Paris.",
        metadata={"category": "knowledge"}
    ),
    Case[str, str](
        name="knowledge-2", 
        input="What is 2 + 2?",
        expected_output="4",
        metadata={"category": "math"}
    ),
    Case[str, str](
        name="reasoning-1",
        input="If it takes 5 machines 5 minutes to make 5 widgets, how long does it take 100 machines to make 100 widgets?",
        expected_output="5 minutes",
        metadata={"category": "reasoning"}
    )
]

# Create evaluator with custom rubric
evaluator = OutputEvaluator(
    rubric="""
    Evaluate the response based on:
    1. Accuracy - Is the information factually correct?
    2. Completeness - Does it fully answer the question?
    3. Clarity - Is it easy to understand?
    
    Score 1.0 if all criteria are met excellently.
    Score 0.5 if some criteria are partially met.
    Score 0.0 if the response is inadequate or incorrect.
    """,
    include_inputs=True
)

# Create and run experiment
experiment = Experiment[str, str](cases=test_cases, evaluators=[evaluator])
reports = experiment.run_evaluations(get_response)

# Display results
print("=== Basic Output Evaluation Results ===")
reports[0].run_display()

# Save experiment for later analysis
experiment.to_file("basic_evaluation")
print("\nExperiment saved to ./experiment_files/basic_evaluation.json")
```

## Tool Usage Evaluation

Now let's evaluate how well agents use tools. Create `my_evaluation/trajectory_eval.py`:

```python
from strands import Agent
from strands_evals import Case, Experiment
from strands_evals.evaluators import TrajectoryEvaluator
from strands_evals.extractors import tools_use_extractor
from strands_tools import calculator, current_time

# Define task function that captures tool usage
def get_response_with_tools(case: Case) -> dict:
    agent = Agent(
        tools=[calculator, current_time],
        system_prompt="You are a helpful assistant. Use tools when appropriate.",
        callback_handler=None
    )
    response = agent(case.input)
    
    # Extract trajectory efficiently to prevent context overflow
    trajectory = tools_use_extractor.extract_agent_tools_used_from_messages(agent.messages)
    
    return {"output": str(response), "trajectory": trajectory}

# Create test cases with expected tool usage
test_cases = [
    Case[str, str](
        name="calculation-1",
        input="What is 15% of 230?",
        expected_trajectory=["calculator"],
        metadata={"category": "math", "expected_tools": ["calculator"]}
    ),
    Case[str, str](
        name="time-1", 
        input="What time is it right now?",
        expected_trajectory=["current_time"],
        metadata={"category": "time", "expected_tools": ["current_time"]}
    ),
    Case[str, str](
        name="complex-1",
        input="What time is it and what is 25 * 48?",
        expected_trajectory=["current_time", "calculator"],
        metadata={"category": "multi_tool", "expected_tools": ["current_time", "calculator"]}
    )
]

# Create trajectory evaluator
evaluator = TrajectoryEvaluator(
    rubric="""
    Evaluate the tool usage trajectory:
    1. Correct tool selection - Were the right tools chosen for the task?
    2. Proper sequence - Were tools used in a logical order?
    3. Efficiency - Were unnecessary tools avoided?
    
    Use the built-in scoring tools to verify trajectory matches:
    - exact_match_scorer for exact sequence matching
    - in_order_match_scorer for ordered subset matching  
    - any_order_match_scorer for unordered matching
    
    Score 1.0 if optimal tools used correctly.
    Score 0.5 if correct tools used but suboptimal sequence.
    Score 0.0 if wrong tools used or major inefficiencies.
    """,
    include_inputs=True
)

# Update evaluator with tool descriptions to prevent context overflow
sample_agent = Agent(tools=[calculator, current_time])
tool_descriptions = tools_use_extractor.extract_tools_description(sample_agent, is_short=True)
evaluator.update_trajectory_description(tool_descriptions)

# Create and run experiment
experiment = Experiment[str, str](cases=test_cases, evaluators=[evaluator])
reports = experiment.run_evaluations(get_response_with_tools)

# Display results
print("=== Tool Usage Evaluation Results ===")
reports[0].run_display()

# Save experiment
experiment.to_file("trajectory_evaluation")
print("\nExperiment saved to ./experiment_files/trajectory_evaluation.json")
```

## Trace-based Helpfulness Evaluation

For more advanced evaluation, let's assess agent helpfulness using execution traces:

!!! warning "Required: Session ID Trace Attributes"
    When using `StrandsInMemorySessionMapper`, you **must** include session ID trace attributes in your agent configuration. This prevents spans from different test cases from being mixed together in the memory exporter.

```python
from strands import Agent
from strands_evals import Case, Experiment
from strands_evals.evaluators import HelpfulnessEvaluator
from strands_evals.telemetry import StrandsEvalsTelemetry
from strands_evals.mappers import StrandsInMemorySessionMapper
from strands_tools import calculator

# Setup telemetry for trace capture
telemetry = StrandsEvalsTelemetry().setup_in_memory_exporter()

def user_task_function(case: Case) -> dict:
    # Clear previous traces
    telemetry.in_memory_exporter.clear()
    
    agent = Agent(
        tools=[calculator],
        # IMPORTANT: trace_attributes with session IDs are required when using StrandsInMemorySessionMapper
        # to prevent spans from different test cases from being mixed together in the memory exporter
        trace_attributes={
            "gen_ai.conversation.id": case.session_id,
            "session.id": case.session_id
        },
        callback_handler=None
    )
    response = agent(case.input)
    
    # Map spans to session for evaluation
    finished_spans = telemetry.in_memory_exporter.get_finished_spans()
    mapper = StrandsInMemorySessionMapper()
    session = mapper.map_to_session(finished_spans, session_id=case.session_id)
    
    return {"output": str(response), "trajectory": session}

# Create test cases for helpfulness evaluation
test_cases = [
    Case[str, str](
        name="helpful-1",
        input="I need help calculating the tip for a $45.67 restaurant bill with 18% tip.",
        metadata={"category": "practical_help"}
    ),
    Case[str, str](
        name="helpful-2",
        input="Can you explain what 2^8 equals and show the calculation?",
        metadata={"category": "educational"}
    )
]

# Create helpfulness evaluator (uses seven-level scoring)
evaluator = HelpfulnessEvaluator()

# Run evaluation
experiment = Experiment[str, str](cases=test_cases, evaluators=[evaluator])
reports = experiment.run_evaluations(user_task_function)

print("=== Helpfulness Evaluation Results ===")
reports[0].run_display()
```

## Running Evaluations

Run your evaluations using Python:

```bash
# Run basic output evaluation
python -u my_evaluation/basic_eval.py

# Run trajectory evaluation  
python -u my_evaluation/trajectory_eval.py
```

You'll see detailed results showing:
- Individual test case scores and reasoning
- Overall experiment statistics
- Pass/fail rates by category
- Detailed judge explanations

## Async Evaluation

For improved performance, you can run evaluations asynchronously using `run_evaluations_async`. This is particularly useful when evaluating multiple test cases, as it allows concurrent execution and significantly reduces total evaluation time.

### Basic Async Example (Applies to Trace-based evaluators)

Here's how to convert the basic output evaluation to use async:

```python
import asyncio
from strands import Agent
from strands_evals import Case, Experiment
from strands_evals.evaluators import OutputEvaluator

# Define async task function
async def get_response_async(case: Case) -> str:
    agent = Agent(
        system_prompt="You are a helpful assistant that provides accurate information.",
        callback_handler=None
    )
    response = await agent.invoke_async(case.input)
    return str(response)

# Create test cases (same as before)
test_cases = [
    Case[str, str](
        name="knowledge-1",
        input="What is the capital of France?",
        expected_output="The capital of France is Paris.",
        metadata={"category": "knowledge"}
    ),
    Case[str, str](
        name="knowledge-2", 
        input="What is 2 + 2?",
        expected_output="4",
        metadata={"category": "math"}
    ),
]

# Create evaluator
evaluator = OutputEvaluator(
    rubric="""
    Evaluate the response based on:
    1. Accuracy - Is the information factually correct?
    2. Completeness - Does it fully answer the question?
    3. Clarity - Is it easy to understand?
    
    Score 1.0 if all criteria are met excellently.
    Score 0.5 if some criteria are partially met.
    Score 0.0 if the response is inadequate or incorrect.
    """,
    include_inputs=True
)

# Run async evaluation
async def run_async_evaluation():
    experiment = Experiment[str, str](cases=test_cases, evaluators=[evaluator])
    reports = await experiment.run_evaluations_async(get_response_async)
    
    reports[0].run_display()
    
    return reports[0]

# Execute the async evaluation
if __name__ == "__main__":
    report = asyncio.run(run_async_evaluation())
```

## Understanding Evaluation Results

Each evaluation returns comprehensive results:

```python
# Access individual case results
for case_result in report.case_results:
    print(f"Case: {case_result.case.name}")
    print(f"Score: {case_result.evaluation_output.score}")
    print(f"Passed: {case_result.evaluation_output.test_pass}")
    print(f"Reason: {case_result.evaluation_output.reason}")
    print("---")

# Get summary statistics
summary = report.get_summary()
print(f"Overall pass rate: {summary['pass_rate']:.2%}")
print(f"Average score: {summary['average_score']:.2f}")
```

## Automated Experiment Generation

Generate test cases automatically from context descriptions:

```python
from strands_evals.generators import ExperimentGenerator
from strands_evals.evaluators import TrajectoryEvaluator

# Define tool context
tool_context = """
Available tools:
- calculator(expression: str) -> float: Evaluate mathematical expressions
- current_time() -> str: Get the current date and time
- file_read(path: str) -> str: Read file contents
"""

# Generate experiment automatically
async def generate_experiment():
    generator = ExperimentGenerator[str, str](str, str)
    
    experiment = await generator.from_context_async(
        context=tool_context,
        num_cases=5,
        evaluator=TrajectoryEvaluator,
        task_description="Assistant with calculation and time tools",
        num_topics=2  # Distribute across multiple topics
    )
    
    # Save generated experiment
    experiment.to_file("generated_experiment")
    print("Generated experiment saved!")
    
    return experiment

# Run the generator
import asyncio
generated_exp = asyncio.run(generate_experiment())
```

## Custom Evaluators

Create domain-specific evaluation logic:

```python
from strands_evals.evaluators import Evaluator
from strands_evals.types import EvaluationData, EvaluationOutput

class SafetyEvaluator(Evaluator[str, str]):
    """Evaluates responses for safety and appropriateness."""
    
    def evaluate(self, evaluation_case: EvaluationData[str, str]) -> EvaluationOutput:
        response = evaluation_case.actual_output.lower()
        
        # Check for safety issues
        unsafe_patterns = ["harmful", "dangerous", "illegal", "inappropriate"]
        safety_violations = [pattern for pattern in unsafe_patterns if pattern in response]
        
        if not safety_violations:
            return EvaluationOutput(
                score=1.0,
                test_pass=True,
                reason="Response is safe and appropriate",
                label="safe"
            )
        else:
            return EvaluationOutput(
                score=0.0,
                test_pass=False,
                reason=f"Safety concerns: {', '.join(safety_violations)}",
                label="unsafe"
            )

# Use custom evaluator
safety_evaluator = SafetyEvaluator()
experiment = Experiment[str, str](cases=test_cases, evaluators=[safety_evaluator])
```

## Best Practices

### Evaluation Strategy
1. **Start Simple**: Begin with output evaluation before moving to complex trajectory analysis
2. **Use Multiple Evaluators**: Combine output, trajectory, and helpfulness evaluators for comprehensive assessment
3. **Create Diverse Test Cases**: Cover different categories, difficulty levels, and edge cases
4. **Regular Evaluation**: Run evaluations frequently during development

### Performance Optimization
1. **Use Extractors**: Always use `tools_use_extractor` functions to prevent context overflow
2. **Batch Processing**: Process multiple test cases efficiently
3. **Choose Appropriate Models**: Use stronger judge models for complex evaluations
4. **Cache Results**: Save experiments to avoid re-running expensive evaluations

### Experiment Management
1. **Version Control**: Save experiments with descriptive names and timestamps
2. **Document Rubrics**: Write clear, specific evaluation criteria
3. **Track Changes**: Monitor how evaluation scores change as you improve your agents
4. **Share Results**: Use saved experiments to collaborate with team members

## Next Steps

Ready to dive deeper? Explore these resources:

- [Output Evaluator](evaluators/output_evaluator.md) - Detailed guide to LLM-based output evaluation
- [Trajectory Evaluator](evaluators/trajectory_evaluator.md) - Comprehensive tool usage and sequence evaluation
- [Helpfulness Evaluator](evaluators/helpfulness_evaluator.md) - Seven-level helpfulness assessment
- [Custom Evaluators](evaluators/custom_evaluator.md) - Build domain-specific evaluation logic
- [Experiment Generator](experiment_generator.md) - Automatically generate comprehensive test suites
- [Serialization](how-to/serialization.md) - Save, load, and version your evaluation experiments
