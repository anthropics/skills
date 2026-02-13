# Experiment Generator

## Overview

The `ExperimentGenerator` automatically creates comprehensive evaluation experiments with test cases and rubrics tailored to your agent's specific tasks and domains. It uses LLMs to generate diverse, realistic test scenarios and evaluation criteria, significantly reducing the manual effort required to build evaluation suites.

## Key Features

- **Automated Test Case Generation**: Creates diverse test cases from context descriptions
- **Topic-Based Planning**: Uses `TopicPlanner` to ensure comprehensive coverage across multiple topics
- **Rubric Generation**: Automatically generates evaluation rubrics for default evaluators
- **Multi-Step Dataset Creation**: Generates test cases across multiple topics with controlled distribution
- **Flexible Input/Output Types**: Supports custom types for inputs, outputs, and trajectories
- **Parallel Generation**: Efficiently generates multiple test cases concurrently
- **Experiment Evolution**: Extends or updates existing experiments with new cases

## When to Use

Use the `ExperimentGenerator` when you need to:

- Quickly bootstrap evaluation experiments without manual test case creation
- Generate diverse test cases covering multiple topics or scenarios
- Create evaluation rubrics automatically for standard evaluators
- Expand existing experiments with additional test cases
- Adapt experiments from one task to another similar task
- Ensure comprehensive coverage across different difficulty levels

## Basic Usage

### Simple Generation from Context

```python
import asyncio
from strands_evals.generators import ExperimentGenerator
from strands_evals.evaluators import OutputEvaluator

# Initialize generator
generator = ExperimentGenerator[str, str](
    input_type=str,
    output_type=str,
    include_expected_output=True
)

# Generate experiment from context
async def generate_experiment():
    experiment = await generator.from_context_async(
        context="""
        Available tools:
        - calculator(expression: str) -> float: Evaluate mathematical expressions
        - current_time() -> str: Get current date and time
        """,
        task_description="Math and time assistant",
        num_cases=5,
        evaluator=OutputEvaluator
    )
    return experiment

# Run generation
experiment = asyncio.run(generate_experiment())
print(f"Generated {len(experiment.cases)} test cases")
```

## Topic-Based Multi-Step Generation

The `TopicPlanner` enables multi-step dataset generation by breaking down your context into diverse topics, ensuring comprehensive coverage:

```python
import asyncio
from strands_evals.generators import ExperimentGenerator
from strands_evals.evaluators import TrajectoryEvaluator

generator = ExperimentGenerator[str, str](
    input_type=str,
    output_type=str,
    include_expected_trajectory=True
)

async def generate_with_topics():
    experiment = await generator.from_context_async(
        context="""
        Customer service agent with tools:
        - search_knowledge_base(query: str) -> str
        - create_ticket(issue: str, priority: str) -> str
        - send_email(to: str, subject: str, body: str) -> str
        """,
        task_description="Customer service assistant",
        num_cases=15,
        num_topics=3,  # Distribute across 3 topics
        evaluator=TrajectoryEvaluator
    )
    
    # Cases will be distributed across topics like:
    # - Topic 1: Knowledge base queries (5 cases)
    # - Topic 2: Ticket creation scenarios (5 cases)
    # - Topic 3: Email communication (5 cases)
    
    return experiment

experiment = asyncio.run(generate_with_topics())
```

## TopicPlanner

The `TopicPlanner` is a utility class that strategically plans diverse topics for test case generation, ensuring comprehensive coverage across different aspects of your agent's capabilities.

### How TopicPlanner Works

1. **Analyzes Context**: Examines your agent's context and task description
2. **Identifies Topics**: Generates diverse, non-overlapping topics
3. **Plans Coverage**: Distributes test cases across topics strategically
4. **Defines Key Aspects**: Specifies 2-5 key aspects per topic for focused testing

### Topic Planning Example

```python
import asyncio
from strands_evals.generators import TopicPlanner

planner = TopicPlanner()

async def plan_topics():
    topic_plan = await planner.plan_topics_async(
        context="""
        E-commerce agent with capabilities:
        - Product search and recommendations
        - Order management and tracking
        - Customer support and returns
        - Payment processing
        """,
        task_description="E-commerce assistant",
        num_topics=4,
        num_cases=20
    )
    
    # Examine generated topics
    for topic in topic_plan.topics:
        print(f"\nTopic: {topic.title}")
        print(f"Description: {topic.description}")
        print(f"Key Aspects: {', '.join(topic.key_aspects)}")
    
    return topic_plan

topic_plan = asyncio.run(plan_topics())
```

### Topic Structure

Each topic includes:

```python
class Topic(BaseModel):
    title: str  # Brief descriptive title
    description: str  # Short explanation
    key_aspects: list[str]  # 2-5 aspects to explore
```

## Generation Methods

### 1. From Context

Generate experiments based on specific context that test cases should reference:

```python
async def generate_from_context():
    experiment = await generator.from_context_async(
        context="Agent with weather API and location tools",
        task_description="Weather information assistant",
        num_cases=10,
        num_topics=2,  # Optional: distribute across topics
        evaluator=OutputEvaluator
    )
    return experiment
```

### 2. From Scratch

Generate experiments from topic lists and task descriptions:

```python
async def generate_from_scratch():
    experiment = await generator.from_scratch_async(
        topics=["product search", "order tracking", "returns"],
        task_description="E-commerce customer service",
        num_cases=12,
        evaluator=TrajectoryEvaluator
    )
    return experiment
```

### 3. From Existing Experiment

Create new experiments inspired by existing ones:

```python
async def generate_from_experiment():
    # Load existing experiment
    source_experiment = Experiment.from_file("original_experiment", "json")
    
    # Generate similar experiment for new task
    new_experiment = await generator.from_experiment_async(
        source_experiment=source_experiment,
        task_description="New task with similar structure",
        num_cases=8,
        extra_information="Additional context about tools and capabilities"
    )
    return new_experiment
```

### 4. Update Existing Experiment

Extend experiments with additional test cases:

```python
async def update_experiment():
    source_experiment = Experiment.from_file("current_experiment", "json")
    
    updated_experiment = await generator.update_current_experiment_async(
        source_experiment=source_experiment,
        task_description="Enhanced task description",
        num_cases=5,  # Add 5 new cases
        context="Additional context for new cases",
        add_new_cases=True,
        add_new_rubric=True
    )
    return updated_experiment
```

## Configuration Options

### Input/Output Types

Configure the structure of generated test cases:

```python
from typing import Dict, List

# Complex types
generator = ExperimentGenerator[Dict[str, str], List[str]](
    input_type=Dict[str, str],
    output_type=List[str],
    include_expected_output=True,
    include_expected_trajectory=True,
    include_metadata=True
)
```

### Parallel Generation

Control concurrent test case generation:

```python
generator = ExperimentGenerator[str, str](
    input_type=str,
    output_type=str,
    max_parallel_num_cases=20  # Generate up to 20 cases in parallel
)
```

### Custom Prompts

Customize generation behavior with custom prompts:

```python
from strands_evals.generators.prompt_template import (
    generate_case_template,
    generate_rubric_template
)

generator = ExperimentGenerator[str, str](
    input_type=str,
    output_type=str,
    case_system_prompt="Custom prompt for case generation...",
    rubric_system_prompt="Custom prompt for rubric generation..."
)
```

## Complete Example: Multi-Step Dataset Generation

```python
import asyncio
from strands_evals.generators import ExperimentGenerator
from strands_evals.evaluators import TrajectoryEvaluator, HelpfulnessEvaluator

async def create_comprehensive_dataset():
    # Initialize generator with trajectory support
    generator = ExperimentGenerator[str, str](
        input_type=str,
        output_type=str,
        include_expected_output=True,
        include_expected_trajectory=True,
        include_metadata=True
    )
    
    # Step 1: Generate initial experiment with topic planning
    print("Step 1: Generating initial experiment...")
    experiment = await generator.from_context_async(
        context="""
        Multi-agent system with:
        - Research agent: Searches and analyzes information
        - Writing agent: Creates content and summaries
        - Review agent: Validates and improves outputs
        
        Tools available:
        - web_search(query: str) -> str
        - summarize(text: str) -> str
        - fact_check(claim: str) -> bool
        """,
        task_description="Research and content creation assistant",
        num_cases=15,
        num_topics=3,  # Research, Writing, Review
        evaluator=TrajectoryEvaluator
    )
    
    print(f"Generated {len(experiment.cases)} cases across 3 topics")
    
    # Step 2: Add more cases to expand coverage
    print("\nStep 2: Expanding experiment...")
    expanded_experiment = await generator.update_current_experiment_async(
        source_experiment=experiment,
        task_description="Research and content creation with edge cases",
        num_cases=5,
        context="Focus on error handling and complex multi-step scenarios",
        add_new_cases=True,
        add_new_rubric=False  # Keep existing rubric
    )
    
    print(f"Expanded to {len(expanded_experiment.cases)} total cases")
    
    # Step 3: Add helpfulness evaluator
    print("\nStep 3: Adding helpfulness evaluator...")
    helpfulness_eval = await generator.construct_evaluator_async(
        prompt="Evaluate helpfulness for research and content creation tasks",
        evaluator=HelpfulnessEvaluator
    )
    expanded_experiment.evaluators.append(helpfulness_eval)
    
    # Step 4: Save experiment
    expanded_experiment.to_file("comprehensive_dataset", "json")
    print("\nDataset saved to ./experiment_files/comprehensive_dataset.json")
    
    return expanded_experiment

# Run the multi-step generation
experiment = asyncio.run(create_comprehensive_dataset())

# Examine results
print(f"\nFinal experiment:")
print(f"- Total cases: {len(experiment.cases)}")
print(f"- Evaluators: {len(experiment.evaluators)}")
print(f"- Categories: {set(c.metadata.get('category', 'unknown') for c in experiment.cases if c.metadata)}")
```

## Difficulty Levels

The generator automatically distributes test cases across difficulty levels:

- **Easy**: ~30% of cases - Basic, straightforward scenarios
- **Medium**: ~50% of cases - Standard complexity
- **Hard**: ~20% of cases - Complex, edge cases

## Supported Evaluators

The generator can automatically create rubrics for these default evaluators:

- `OutputEvaluator`: Evaluates output quality
- `TrajectoryEvaluator`: Evaluates tool usage sequences
- `InteractionsEvaluator`: Evaluates conversation interactions

For other evaluators, pass `evaluator=None` or use `Evaluator()` as a placeholder.

## Best Practices

### 1. Provide Rich Context

```python
# Good: Detailed context
context = """
Agent capabilities:
- Tool 1: search_database(query: str) -> List[Result]
  Returns up to 10 results from knowledge base
- Tool 2: analyze_sentiment(text: str) -> Dict[str, float]
  Returns sentiment scores (positive, negative, neutral)
  
Agent behavior:
- Always searches before answering
- Cites sources in responses
- Handles "no results" gracefully
"""

# Less effective: Vague context
context = "Agent with search and analysis tools"
```

### 2. Use Topic Planning for Large Datasets

```python
# For 15+ cases, use topic planning
experiment = await generator.from_context_async(
    context=context,
    task_description=task,
    num_cases=20,
    num_topics=4  # Ensures diverse coverage
)
```

### 3. Iterate and Expand

```python
# Start small
initial = await generator.from_context_async(
    context=context,
    task_description=task,
    num_cases=5
)

# Test and refine
# ... run evaluations ...

# Expand based on findings
expanded = await generator.update_current_experiment_async(
    source_experiment=initial,
    task_description=task,
    num_cases=10,
    context="Focus on areas where initial cases showed weaknesses"
)
```

### 4. Save Intermediate Results

```python
# Save after each generation step
experiment.to_file(f"experiment_v{version}", "json")
```

## Common Patterns

### Pattern 1: Bootstrap Evaluation Suite

```python
async def bootstrap_evaluation():
    generator = ExperimentGenerator[str, str](str, str)
    
    experiment = await generator.from_context_async(
        context="Your agent context here",
        task_description="Your task here",
        num_cases=10,
        num_topics=2,
        evaluator=OutputEvaluator
    )
    
    experiment.to_file("initial_suite", "json")
    return experiment
```

### Pattern 2: Adapt Existing Experiments

```python
async def adapt_for_new_task():
    source = Experiment.from_file("existing_experiment", "json")
    generator = ExperimentGenerator[str, str](str, str)
    
    adapted = await generator.from_experiment_async(
        source_experiment=source,
        task_description="New task description",
        num_cases=len(source.cases),
        extra_information="New context and tools"
    )
    
    return adapted
```

### Pattern 3: Incremental Expansion

```python
async def expand_incrementally():
    experiment = Experiment.from_file("current", "json")
    generator = ExperimentGenerator[str, str](str, str)
    
    # Add edge cases
    experiment = await generator.update_current_experiment_async(
        source_experiment=experiment,
        task_description="Focus on edge cases",
        num_cases=5,
        context="Error handling, boundary conditions",
        add_new_cases=True,
        add_new_rubric=False
    )
    
    # Add performance cases
    experiment = await generator.update_current_experiment_async(
        source_experiment=experiment,
        task_description="Focus on performance",
        num_cases=5,
        context="Large inputs, complex queries",
        add_new_cases=True,
        add_new_rubric=False
    )
    
    return experiment
```

## Troubleshooting

### Issue: Generated Cases Are Too Similar

**Solution**: Use topic planning with more topics

```python
experiment = await generator.from_context_async(
    context=context,
    task_description=task,
    num_cases=20,
    num_topics=5  # Increase topic diversity
)
```

### Issue: Cases Don't Match Expected Complexity

**Solution**: Provide more detailed context and examples

```python
context = """
Detailed context with:
- Specific tool descriptions
- Expected behavior patterns
- Example scenarios
- Edge cases to consider
"""
```

### Issue: Rubric Generation Fails

**Solution**: Use explicit rubric or skip automatic generation

```python
# Option 1: Provide custom rubric
evaluator = OutputEvaluator(rubric="Your custom rubric here")
experiment = Experiment(cases=cases, evaluators=[evaluator])

# Option 2: Generate without evaluator
experiment = await generator.from_context_async(
    context=context,
    task_description=task,
    num_cases=10,
    evaluator=None  # No automatic rubric generation
)
```

## Related Documentation

- [Quickstart Guide](quickstart.md): Get started with Strands Evals
- [Output Evaluator](evaluators/output_evaluator.md): Learn about output evaluation
- [Trajectory Evaluator](evaluators/trajectory_evaluator.md): Understand trajectory evaluation
- [Dataset Management](how-to/experiment_management.md): Manage and organize datasets
- [Serialization](how-to/serialization.md): Save and load experiments
