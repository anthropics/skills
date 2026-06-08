# Experiment Management

## Overview

Test cases in Strands Evals are organized into `Experiment` objects. This guide covers practical patterns for managing experiments and test cases.

## Organizing Test Cases

### Using Metadata for Organization

```python
from strands_evals import Case

# Add metadata for filtering and organization
cases = [
    Case(
        name="easy-math",
        input="What is 2 + 2?",
        metadata={
            "category": "math",
            "difficulty": "easy",
            "tags": ["arithmetic"]
        }
    ),
    Case(
        name="hard-math",
        input="Solve x^2 + 5x + 6 = 0",
        metadata={
            "category": "math",
            "difficulty": "hard",
            "tags": ["algebra"]
        }
    )
]

# Filter by metadata
easy_cases = [c for c in cases if c.metadata.get("difficulty") == "easy"]
```

### Naming Conventions

```python
# Pattern: {category}-{subcategory}-{number}
Case(name="knowledge-geography-001", input="..."),
Case(name="math-arithmetic-001", input="..."),
```

## Managing Multiple Experiments

### Experiment Collections

```python
from strands_evals import Experiment

experiments = {
    "baseline": Experiment(cases=baseline_cases, evaluators=[...]),
    "with_tools": Experiment(cases=tool_cases, evaluators=[...]),
    "edge_cases": Experiment(cases=edge_cases, evaluators=[...])
}

# Run all
for name, exp in experiments.items():
    print(f"Running {name}...")
    reports = exp.run_evaluations(task_function)
```

### Combining Experiments

```python
# Merge cases from multiple experiments
combined = Experiment(
    cases=exp1.cases + exp2.cases + exp3.cases,
    evaluators=[OutputEvaluator()]
)
```

## Modifying Experiments

### Adding Cases

```python
# Add single case
experiment.cases.append(new_case)

# Add multiple
experiment.cases.extend(additional_cases)
```

### Updating Evaluators

```python
from strands_evals.evaluators import HelpfulnessEvaluator

# Replace evaluators
experiment.evaluators = [
    OutputEvaluator(),
    HelpfulnessEvaluator()
]
```

## Session IDs

Each case gets a unique session ID automatically:

```python
case = Case(input="test")
print(case.session_id)  # Auto-generated UUID

# Or provide custom
case = Case(input="test", session_id="custom-123")
```

## Best Practices

### 1. Use Descriptive Names

```python
# Good
Case(name="customer-service-refund-request", input="...")

# Less helpful
Case(name="test1", input="...")
```

### 2. Include Rich Metadata

```python
Case(
    name="complex-query",
    input="...",
    metadata={
        "category": "customer_service",
        "difficulty": "medium",
        "expected_tools": ["search_orders"],
        "created_date": "2025-01-15"
    }
)
```

### 3. Version Your Experiments

```python
experiment.to_file("experiment_v1.json")
experiment.to_file("experiment_v2.json")

# Or with timestamps
from datetime import datetime
timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
experiment.to_file(f"experiment_{timestamp}.json")
```

## Related Documentation

- [Serialization](serialization.md): Save and load experiments
- [Experiment Generator](../experiment_generator.md): Generate experiments automatically
- [Quickstart Guide](../quickstart.md): Get started with experiments
