# Serialization

## Overview

Strands Evals provides JSON serialization for experiments and reports, enabling you to save, load, version, and share evaluation work.

## Saving Experiments

```python
from strands_evals import Experiment

# Save to file
experiment.to_file("my_experiment.json")
experiment.to_file("my_experiment")  # .json added automatically

# Relative path
experiment.to_file("experiments/baseline.json")

# Absolute path
experiment.to_file("/path/to/experiments/baseline.json")
```

## Loading Experiments

```python
# Load from file
experiment = Experiment.from_file("my_experiment.json")

print(f"Loaded {len(experiment.cases)} cases")
print(f"Evaluators: {[e.get_type_name() for e in experiment.evaluators]}")
```

## Custom Evaluators

Pass custom evaluator classes when loading:

```python
from strands_evals.evaluators import Evaluator

class CustomEvaluator(Evaluator):
    def evaluate(self, evaluation_case):
        # Custom logic
        return EvaluationOutput(score=1.0, test_pass=True, reason="...")

# Save with custom evaluator
experiment = Experiment(
    cases=cases,
    evaluators=[CustomEvaluator()]
)
experiment.to_file("custom.json")

# Load with custom evaluator class
loaded = Experiment.from_file(
    "custom.json",
    custom_evaluators=[CustomEvaluator]
)
```

## Dictionary Conversion

```python
# To dictionary
experiment_dict = experiment.to_dict()

# From dictionary
experiment = Experiment.from_dict(experiment_dict)

# With custom evaluators
experiment = Experiment.from_dict(
    experiment_dict,
    custom_evaluators=[CustomEvaluator]
)
```

## Saving Reports

```python
import json

# Run evaluation
reports = experiment.run_evaluations(task_function)

# Save reports
for i, report in enumerate(reports):
    report_data = {
        "evaluator": experiment.evaluators[i].get_type_name(),
        "overall_score": report.overall_score,
        "scores": report.scores,
        "test_passes": report.test_passes,
        "reasons": report.reasons
    }
    
    with open(f"report_{i}.json", "w") as f:
        json.dump(report_data, f, indent=2)
```

## Versioning Strategies

### Timestamp Versioning

```python
from datetime import datetime

timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
experiment.to_file(f"experiment_{timestamp}.json")
```

### Semantic Versioning

```python
experiment.to_file("experiment_v1.json")
experiment.to_file("experiment_v2.json")
```

## Organizing Files

### Directory Structure

```
experiments/
├── baseline/
│   ├── experiment.json
│   └── reports/
├── iteration_1/
│   ├── experiment.json
│   └── reports/
└── final/
    ├── experiment.json
    └── reports/
```

### Organized Saving

```python
from pathlib import Path

base_dir = Path("experiments/iteration_1")
base_dir.mkdir(parents=True, exist_ok=True)

# Save experiment
experiment.to_file(base_dir / "experiment.json")

# Save reports
reports_dir = base_dir / "reports"
reports_dir.mkdir(exist_ok=True)
```

## Saving Experiments with Reports

```python
from pathlib import Path
import json

def save_with_reports(experiment, reports, base_name):
    base_path = Path(f"evaluations/{base_name}")
    base_path.mkdir(parents=True, exist_ok=True)
    
    # Save experiment
    experiment.to_file(base_path / "experiment.json")
    
    # Save reports
    for i, report in enumerate(reports):
        evaluator_name = experiment.evaluators[i].get_type_name()
        report_data = {
            "evaluator": evaluator_name,
            "overall_score": report.overall_score,
            "pass_rate": sum(report.test_passes) / len(report.test_passes),
            "scores": report.scores
        }
        
        with open(base_path / f"report_{evaluator_name}.json", "w") as f:
            json.dump(report_data, f, indent=2)

# Usage
reports = experiment.run_evaluations(task_function)
save_with_reports(experiment, reports, "baseline_20250115")
```

## Error Handling

```python
from pathlib import Path

def safe_load(path, custom_evaluators=None):
    try:
        file_path = Path(path)
        
        if not file_path.exists():
            raise FileNotFoundError(f"File not found: {path}")
        
        if file_path.suffix != ".json":
            raise ValueError(f"Expected .json file, got: {file_path.suffix}")
        
        experiment = Experiment.from_file(path, custom_evaluators=custom_evaluators)
        print(f"✓ Loaded {len(experiment.cases)} cases")
        return experiment
        
    except Exception as e:
        print(f"✗ Failed to load: {e}")
        return None
```

## Best Practices

### 1. Use Consistent Naming

```python
# Good
experiment.to_file("customer_service_baseline_v1.json")

# Less helpful
experiment.to_file("test.json")
```

### 2. Validate After Loading

```python
experiment = Experiment.from_file("experiment.json")

assert len(experiment.cases) > 0, "No cases loaded"
assert len(experiment.evaluators) > 0, "No evaluators loaded"
```

### 3. Include Metadata

```python
experiment_data = experiment.to_dict()
experiment_data["metadata"] = {
    "created_date": datetime.now().isoformat(),
    "description": "Baseline evaluation",
    "version": "1.0"
}

with open("experiment.json", "w") as f:
    json.dump(experiment_data, f, indent=2)
```

## Related Documentation

- [Experiment Management](experiment_management.md): Organize experiments
- [Experiment Generator](../experiment_generator.md): Generate experiments
- [Quickstart Guide](../quickstart.md): Get started with Strands Evals
