# Type Hints Best Practices for ML Applications

## Overview

Comprehensive type annotations in Python 3.13 provide IDE support, runtime validation, and self-documenting code. This guide covers practical type hints patterns specifically for ML backends, focusing on improving code clarity and catching errors early.

## 1. Basic Type Annotations for ML Code

### Function Type Hints

```python
import numpy as np
from numpy.typing import NDArray
from typing import Sequence, Mapping

def preprocess_features(raw_data: Sequence[float],
                       normalize: bool = True) -> NDArray[np.float32]:
    """Preprocess raw features into normalized array.

    Args:
        raw_data: Sequence of raw feature values
        normalize: Whether to normalize to [0, 1] range

    Returns:
        Preprocessed feature array of shape (n_features,)
    """
    data = np.array(raw_data, dtype=np.float32)

    if normalize:
        data = (data - data.min()) / (data.max() - data.min() + 1e-8)

    return data

def predict(model, features: NDArray[np.float32]) -> float:
    """Generate prediction from features.

    Args:
        model: Pre-trained ML model
        features: Feature array of shape (n_features,)

    Returns:
        Scalar prediction value
    """
    prediction = model.predict(features.reshape(1, -1))[0]
    return float(prediction)
```

### Variable Type Hints

```python
from typing import Optional
import numpy as np

# Basic type annotations
confidence_threshold: float = 0.8
max_batch_size: int = 32
model_name: str = "gpt2-medium"

# Optional types (can be None)
cache: Optional[dict] = None
cached_features: Optional[np.ndarray] = None

# Collection types
feature_names: list[str] = ["age", "income", "credit_score"]
model_params: dict[str, float] = {"lr": 0.001, "momentum": 0.9}
predictions: tuple[float, float, float] = (0.1, 0.2, 0.7)
```

## 2. Protocol: Duck Typing with Type Safety

Protocols define implicit interfaces without inheritance:

```python
from typing import Protocol, runtime_checkable

@runtime_checkable
class Predictor(Protocol):
    """Protocol for objects that can make predictions.

    Any class implementing these methods satisfies the protocol,
    without explicitly inheriting from it.
    """

    def predict(self, features: list[float]) -> float:
        """Make a prediction from features."""
        ...

    def predict_batch(self, features_batch: list[list[float]]) -> list[float]:
        """Make predictions on a batch of features."""
        ...

# Classes implementing this protocol
class SKLearnModel:
    """Scikit-learn model (implicitly satisfies Predictor protocol)."""

    def predict(self, features: list[float]) -> float:
        return sum(features) / len(features)

    def predict_batch(self, features_batch: list[list[float]]) -> list[float]:
        return [self.predict(f) for f in features_batch]

class NeuralNetModel:
    """Neural network model (also satisfies Predictor protocol)."""

    def predict(self, features: list[float]) -> float:
        return sum(features) / len(features)

    def predict_batch(self, features_batch: list[list[float]]) -> list[float]:
        return [self.predict(f) for f in features_batch]

# Function accepting any Predictor
def ensemble_predict(models: list[Predictor],
                    features: list[float]) -> float:
    """Average predictions from multiple models."""
    predictions = [model.predict(features) for model in models]
    return sum(predictions) / len(predictions)

# Works with both SKLearnModel and NeuralNetModel
sk_model = SKLearnModel()
nn_model = NeuralNetModel()
ensemble_result = ensemble_predict([sk_model, nn_model], [1.0, 2.0, 3.0])
```

## 3. Generic Types for Flexible Pipelines

Use `TypeVar` and `Generic` to write flexible, type-safe pipeline code:

```python
from typing import TypeVar, Generic, Callable, Sequence

# Define type variables
InputType = TypeVar('InputType')
OutputType = TypeVar('OutputType')
StateType = TypeVar('StateType')

class Pipeline(Generic[InputType, OutputType]):
    """Generic pipeline that transforms input to output."""

    def __init__(self, transform_fn: Callable[[InputType], OutputType]):
        self.transform_fn = transform_fn

    def process(self, data: Sequence[InputType]) -> list[OutputType]:
        """Process sequence of inputs through pipeline."""
        return [self.transform_fn(item) for item in data]

# Specialized pipelines for specific types
class FeatureNormalizer(Pipeline[list[float], list[float]]):
    """Pipeline that normalizes feature lists."""

    def __init__(self):
        super().__init__(self._normalize)

    def _normalize(self, features: list[float]) -> list[float]:
        """Normalize features to [0, 1]."""
        min_val = min(features)
        max_val = max(features)
        scale = max_val - min_val or 1.0
        return [(f - min_val) / scale for f in features]

# Type-safe usage
normalizer: FeatureNormalizer = FeatureNormalizer()
raw_features = [[1.0, 5.0, 3.0], [2.0, 6.0, 4.0]]
normalized = normalizer.process(raw_features)

# Type checking catches errors
# This would be a type error:
# bad_result: str = normalizer.process(raw_features)  # Expected list[list[float]], got str
```

## 4. TypeVar with Constraints and Bounds

Restrict type variables to specific domains:

```python
from typing import TypeVar, Union

# Constrained TypeVar: only specific types allowed
NumericType = TypeVar('NumericType', int, float, complex)

def compute_mean(values: list[NumericType]) -> NumericType:
    """Compute mean of numeric values."""
    return sum(values) / len(values)  # type: ignore

# Works with int, float, complex
mean_int: int = compute_mean([1, 2, 3])
mean_float: float = compute_mean([1.0, 2.0, 3.0])

# Bounded TypeVar: base class required
from abc import ABC, abstractmethod

class MLModel(ABC):
    @abstractmethod
    def predict(self, features):
        pass

ModelType = TypeVar('ModelType', bound=MLModel)

class ModelManager(Generic[ModelType]):
    """Manage models of a specific type."""

    def __init__(self, model: ModelType):
        self.model = model

    def get_model(self) -> ModelType:
        """Return the managed model."""
        return self.model

# Type checking ensures only MLModel subclasses
```

## 5. TypedDict for Structured Responses

```python
from typing import TypedDict, NotRequired

class PredictionResponse(TypedDict):
    """Structured prediction response.

    Required fields: prediction, confidence
    Optional fields: reasoning, model_version
    """

    prediction: float
    confidence: float
    reasoning: NotRequired[str]
    model_version: NotRequired[str]

class InferenceResult(TypedDict):
    """Result from batch inference."""

    batch_id: str
    predictions: list[float]
    latency_ms: float
    model_used: str

def make_prediction(features: list[float]) -> PredictionResponse:
    """Make typed prediction response."""
    return PredictionResponse(
        prediction=0.75,
        confidence=0.92,
        reasoning="High correlation with training data",
        model_version="v2.1"
    )

def batch_inference(samples: list[list[float]]) -> InferenceResult:
    """Run batch inference with typed result."""
    return InferenceResult(
        batch_id="batch_001",
        predictions=[0.1, 0.2, 0.3],
        latency_ms=45.2,
        model_used="pytorch_v3"
    )
```

## 6. Dataclass-Based Model Configuration

```python
from dataclasses import dataclass, field
from typing import Optional

@dataclass
class ModelConfig:
    """Model configuration with type safety."""

    name: str
    learning_rate: float = 0.001
    batch_size: int = 32
    epochs: int = 10
    dropout_rate: float = 0.2
    use_cuda: bool = False
    seed: Optional[int] = None

    def validate(self) -> bool:
        """Validate configuration values."""
        assert self.learning_rate > 0, "Learning rate must be positive"
        assert self.batch_size > 0, "Batch size must be positive"
        assert 0 <= self.dropout_rate < 1, "Dropout must be in [0, 1)"
        return True

# Usage with type safety
config = ModelConfig(
    name="bert-base",
    learning_rate=0.0001,
    batch_size=16,
    use_cuda=True
)

config.validate()  # Validate before use
```

## 7. Union Types and Type Narrowing

```python
from typing import Union, Optional
import numpy as np

# Union for multiple possible types
class ArrayInput(Union[list[float], np.ndarray]):
    """Input can be Python list or NumPy array."""
    pass

def process_input(data: Union[list[float], np.ndarray]) -> np.ndarray:
    """Process various input types.

    Type narrowing allows type checker to understand control flow.
    """
    # Type narrowing: isinstance check narrows type
    if isinstance(data, np.ndarray):
        # In this branch, type is narrowed to NDArray
        return data.astype(np.float32)
    else:
        # In this branch, type is narrowed to list[float]
        return np.array(data, dtype=np.float32)

# Optional = Union[T, None]
def get_cached_result(cache_key: str) -> Optional[dict]:
    """Return cached result or None if not found."""
    cache: dict = {}

    # Safe handling with type narrowing
    result = cache.get(cache_key)

    if result is not None:
        # Type is narrowed to dict, not Optional[dict]
        return result
    else:
        return None
```

## 8. Callable Types for Function Parameters

```python
from typing import Callable, Sequence

# Define callable type aliases
PreprocessFn = Callable[[list[float]], list[float]]
PredictFn = Callable[[list[float]], float]
MetricFn = Callable[[list[float], list[float]], float]

class InferencePipeline:
    """Pipeline with pluggable components."""

    def __init__(self,
                 preprocess: PreprocessFn,
                 predict: PredictFn,
                 evaluate: Optional[MetricFn] = None):
        self.preprocess = preprocess
        self.predict = predict
        self.evaluate = evaluate

    def run(self,
            raw_data: list[float],
            ground_truth: Optional[list[float]] = None) -> dict:
        """Run inference pipeline."""
        # Preprocess
        features = self.preprocess(raw_data)

        # Predict
        prediction = self.predict(features)

        # Evaluate if provided
        metric = None
        if self.evaluate and ground_truth:
            metric = self.evaluate([prediction], ground_truth)

        return {
            "features": features,
            "prediction": prediction,
            "metric": metric
        }

# Usage with lambda functions
pipeline = InferencePipeline(
    preprocess=lambda x: [(v - min(x)) / (max(x) - min(x) + 1e-8) for v in x],
    predict=lambda x: sum(x) / len(x),
    evaluate=lambda pred, truth: abs(pred[0] - truth[0])
)
```

## 9. Using Overload for Multiple Signatures

```python
from typing import overload

class Model:
    def predict(self, features: list[float]) -> float:
        """Single prediction."""
        return sum(features) / len(features)

    def predict_batch(self, batch: list[list[float]]) -> list[float]:
        """Batch prediction."""
        return [self.predict(f) for f in batch]

# Overload: same function name, different signatures
@overload
def ensemble_predict(models: list[Model],
                    features: list[float]) -> float:
    """Single prediction from ensemble."""
    ...

@overload
def ensemble_predict(models: list[Model],
                    features: list[list[float]]) -> list[float]:
    """Batch prediction from ensemble."""
    ...

# Implementation
def ensemble_predict(models, features):
    """Ensemble prediction (single or batch)."""
    if not features:
        return [] if isinstance(features[0], list) else 0.0

    predictions = [model.predict(features)] if isinstance(features[0], (int, float)) else [model.predict_batch(features)]

    # Average results
    return sum(predictions) / len(predictions)
```

## 10. Runtime Type Checking with Pydantic

```python
from pydantic import BaseModel, Field, field_validator
from typing import Optional

class PredictionInput(BaseModel):
    """Input validation with Pydantic."""

    features: list[float] = Field(..., description="Input features")
    model_id: str = Field(..., description="Model identifier")
    confidence_threshold: float = Field(default=0.5, ge=0, le=1)
    cache_key: Optional[str] = None

    @field_validator('features')
    @classmethod
    def validate_features(cls, v):
        """Custom validation for features."""
        if len(v) == 0:
            raise ValueError("Features cannot be empty")
        if any(not isinstance(x, (int, float)) for x in v):
            raise ValueError("All features must be numeric")
        return v

# Automatic validation and type coercion
input_data = PredictionInput(
    features=[1.0, 2.0, 3.0],
    model_id="gpt2",
    confidence_threshold=0.8
)

# Invalid data raises ValidationError
try:
    bad_input = PredictionInput(
        features=[],  # Fails validation
        model_id="gpt2"
    )
except Exception as e:
    print(f"Validation error: {e}")
```

## 11. Type Checking with mypy

### Configuration (pyproject.toml)

```toml
[tool.mypy]
python_version = "3.13"
warn_return_any = true
warn_unused_configs = true
warn_redundant_casts = true
warn_unused_ignores = true
warn_no_return = true
check_untyped_defs = true
strict_optional = true
disallow_untyped_defs = true
disallow_incomplete_defs = true
no_implicit_optional = true

[[tool.mypy.overrides]]
module = "numpy.*,sklearn.*"
ignore_missing_imports = true
```

### Running mypy

```bash
# Type check entire project
mypy .

# Type check specific file
mypy src/inference.py

# Generate type stubs for external libraries
stubgen -p numpy
```

## 12. Self Type for Class Methods

```python
from typing import Self

class ModelBuilder:
    """Builder pattern with Self type for proper chaining."""

    def __init__(self, name: str):
        self.name = name
        self.params = {}

    def with_learning_rate(self, lr: float) -> Self:
        """Set learning rate and return self for chaining."""
        self.params['lr'] = lr
        return self

    def with_batch_size(self, batch_size: int) -> Self:
        """Set batch size and return self for chaining."""
        self.params['batch_size'] = batch_size
        return self

    def build(self) -> 'ModelBuilder':
        """Return configured builder."""
        return self

# Fluent API with proper typing
model = (ModelBuilder("gpt2")
         .with_learning_rate(0.001)
         .with_batch_size(32)
         .build())

# Self type ensures subclasses work correctly
class AdvancedModelBuilder(ModelBuilder):
    def with_dropout(self, rate: float) -> Self:
        """Set dropout rate."""
        self.params['dropout'] = rate
        return self

advanced = (AdvancedModelBuilder("bert")
           .with_learning_rate(0.0001)
           .with_dropout(0.2)
           .build())
```

## 13. Pattern Matching with Type Guards

```python
from typing import TypeGuard, Union
import numpy as np

def is_numpy_array(obj: Union[list, np.ndarray]) -> TypeGuard[np.ndarray]:
    """Type guard to narrow union types."""
    return isinstance(obj, np.ndarray)

def process_data(data: Union[list[float], np.ndarray]) -> float:
    """Process data with type narrowing."""
    # Type guard narrows type
    if is_numpy_array(data):
        return float(np.mean(data))
    else:
        return sum(data) / len(data)

# Match expression for pattern matching
def describe_prediction(prediction: Union[float, dict]) -> str:
    match prediction:
        case float() as value:
            return f"Simple prediction: {value}"
        case {"confidence": float() as conf, "prediction": float() as pred}:
            return f"Confident prediction: {pred} (confidence: {conf})"
        case _:
            return "Unknown prediction format"
```

## 14. IDE Integration Tips

### VS Code Configuration (.vscode/settings.json)

```json
{
    "python.linting.enabled": true,
    "python.linting.mypyEnabled": true,
    "python.linting.mypyArgs": [
        "--strict",
        "--ignore-missing-imports"
    ],
    "python.formatting.provider": "black",
    "editor.formatOnSave": true,
    "[python]": {
        "editor.defaultFormatter": "ms-python.python",
        "editor.formatOnSave": true
    }
}
```

### IntelliSense Benefits

```python
# With type hints, IDE provides:
# 1. Autocomplete suggestions
def process_model(model: Predictor):
    model.predict  # IDE suggests predict method
    model.fit      # IDE catches that Predictor doesn't have fit

# 2. Quick info on hover
scores: list[float] = []  # IDE shows list[float]

# 3. Type mismatch detection
bad_assignment: int = "string"  # IDE warns
```

## 15. Best Practices Summary

1. **Annotate function signatures completely** - Both parameters and return types
2. **Use Protocols for duck typing** - Flexible without inheritance
3. **Leverage Generic types** - Write reusable, type-safe code
4. **Validate at boundaries** - Use Pydantic for API inputs/outputs
5. **Use TypedDict for structured data** - Better than untyped dictionaries
6. **Enable strict mypy checking** - Catch errors early
7. **Document complex types** - Docstrings explain Union and Generic usage
8. **Test type checking** - Include mypy in CI/CD pipeline
9. **Use IDE warnings** - Red squiggles indicate real problems
10. **Update types with refactoring** - Keep types in sync with changes

## Conclusion

Type hints transform Python into a safer, more maintainable language, especially for large ML backends. Combined with Python 3.13's improved type system and MyPy's strict checking, you gain IDE support and early error detection without sacrificing Python's flexibility.
