---
name: dingo-evaluation
description: Guide for using Dingo, a comprehensive AI data quality evaluation tool for ML datasets, LLM training data validation, RAG system assessment, and hallucination detection. Use when evaluating dataset quality, detecting data issues, assessing RAG systems, or checking for hallucinations.
license: Complete terms in LICENSE.txt
---

# Dingo Data Quality Evaluation

Dingo is a comprehensive AI data quality evaluation tool designed for machine learning engineers, data scientists, and AI researchers. Use this skill to systematically assess and improve the quality of training data, fine-tuning datasets, and production AI systems.

## When to Use This Skill

Use Dingo evaluation when you need to:
- **Evaluate ML training datasets** - Assess completeness, validity, and quality of pre-training or fine-tuning data
- **Detect hallucinations** - Verify factual accuracy and context consistency in AI-generated content
- **Assess RAG systems** - Comprehensive evaluation of retrieval and generation quality
- **Check data quality** - Run 70+ built-in rules for text quality, format validation, PII detection
- **Custom evaluations** - Create domain-specific quality checks with custom rules

## Installation & Setup

### Quick Start

```bash
# Install Dingo
pip install dingo-python

# Verify installation
python -c "from dingo.config import InputArgs; print('Dingo installed successfully')"
```

### Optional: MCP Integration

Dingo supports Model Context Protocol (MCP) for integration with AI assistants like Claude in Cursor. For setup instructions, see [Dingo MCP documentation](https://github.com/MigoXLab/dingo/blob/main/README_mcp_zh-CN.md).

## Core Evaluation Workflows

### 1. Quick Rule-Based Evaluation

Fast, deterministic quality checks using 30+ built-in rules.

**When to use:** Initial data screening, format validation, PII detection

```python
from dingo.config import InputArgs
from dingo.exec import Executor

# Evaluate dataset with built-in rules
input_data = {
    "input_path": "data/training_data.jsonl",
    "dataset": {
        "source": "local",
        "format": "jsonl"
    },
    "executor": {
        "result_save": {"bad": True}  # Save problematic data
    },
    "evaluator": [
        {
            "fields": {"content": "text"},  # Map 'content' to 'text' field
            "evals": [
                {"name": "RuleAbnormalChar"},      # Check for abnormal characters
                {"name": "RuleSpecialCharacter"},  # Detect special characters
                {"name": "RuleColonEnd"}           # Check formatting
            ]
        }
    ]
}

input_args = InputArgs(**input_data)
executor = Executor.exec_map["local"](input_args)
result = executor.execute()

# Access results
summary = executor.get_summary()
bad_data = executor.get_bad_info_list()
```

**Available Rule Groups:**
- `default` - General text quality rules
- `sft` - Supervised fine-tuning data rules  
- `pretrain` - Pre-training data rules

**Common Rules:**
- `RuleAbnormalChar` - Unusual characters
- `RulePunctuation` - Punctuation issues
- `RuleEnterAndSpace` - Whitespace problems
- `RulePII` - Personal information detection
- `RuleIsbn` - ISBN validation (for book data)

### 2. LLM-Based Deep Evaluation

Semantic understanding using large language models.

**When to use:** Nuanced quality assessment, content relevance, helpfulness evaluation

```python
from dingo.config.input_args import EvaluatorLLMArgs
from dingo.io.input import Data
from dingo.model.llm.text_quality.llm_text_quality_v4 import LLMTextQualityV4

# Configure LLM
LLMTextQualityV4.dynamic_config = EvaluatorLLMArgs(
    key='YOUR_API_KEY',
    api_url='https://api.openai.com/v1/chat/completions',
    model='gpt-4o',
)

# Evaluate single data point
data = Data(
    data_id='123',
    prompt="Explain quantum computing",
    content="Quantum computing uses quantum bits or qubits..."
)

result = LLMTextQualityV4.eval(data)
print(f"Score: {result.score}, Issues: {result.reason}")
```

**Batch LLM Evaluation:**

```python
input_data = {
    "input_path": "data/instruction_data.jsonl",
    "dataset": {"source": "local", "format": "jsonl"},
    "executor": {"result_save": {"bad": True}},
    "evaluator": [
        {
            "fields": {
                "prompt": "instruction",
                "content": "response"
            },
            "evals": [
                {
                    "name": "LLMTextQualityV5",
                    "config": {
                        "model": "gpt-4o",
                        "key": "YOUR_API_KEY",
                        "api_url": "https://api.openai.com/v1/chat/completions"
                    }
                }
            ]
        }
    ]
}
```

### 3. Hybrid Strategy (Recommended for Production)

Combine fast rules (100% coverage) with sampled LLM checks.

**When to use:** Production pipelines, large datasets, cost-conscious evaluation

```python
input_data = {
    "input_path": "data/large_dataset.jsonl",
    "dataset": {"source": "local", "format": "jsonl"},
    "executor": {
        "result_save": {"bad": True},
        "max_workers": 4  # Parallel processing
    },
    "evaluator": [
        {
            "fields": {"content": "text"},
            "evals": [
                # Fast rules - run on all data
                {"name": "RuleAbnormalChar"},
                {"name": "RulePunctuation"},
                
                # LLM evaluation - can be sampled
                {
                    "name": "LLMTextQualityV5",
                    "config": {
                        "model": "gpt-4o-mini",  # Cost-effective model
                        "key": "YOUR_API_KEY",
                        "api_url": "https://api.openai.com/v1/chat/completions"
                    }
                }
            ]
        }
    ]
}
```

### 4. RAG System Evaluation

Comprehensive assessment of Retrieval-Augmented Generation systems using 5 academic-backed metrics.

**When to use:** Testing RAG pipelines, comparing retrieval strategies, production RAG monitoring

**Metrics:**
- **Faithfulness** - Answer-context consistency (hallucination detection)
- **Answer Relevancy** - Answer-query alignment
- **Context Precision** - Retrieval precision
- **Context Recall** - Retrieval recall  
- **Context Relevancy** - Context-query relevance

```python
input_data = {
    "input_path": "data/rag_results.jsonl",
    "dataset": {"source": "local", "format": "jsonl"},
    "evaluator": [
        {
            "fields": {
                "prompt": "user_query",
                "content": "response",
                "context": "retrieved_contexts"  # Array of retrieved passages
            },
            "evals": [
                {
                    "name": "RAGFaithfulness",
                    "config": {
                        "model": "gpt-4o",
                        "key": "YOUR_API_KEY",
                        "api_url": "https://api.openai.com/v1/chat/completions"
                    }
                },
                {"name": "RAGAnswerRelevancy"},
                {"name": "RAGContextPrecision"}
            ]
        }
    ]
}
```

**Expected Data Format for RAG:**
```json
{
  "user_query": "What is quantum entanglement?",
  "response": "Quantum entanglement is...",
  "retrieved_contexts": [
    "Context 1: Quantum mechanics describes...",
    "Context 2: Entanglement occurs when..."
  ]
}
```

### 5. Multi-Field Evaluation

Apply different quality checks to different fields in a single pass.

**When to use:** Structured data with varying field types (e.g., database tables, complex datasets)

```python
input_data = {
    "input_path": "data/books.jsonl",
    "dataset": {"source": "local", "format": "jsonl"},
    "evaluator": [
        # Validate ISBN field
        {
            "fields": {"content": "isbn"},
            "evals": [{"name": "RuleIsbn"}]
        },
        # Check title quality
        {
            "fields": {"content": "title"},
            "evals": [
                {"name": "RuleAbnormalChar"},
                {"name": "RulePunctuation"}
            ]
        },
        # Deep check on description
        {
            "fields": {"content": "description"},
            "evals": [
                {
                    "name": "LLMTextQualityV5",
                    "config": {
                        "model": "gpt-4o-mini",
                        "key": "YOUR_API_KEY"
                    }
                }
            ]
        }
    ]
}
```

## Data Source Integration

Dingo supports multiple data sources for enterprise workflows.

### Local Files

```python
input_data = {
    "input_path": "data/dataset.jsonl",  # or .csv, .txt, .parquet
    "dataset": {
        "source": "local",
        "format": "jsonl"  # or "csv", "plaintext", "parquet"
    }
}
```

### HuggingFace Datasets

```python
input_data = {
    "input_path": "tatsu-lab/alpaca",  # HuggingFace dataset ID
    "dataset": {
        "source": "hugging_face",
        "format": "plaintext"
    }
}
```

### SQL Databases (PostgreSQL, MySQL, SQLite)

Stream processing for billion-scale datasets without memory overflow.

```python
input_data = {
    "input_path": "postgresql://user:pass@localhost/dbname",
    "dataset": {
        "source": "sql",
        "query": "SELECT id, text FROM training_data WHERE quality_score IS NULL"
    },
    "evaluator": [...]
}
```

### S3 Storage

```python
input_data = {
    "input_path": "s3://bucket-name/path/to/data.jsonl",
    "dataset": {
        "source": "s3",
        "format": "jsonl"
    }
}
```

## Custom Rules & Extensions

Create domain-specific quality checks.

**Example: Empty Content Check**

```python
from dingo.model import Model
from dingo.model.rule.base import BaseRule
from dingo.io import Data
from dingo.io.output.eval_detail import EvalDetail

@Model.rule_register('QUALITY_BAD_EMPTY', ['default'])
class RuleEmptyContent(BaseRule):
    """Check if content is empty or whitespace-only"""
    
    @classmethod
    def eval(cls, input_data: Data) -> EvalDetail:
        text = input_data.content
        
        if not text or not text.strip():
            return EvalDetail(
                metric=cls.__name__,
                status=True,  # Found issue
                label=[f'{cls.metric_type}.{cls.__name__}'],
                reason=["Content is empty or whitespace-only"]
            )
        
        return EvalDetail(
            metric=cls.__name__,
            status=False,  # No issue
            label=['QUALITY_GOOD']
        )

# Use in evaluation
input_data = {
    "evaluator": [{
        "evals": [{"name": "RuleEmptyContent"}]
    }]
}
```

**See examples/custom_rule_example.py for more patterns**

## Understanding Results

After evaluation, Dingo generates:

1. **Summary Report** (`summary.json`) - Overall metrics
2. **Detailed Reports** - Issue-specific files
3. **Web GUI** - Interactive visualization (auto-generated)

### Reading Summary Results

```json
{
    "task_id": "eval_20241229_123456",
    "score": 85.5,              // Overall quality score
    "num_good": 855,             // Good data count
    "num_bad": 145,              // Problematic data count
    "total": 1000,
    "type_ratio": {              // Issue distribution
        "content": {
            "QUALITY_BAD_COMPLETENESS.RuleColonEnd": 0.08,
            "QUALITY_BAD_RELEVANCE.RuleSpecialCharacter": 0.06
        }
    }
}
```

### Accessing Results Programmatically

```python
executor = Executor.exec_map["local"](input_args)
result = executor.execute()

# Get summary statistics
summary = executor.get_summary()
print(f"Overall score: {summary['score']}%")
print(f"Issues found: {summary['num_bad']}/{summary['total']}")

# Get problematic data
bad_data = executor.get_bad_info_list()
for item in bad_data[:5]:  # First 5 issues
    print(f"ID: {item.data_id}, Issues: {item.label}, Reason: {item.reason}")

# Get high-quality data
good_data = executor.get_good_info_list()
```

### Viewing GUI Report

```bash
# Auto-generated after evaluation (if result_save.bad=True)
# Or manually start:
python -m dingo.run.vsl --input outputs/eval_20241229_123456
```

## Best Practices

### 1. Start with Rules, Then Add LLM

```python
# Phase 1: Quick screening with rules
rule_eval = {"evals": [{"name": "RuleAbnormalChar"}, {"name": "RulePII"}]}

# Phase 2: Deep check on filtered data
llm_eval = {"evals": [{"name": "LLMTextQualityV5", "config": {...}}]}
```

### 2. Use Appropriate Batch Sizes

```python
"executor": {
    "max_workers": 4,      # CPU-bound (rules): higher is better
    "batch_size": 10       # LLM calls: balance API rate limits
}
```

### 3. Save Results for Analysis

```python
"executor": {
    "result_save": {
        "bad": True,      # Save problematic data
        "good": True      # Save high-quality data (optional)
    }
}
```

### 4. Field Mapping for Complex Data

```python
"evaluator": [{
    "fields": {
        "content": "response",        # Source field -> Dingo field
        "prompt": "user_question",
        "context": "retrieved_docs"
    },
    "evals": [...]
}]
```

### 5. Cost-Effective LLM Usage

```python
# Use smaller models for simple checks
"config": {
    "model": "gpt-4o-mini",  # More cost-effective
    "key": "YOUR_API_KEY"
}

# Or local models
"config": {
    "model": "llama3:8b",
    "api_url": "http://localhost:11434/v1/chat/completions"
}
```

## Common Patterns & Examples

### Pattern 1: Pre-training Data Cleanup

```bash
# See examples/evaluate_pretraining_data.py
python examples/evaluate_pretraining_data.py --input data/raw_text.jsonl
```

### Pattern 2: RAG Pipeline Assessment

```bash
# See examples/evaluate_rag_system.py
python examples/evaluate_rag_system.py --input data/rag_outputs.jsonl
```

### Pattern 3: Custom Domain-Specific Rules

```bash
# See examples/custom_rule_example.py
python examples/custom_rule_example.py
```

## Troubleshooting

### Issue: "Module 'dingo' not found"

**Solution:** Install Dingo
```bash
pip install dingo-python
```

### Issue: LLM evaluation fails

**Solution:** Verify API configuration
```python
# Test API key separately
import openai
client = openai.OpenAI(api_key="YOUR_KEY")
response = client.chat.completions.create(
    model="gpt-4o-mini",
    messages=[{"role": "user", "content": "test"}]
)
```

### Issue: Memory errors with large datasets

**Solution:** Use streaming or Spark executor
```python
# For SQL sources, Dingo automatically streams
"dataset": {"source": "sql", "query": "..."}

# Or use Spark for distributed processing
from pyspark.sql import SparkSession
executor = Executor.exec_map["spark"](input_args, spark_session=spark)
```

## Reference Documentation

- **[examples/](examples/)** - Working code examples for common tasks
- **[Dingo Official Docs](https://github.com/MigoXLab/dingo)** - Complete Dingo documentation
- **[Dingo MCP Setup](https://github.com/MigoXLab/dingo/blob/main/README_mcp_zh-CN.md)** - MCP server configuration guide
- **[Metrics Reference](https://github.com/MigoXLab/dingo/blob/main/docs/metrics.md)** - All 70+ evaluation metrics

## Limitations & Considerations

- **LLM costs**: Deep evaluations with GPT-4 can be expensive for large datasets
- **Rate limits**: Consider API rate limits when batch processing
- **Custom rules**: Built-in rules focus on common issues; create custom rules for domain-specific needs
- **Model availability**: Some metrics require specific LLM capabilities (e.g., function calling)

## Additional Resources

- **Dingo GitHub**: https://github.com/MigoXLab/dingo
- **PyPI Package**: https://pypi.org/project/dingo-python/
- **Community**: Discord and WeChat groups (see Dingo README)
- **Academic Papers**: Referenced in [metrics documentation](https://github.com/MigoXLab/dingo/blob/main/docs/metrics.md)

