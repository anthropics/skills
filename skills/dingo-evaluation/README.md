# Dingo Evaluation Skill

A comprehensive skill for using Dingo, an AI data quality evaluation tool, to assess ML training data, RAG systems, and AI-generated content.

## Quick Start

This skill teaches Claude how to use Dingo for data quality evaluation tasks. See [SKILL.md](SKILL.md) for complete documentation.

## What's Included

- **Complete Usage Guide** - Workflows for rule-based, LLM-based, and hybrid evaluations
- **Working Examples** - Production-ready scripts for common scenarios
- **Custom Rules Guide** - Patterns for creating domain-specific quality checks
- **MCP Support** - Optional integration with Cursor (see Dingo MCP docs)

## Key Features

### Multiple Evaluation Modes

1. **Quick Rule-Based** - Fast checks with 30+ built-in rules
2. **LLM-Based Deep** - Semantic quality assessment  
3. **Hybrid Strategy** - Cost-effective combination
4. **RAG Evaluation** - Comprehensive RAG system metrics
5. **Multi-Field** - Different rules for different fields

### Data Sources Supported

- Local files (JSONL, CSV, TXT, Parquet)
- SQL databases (PostgreSQL, MySQL, SQLite)
- HuggingFace datasets
- S3 storage

## Installation

```bash
# Install Dingo
pip install dingo-python

# Optional: For MCP integration with Cursor
# See https://github.com/MigoXLab/dingo/blob/main/README_mcp_zh-CN.md
```

## Usage Examples

### Python SDK

```python
from dingo.config import InputArgs
from dingo.exec import Executor

# Quick evaluation
input_data = {
    "input_path": "training_data.jsonl",
    "dataset": {"source": "local", "format": "jsonl"},
    "evaluator": [{
        "fields": {"content": "text"},
        "evals": [
            {"name": "RuleAbnormalChar"},
            {"name": "RulePunctuation"}
        ]
    }]
}

input_args = InputArgs(**input_data)
executor = Executor.exec_map["local"](input_args)
result = executor.execute()
```

## Example Scripts

All examples are in the [examples/](examples/) directory:

- **[evaluate_pretraining_data.py](examples/evaluate_pretraining_data.py)** - Pre-training corpus quality checks
- **[evaluate_rag_system.py](examples/evaluate_rag_system.py)** - RAG system comprehensive assessment
- **[custom_rule_example.py](examples/custom_rule_example.py)** - Creating custom quality rules

Run any example with `--help` for usage instructions:

```bash
python examples/evaluate_pretraining_data.py --help
```

## Use Cases

### 1. ML Data Quality Assessment

Evaluate training datasets before expensive model training:
- Detect formatting issues
- Find PII (personally identifiable information)
- Check text completeness and coherence
- Identify duplicate or low-quality samples

### 2. RAG System Evaluation

Comprehensive assessment of retrieval-augmented generation:
- **Faithfulness**: Detect hallucinations
- **Answer Relevancy**: Query-answer alignment
- **Context Precision**: Retrieval accuracy
- **Context Recall**: Retrieval coverage
- **Context Relevancy**: Context-query relevance

### 3. Production AI Monitoring

Real-time quality checks on AI outputs:
- Ensure response quality
- Detect content drift
- Monitor compliance with guidelines
- Flag low-quality generations

### 4. Custom Domain Validation

Create organization-specific quality rules:
- Industry terminology validation
- Compliance checks
- Brand guideline enforcement
- Custom safety filters

## Documentation Structure

```
dingo-evaluation/
├── SKILL.md                    # Complete usage guide (START HERE)
├── README.md                   # This file
├── LICENSE.txt                 # Apache 2.0 license
└── examples/                   # Working code examples
    ├── evaluate_pretraining_data.py
    ├── evaluate_rag_system.py
    └── custom_rule_example.py
```

## Getting Help

- **Skill Documentation**: [SKILL.md](SKILL.md)
- **Dingo Documentation**: https://github.com/MigoXLab/dingo
- **MCP Setup**: https://github.com/MigoXLab/dingo/blob/main/README_mcp_zh-CN.md
- **Dingo Community**: https://discord.gg/Jhgb2eKWh8

## About Dingo

Dingo is an open-source AI data quality evaluation platform with:
- 70+ evaluation metrics
- Multi-source data integration
- Rule-based and LLM-based evaluation
- Production-ready scalability
- Active community and development

**GitHub**: https://github.com/MigoXLab/dingo  
**PyPI**: https://pypi.org/project/dingo-python/  
**License**: Apache 2.0

## License

This skill is licensed under the Apache License 2.0. See [LICENSE.txt](LICENSE.txt) for details.

Dingo itself is also Apache 2.0 licensed and maintained by the MigoXLab team.

