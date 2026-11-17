#!/usr/bin/env python3
"""
Example: Evaluate Pre-training Data Quality

This script demonstrates how to evaluate large-scale pre-training text data
using Dingo's built-in rules and optional LLM-based evaluation.

Supports:
- Rule-based evaluation (fast, 100% coverage)
- LLM-based evaluation (deep semantic analysis)
- Hybrid strategy (combining both approaches)

Usage:
    # Rule-based only (fast)
    python evaluate_pretraining_data.py --input data/raw_text.jsonl
    
    # With LLM evaluation (deep analysis)
    python evaluate_pretraining_data.py --input data/raw_text.jsonl --llm --api-key sk-xxx
    
    # Using environment variables
    export OPENAI_API_KEY=sk-xxx
    python evaluate_pretraining_data.py --input data/raw_text.jsonl --llm
"""

import argparse
import os
from pathlib import Path
from dingo.config import InputArgs
from dingo.exec import Executor


def evaluate_pretraining_data(
    input_path: str, 
    output_dir: str = None,
    use_llm: bool = False,
    api_key: str = None,
    model: str = "gpt-4o-mini",
    api_url: str = "https://api.openai.com/v1/chat/completions"
):
    """
    Evaluate pre-training data using rule-based and/or LLM-based evaluation.
    
    Args:
        input_path: Path to input data file (JSONL, CSV, TXT, or Parquet)
        output_dir: Optional output directory for results
        use_llm: Enable LLM-based deep evaluation
        api_key: API key for LLM (uses OPENAI_API_KEY env var if not provided)
        model: LLM model to use (default: gpt-4o-mini)
        api_url: API endpoint URL
    """
    
    # Infer format from file extension
    suffix = Path(input_path).suffix.lower()
    format_map = {
        '.jsonl': 'jsonl',
        '.json': 'json',
        '.csv': 'csv',
        '.txt': 'plaintext',
        '.parquet': 'parquet'
    }
    data_format = format_map.get(suffix, 'jsonl')
    
    print(f"📊 Evaluating pre-training data from: {input_path}")
    print(f"📝 Format: {data_format}")
    print(f"🤖 LLM evaluation: {'Enabled' if use_llm else 'Disabled (rule-based only)'}")
    
    if use_llm:
        if not api_key:
            api_key = os.environ.get('OPENAI_API_KEY')
            if not api_key:
                raise ValueError(
                    "API key required for LLM evaluation. "
                    "Provide --api-key or set OPENAI_API_KEY environment variable."
                )
        print(f"🔑 Using model: {model}")
    
    # Configure rule-based evaluation
    evaluator_config = [
        {
            "eval_group_name": "pretrain",  # Use pretrain rule group
            "fields": {"content": "text"},   # Adjust based on your data
            "evals": [
                # Fast rule-based checks (run on all data)
                {"name": "RuleAbnormalChar"},      # Detect unusual characters
                {"name": "RulePunctuation"},       # Check punctuation issues
                {"name": "RuleEnterAndSpace"},     # Whitespace problems
                {"name": "RuleSpecialCharacter"},  # Special character issues
                {"name": "RulePII"},               # Personal information detection
            ]
        }
    ]
    
    # Add LLM-based evaluation if requested
    if use_llm:
        llm_config = {
            "model": model,
            "key": api_key,
            "api_url": api_url
        }
        
        # Add LLM evaluator for deep semantic quality checks
        evaluator_config.append({
            "fields": {"content": "text"},
            "evals": [
                {
                    "name": "LLMTextQualityV5",  # Deep quality assessment
                    "config": llm_config
                }
            ]
        })
        
        print("💡 Hybrid strategy: Fast rules (100% coverage) + LLM (deep analysis)")
    
    input_data = {
        "input_path": input_path,
        "dataset": {
            "source": "local",
            "format": data_format
        },
        "executor": {
            "result_save": {
                "bad": True,   # Save problematic data
                "good": False  # Don't save good data (save space)
            },
            "max_workers": 4 if not use_llm else 2,  # Lower for API rate limits
            "batch_size": 10  # Batch size for processing
        },
        "evaluator": evaluator_config
    }
    
    # Override output directory if specified
    if output_dir:
        input_data["output_dir"] = output_dir
    
    # Run evaluation
    print("\n🔍 Running evaluation...")
    input_args = InputArgs(**input_data)
    executor = Executor.exec_map["local"](input_args)
    result = executor.execute()
    
    # Get and display summary
    summary = executor.get_summary()
    bad_data = executor.get_bad_info_list()
    
    print("\n" + "="*60)
    print("📈 EVALUATION RESULTS")
    print("="*60)
    print(f"Overall Quality Score: {summary['score']:.2f}%")
    print(f"Total Records: {summary['total']}")
    print(f"✅ Good Records: {summary['num_good']}")
    print(f"❌ Problematic Records: {summary['num_bad']}")
    
    if summary.get('type_ratio'):
        print("\n📋 Issue Distribution:")
        for field, issues in summary['type_ratio'].items():
            print(f"\n  Field: {field}")
            for issue_type, ratio in sorted(issues.items(), key=lambda x: x[1], reverse=True):
                count = int(ratio * summary['total'])
                print(f"    - {issue_type}: {count} ({ratio*100:.1f}%)")
    
    # Show sample issues
    if bad_data:
        print("\n⚠️  Sample Issues (first 5):")
        for i, item in enumerate(bad_data[:5], 1):
            print(f"\n  {i}. ID: {item.data_id}")
            print(f"     Issues: {', '.join(item.label)}")
            print(f"     Reason: {item.reason[0] if item.reason else 'N/A'}")
            if hasattr(item, 'content') and item.content:
                preview = item.content[:100] + "..." if len(item.content) > 100 else item.content
                print(f"     Preview: {preview}")
    
    print(f"\n💾 Results saved to: {summary.get('output_path', 'outputs/')}")
    print("\n💡 To view interactive GUI:")
    print(f"   python -m dingo.run.vsl --input {summary.get('output_path', 'outputs/')}")
    
    return summary


def main():
    parser = argparse.ArgumentParser(
        description="Evaluate pre-training data quality using Dingo (rules + optional LLM)",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Quick rule-based check (fast, no API costs)
  python evaluate_pretraining_data.py --input data/raw_text.jsonl
  
  # Add LLM deep evaluation (requires API key)
  python evaluate_pretraining_data.py --input data/raw_text.jsonl --llm --api-key sk-xxx
  
  # Use environment variable for API key
  export OPENAI_API_KEY=sk-xxx
  python evaluate_pretraining_data.py --input data/raw_text.jsonl --llm
  
  # Use different model
  python evaluate_pretraining_data.py --input data/raw_text.jsonl --llm --model gpt-4o
  
  # Use local model (e.g., Ollama)
  python evaluate_pretraining_data.py --input data/raw_text.jsonl --llm \\
      --model llama3:8b --api-url http://localhost:11434/v1/chat/completions
  
  # Custom output directory
  python evaluate_pretraining_data.py --input data/raw_text.jsonl --output results/
        """
    )
    
    parser.add_argument(
        '--input',
        required=True,
        help='Input data file path (JSONL, CSV, TXT, Parquet)'
    )
    
    parser.add_argument(
        '--output',
        help='Output directory for results (default: auto-generated in outputs/)'
    )
    
    parser.add_argument(
        '--llm',
        action='store_true',
        help='Enable LLM-based deep evaluation (requires API key)'
    )
    
    parser.add_argument(
        '--api-key',
        help='API key for LLM (or set OPENAI_API_KEY env var)'
    )
    
    parser.add_argument(
        '--model',
        default='gpt-4o-mini',
        help='LLM model to use (default: gpt-4o-mini, cost-effective)'
    )
    
    parser.add_argument(
        '--api-url',
        default='https://api.openai.com/v1/chat/completions',
        help='API endpoint URL (default: OpenAI)'
    )
    
    parser.add_argument(
        '--hf',
        action='store_true',
        help='Input is a HuggingFace dataset ID'
    )
    
    args = parser.parse_args()
    
    # Modify input config for HuggingFace datasets
    if args.hf:
        print("📦 Loading from HuggingFace...")
        # This would require additional handling for HF datasets
        # For now, we'll just process as local
    
    evaluate_pretraining_data(
        input_path=args.input,
        output_dir=args.output,
        use_llm=args.llm,
        api_key=args.api_key,
        model=args.model,
        api_url=args.api_url
    )


if __name__ == "__main__":
    main()

