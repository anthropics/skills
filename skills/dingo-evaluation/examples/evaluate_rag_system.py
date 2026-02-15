#!/usr/bin/env python3
"""
Example: Evaluate RAG (Retrieval-Augmented Generation) System

This script demonstrates comprehensive evaluation of RAG systems using 5
academic-backed metrics: Faithfulness, Answer Relevancy, Context Precision,
Context Recall, and Context Relevancy.

Expected input format (JSONL):
{
  "user_query": "What is quantum entanglement?",
  "response": "Quantum entanglement is a phenomenon...",
  "retrieved_contexts": [
    "Context 1: Quantum mechanics describes...",
    "Context 2: Entanglement occurs when..."
  ]
}

Usage:
    python evaluate_rag_system.py --input data/rag_outputs.jsonl --api-key YOUR_KEY
    python evaluate_rag_system.py --input data/rag_outputs.jsonl --metrics faithfulness answer_relevancy
"""

import argparse
import os
import json
from pathlib import Path
from dingo.config import InputArgs
from dingo.exec import Executor


# Available RAG metrics and their descriptions
RAG_METRICS = {
    'faithfulness': {
        'class': 'RAGFaithfulness',
        'description': 'Measures if the answer is consistent with retrieved contexts (hallucination detection)'
    },
    'answer_relevancy': {
        'class': 'RAGAnswerRelevancy',
        'description': 'Evaluates how well the answer addresses the user query'
    },
    'context_precision': {
        'class': 'RAGContextPrecision',
        'description': 'Assesses precision of retrieved contexts (relevant vs. irrelevant)'
    },
    'context_recall': {
        'class': 'RAGContextRecall',
        'description': 'Measures recall of retrieved contexts (coverage of needed information)'
    },
    'context_relevancy': {
        'class': 'RAGContextRelevancy',
        'description': 'Evaluates relevance of retrieved contexts to the user query'
    }
}


def evaluate_rag_system(
    input_path: str,
    api_key: str,
    metrics: list = None,
    model: str = "gpt-4o",
    output_dir: str = None
):
    """
    Evaluate RAG system using specified metrics.
    
    Args:
        input_path: Path to RAG output data (JSONL format)
        api_key: OpenAI API key
        metrics: List of metrics to evaluate (default: all)
        model: LLM model to use
        output_dir: Optional output directory
    """
    
    if metrics is None:
        metrics = list(RAG_METRICS.keys())
    
    print(f"📊 Evaluating RAG system from: {input_path}")
    print(f"🔑 Using model: {model}")
    print(f"📏 Metrics: {', '.join(metrics)}")
    
    # Build evaluator configuration
    evals_config = []
    for metric_name in metrics:
        if metric_name not in RAG_METRICS:
            print(f"⚠️  Unknown metric: {metric_name}, skipping")
            continue
        
        metric_info = RAG_METRICS[metric_name]
        evals_config.append({
            "name": metric_info['class'],
            "config": {
                "model": model,
                "key": api_key,
                "api_url": "https://api.openai.com/v1/chat/completions"
            }
        })
    
    if not evals_config:
        raise ValueError("No valid metrics specified")
    
    input_data = {
        "input_path": input_path,
        "dataset": {
            "source": "local",
            "format": "jsonl"
        },
        "executor": {
            "result_save": {
                "bad": True,
                "good": True
            },
            "max_workers": 2,  # Lower for API rate limiting
            "batch_size": 5
        },
        "evaluator": [
            {
                "fields": {
                    "prompt": "user_query",
                    "content": "response",
                    "context": "retrieved_contexts"
                },
                "evals": evals_config
            }
        ]
    }
    
    if output_dir:
        input_data["output_dir"] = output_dir
    
    # Run evaluation
    print("\n🔍 Running RAG evaluation...")
    print("⏳ This may take a while for large datasets...")
    
    input_args = InputArgs(**input_data)
    executor = Executor.exec_map["local"](input_args)
    result = executor.execute()
    
    # Display results
    summary = executor.get_summary()
    
    print("\n" + "="*60)
    print("📈 RAG SYSTEM EVALUATION RESULTS")
    print("="*60)
    print(f"Overall Score: {summary['score']:.2f}%")
    print(f"Total Queries Evaluated: {summary['total']}")
    print(f"✅ High Quality Responses: {summary['num_good']}")
    print(f"❌ Need Review: {summary['num_bad']}")
    
    # Display metric-specific results
    if summary.get('type_ratio'):
        print("\n📊 Metric Breakdown:")
        for field, issues in summary['type_ratio'].items():
            print(f"\n  Field: {field}")
            for issue_type, ratio in sorted(issues.items(), key=lambda x: x[1], reverse=True):
                count = int(ratio * summary['total'])
                
                # Try to identify which metric this is
                metric_name = "Unknown"
                for key, info in RAG_METRICS.items():
                    if info['class'] in issue_type:
                        metric_name = key.replace('_', ' ').title()
                        break
                
                print(f"    - {metric_name}: {count} issues ({ratio*100:.1f}%)")
    
    # Show examples with issues
    bad_data = executor.get_bad_info_list()
    if bad_data:
        print("\n⚠️  Examples with Issues (first 3):")
        for i, item in enumerate(bad_data[:3], 1):
            print(f"\n  {i}. Query: {getattr(item, 'prompt', 'N/A')[:80]}...")
            print(f"     Response: {getattr(item, 'content', 'N/A')[:80]}...")
            print(f"     Issues: {', '.join(item.label)}")
            if item.reason:
                print(f"     Details: {item.reason[0][:100]}...")
    
    # Show good examples
    good_data = executor.get_good_info_list()
    if good_data:
        print(f"\n✅ Found {len(good_data)} high-performing queries")
        print("\n💡 Example of good response:")
        example = good_data[0]
        print(f"   Query: {getattr(example, 'prompt', 'N/A')[:80]}...")
        print(f"   Response: {getattr(example, 'content', 'N/A')[:100]}...")
    
    print(f"\n💾 Results saved to: {summary.get('output_path', 'outputs/')}")
    print("\n📋 Next steps:")
    print("   1. Review queries with low scores")
    print("   2. Check if retrieval is returning relevant contexts")
    print("   3. Analyze if generation is faithful to contexts")
    print("   4. View interactive report:")
    print(f"      python -m dingo.run.vsl --input {summary.get('output_path', 'outputs/')}")
    
    return summary


def validate_input_format(input_path: str) -> bool:
    """
    Validate that input file has expected RAG format.
    """
    print("\n🔍 Validating input format...")
    
    required_fields = {'user_query', 'response', 'retrieved_contexts'}
    
    try:
        with open(input_path, 'r') as f:
            first_line = f.readline()
            data = json.loads(first_line)
            
            missing_fields = required_fields - set(data.keys())
            if missing_fields:
                print(f"❌ Missing required fields: {missing_fields}")
                print(f"   Expected fields: {required_fields}")
                print(f"   Found fields: {set(data.keys())}")
                return False
            
            # Check if retrieved_contexts is a list
            if not isinstance(data['retrieved_contexts'], list):
                print(f"❌ 'retrieved_contexts' must be a list of strings")
                return False
            
            print("✅ Input format validated")
            return True
    
    except json.JSONDecodeError:
        print(f"❌ Invalid JSON format")
        return False
    except Exception as e:
        print(f"❌ Validation error: {e}")
        return False


def main():
    parser = argparse.ArgumentParser(
        description="Evaluate RAG system quality with academic-backed metrics",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Available Metrics:
  faithfulness        - Answer-context consistency (hallucination detection)
  answer_relevancy    - Answer-query alignment
  context_precision   - Retrieval precision
  context_recall      - Retrieval recall
  context_relevancy   - Context-query relevance

Examples:
  # Evaluate all metrics
  python evaluate_rag_system.py --input data/rag_outputs.jsonl --api-key sk-xxx
  
  # Evaluate specific metrics
  python evaluate_rag_system.py --input data/rag_outputs.jsonl --api-key sk-xxx \\
      --metrics faithfulness answer_relevancy
  
  # Use different model
  python evaluate_rag_system.py --input data/rag_outputs.jsonl --api-key sk-xxx \\
      --model gpt-4o-mini
  
  # Use environment variable for API key
  export OPENAI_API_KEY=sk-xxx
  python evaluate_rag_system.py --input data/rag_outputs.jsonl
        """
    )
    
    parser.add_argument(
        '--input',
        required=True,
        help='Input JSONL file with RAG outputs'
    )
    
    parser.add_argument(
        '--api-key',
        help='OpenAI API key (or set OPENAI_API_KEY env var)'
    )
    
    parser.add_argument(
        '--metrics',
        nargs='+',
        choices=list(RAG_METRICS.keys()),
        help='Metrics to evaluate (default: all)'
    )
    
    parser.add_argument(
        '--model',
        default='gpt-4o',
        help='LLM model to use (default: gpt-4o)'
    )
    
    parser.add_argument(
        '--output',
        help='Output directory for results'
    )
    
    parser.add_argument(
        '--skip-validation',
        action='store_true',
        help='Skip input format validation'
    )
    
    args = parser.parse_args()
    
    # Get API key
    api_key = args.api_key or os.environ.get('OPENAI_API_KEY')
    if not api_key:
        parser.error(
            "API key required. Provide --api-key or set OPENAI_API_KEY environment variable."
        )
    
    # Validate input format
    if not args.skip_validation:
        if not validate_input_format(args.input):
            print("\n💡 Tip: Use --skip-validation to bypass this check")
            return 1
    
    # Run evaluation
    evaluate_rag_system(
        input_path=args.input,
        api_key=api_key,
        metrics=args.metrics,
        model=args.model,
        output_dir=args.output
    )
    
    return 0


if __name__ == "__main__":
    exit(main())

