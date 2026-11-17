#!/usr/bin/env python3
"""
Example: Creating Custom Dingo Rules

This script demonstrates how to create custom domain-specific quality rules
for Dingo evaluation. Custom rules allow you to enforce your organization's
specific data quality standards.

Usage:
    python custom_rule_example.py
"""

from dingo.model import Model
from dingo.model.rule.base import BaseRule
from dingo.io import Data
from dingo.io.output.eval_detail import EvalDetail
from dingo.config import InputArgs
from dingo.exec import Executor


# Example 1: Simple empty content check
@Model.rule_register('QUALITY_BAD_EMPTY', ['default'])
class RuleEmptyContent(BaseRule):
    """Check if content is empty or whitespace-only"""
    
    @classmethod
    def eval(cls, input_data: Data) -> EvalDetail:
        text = input_data.content
        
        if not text or not text.strip():
            return EvalDetail(
                metric=cls.__name__,
                status=True,  # Found an issue
                label=[f'{cls.metric_type}.{cls.__name__}'],
                reason=["Content is empty or whitespace-only"]
            )
        
        return EvalDetail(
            metric=cls.__name__,
            status=False,  # No issue found
            label=['QUALITY_GOOD']
        )


# Example 2: Minimum length requirement
@Model.rule_register('QUALITY_BAD_LENGTH', ['default'])
class RuleMinimumLength(BaseRule):
    """Check if content meets minimum length requirement"""
    
    MIN_LENGTH = 50  # Configurable minimum length
    
    @classmethod
    def eval(cls, input_data: Data) -> EvalDetail:
        text = input_data.content
        
        if not text:
            length = 0
        else:
            length = len(text.strip())
        
        if length < cls.MIN_LENGTH:
            return EvalDetail(
                metric=cls.__name__,
                status=True,
                label=[f'{cls.metric_type}.{cls.__name__}'],
                reason=[f"Content too short: {length} chars (minimum: {cls.MIN_LENGTH})"]
            )
        
        return EvalDetail(
            metric=cls.__name__,
            status=False,
            label=['QUALITY_GOOD']
        )


# Example 3: Domain-specific keyword check
@Model.rule_register('QUALITY_BAD_KEYWORDS', ['default'])
class RuleForbiddenKeywords(BaseRule):
    """Check for forbidden keywords or phrases"""
    
    # Define your forbidden keywords
    FORBIDDEN_KEYWORDS = {
        'placeholder', 'todo', 'fixme', 'tbd', 'lorem ipsum',
        'test test', '[insert', 'xxx', 'yyy'
    }
    
    @classmethod
    def eval(cls, input_data: Data) -> EvalDetail:
        text = input_data.content
        
        if not text:
            return EvalDetail(
                metric=cls.__name__,
                status=False,
                label=['QUALITY_GOOD']
            )
        
        text_lower = text.lower()
        found_keywords = []
        
        for keyword in cls.FORBIDDEN_KEYWORDS:
            if keyword in text_lower:
                found_keywords.append(keyword)
        
        if found_keywords:
            return EvalDetail(
                metric=cls.__name__,
                status=True,
                label=[f'{cls.metric_type}.{cls.__name__}'],
                reason=[f"Found forbidden keywords: {', '.join(found_keywords)}"]
            )
        
        return EvalDetail(
            metric=cls.__name__,
            status=False,
            label=['QUALITY_GOOD']
        )


# Example 4: Pattern-based validation (e.g., email, phone)
@Model.rule_register('QUALITY_BAD_FORMAT', ['default'])
class RuleEmailFormat(BaseRule):
    """Validate email format in content marked as 'email' field"""
    
    import re
    EMAIL_PATTERN = re.compile(r'^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$')
    
    @classmethod
    def eval(cls, input_data: Data) -> EvalDetail:
        text = input_data.content
        
        if not text:
            return EvalDetail(
                metric=cls.__name__,
                status=True,
                label=[f'{cls.metric_type}.{cls.__name__}'],
                reason=["Email field is empty"]
            )
        
        if not cls.EMAIL_PATTERN.match(text.strip()):
            return EvalDetail(
                metric=cls.__name__,
                status=True,
                label=[f'{cls.metric_type}.{cls.__name__}'],
                reason=[f"Invalid email format: {text}"]
            )
        
        return EvalDetail(
            metric=cls.__name__,
            status=False,
            label=['QUALITY_GOOD']
        )


# Example 5: Multi-field validation
@Model.rule_register('QUALITY_BAD_CONSISTENCY', ['default'])
class RulePromptResponseConsistency(BaseRule):
    """Check if response is too similar to prompt (copy-paste detection)"""
    
    SIMILARITY_THRESHOLD = 0.8
    
    @classmethod
    def eval(cls, input_data: Data) -> EvalDetail:
        prompt = input_data.prompt
        content = input_data.content
        
        if not prompt or not content:
            return EvalDetail(
                metric=cls.__name__,
                status=False,
                label=['QUALITY_GOOD']
            )
        
        # Simple similarity check (Jaccard similarity)
        prompt_words = set(prompt.lower().split())
        content_words = set(content.lower().split())
        
        if not prompt_words or not content_words:
            return EvalDetail(
                metric=cls.__name__,
                status=False,
                label=['QUALITY_GOOD']
            )
        
        intersection = len(prompt_words & content_words)
        union = len(prompt_words | content_words)
        similarity = intersection / union if union > 0 else 0
        
        if similarity > cls.SIMILARITY_THRESHOLD:
            return EvalDetail(
                metric=cls.__name__,
                status=True,
                label=[f'{cls.metric_type}.{cls.__name__}'],
                reason=[f"Response too similar to prompt (similarity: {similarity:.2f})"]
            )
        
        return EvalDetail(
            metric=cls.__name__,
            status=False,
            label=['QUALITY_GOOD']
        )


def demo_custom_rules():
    """
    Demonstrate using custom rules in evaluation
    """
    
    print("="*60)
    print("CUSTOM DINGO RULES DEMO")
    print("="*60)
    
    # Test data
    test_data = [
        Data(data_id='1', content='This is a good quality text with sufficient length.'),
        Data(data_id='2', content=''),  # Empty
        Data(data_id='3', content='Short'),  # Too short
        Data(data_id='4', content='This text contains a TODO placeholder that should be flagged.'),
        Data(data_id='5', content='test@example.com'),  # For email validation
        Data(data_id='6', content='invalid-email'),  # Invalid email
        Data(
            data_id='7',
            prompt='What is AI?',
            content='What is AI? That is a great question.'  # Too similar
        ),
    ]
    
    # Test each rule
    rules = [
        RuleEmptyContent,
        RuleMinimumLength,
        RuleForbiddenKeywords,
        RuleEmailFormat,
        RulePromptResponseConsistency
    ]
    
    print("\n📋 Testing Custom Rules:\n")
    
    for rule_class in rules:
        print(f"\n{rule_class.__name__}:")
        print(f"  Description: {rule_class.__doc__.strip()}")
        print(f"  Results:")
        
        for data in test_data:
            result = rule_class.eval(data)
            if result.status:  # Has issue
                print(f"    ❌ ID {data.data_id}: {result.reason[0] if result.reason else 'Issue found'}")
            else:
                print(f"    ✅ ID {data.data_id}: Passed")
    
    print("\n" + "="*60)
    print("BATCH EVALUATION WITH CUSTOM RULES")
    print("="*60)
    
    # Create a test JSONL file
    import json
    import tempfile
    
    test_file = tempfile.NamedTemporaryFile(mode='w', suffix='.jsonl', delete=False)
    test_data_dicts = [
        {'id': '1', 'text': 'This is good quality content.'},
        {'id': '2', 'text': ''},
        {'id': '3', 'text': 'Short'},
        {'id': '4', 'text': 'Contains TODO placeholder'},
    ]
    
    for item in test_data_dicts:
        test_file.write(json.dumps(item) + '\n')
    test_file.close()
    
    # Run batch evaluation with custom rules
    input_data = {
        "input_path": test_file.name,
        "dataset": {
            "source": "local",
            "format": "jsonl"
        },
        "executor": {
            "result_save": {"bad": True}
        },
        "evaluator": [
            {
                "fields": {"content": "text"},
                "evals": [
                    {"name": "RuleEmptyContent"},
                    {"name": "RuleMinimumLength"},
                    {"name": "RuleForbiddenKeywords"}
                ]
            }
        ]
    }
    
    print(f"\n🔍 Running batch evaluation with custom rules...")
    input_args = InputArgs(**input_data)
    executor = Executor.exec_map["local"](input_args)
    result = executor.execute()
    
    summary = executor.get_summary()
    print(f"\n📊 Results:")
    print(f"  Overall Score: {summary['score']:.2f}%")
    print(f"  Total: {summary['total']}")
    print(f"  Good: {summary['num_good']}")
    print(f"  Bad: {summary['num_bad']}")
    
    # Cleanup
    import os
    os.unlink(test_file.name)
    
    print("\n💡 Integration Tips:")
    print("   1. Place custom rules in a separate module (e.g., my_rules.py)")
    print("   2. Import the module before running evaluation")
    print("   3. Rules are automatically registered via @Model.rule_register decorator")
    print("   4. Use meaningful metric_type categories (e.g., 'QUALITY_BAD_EMPTY')")
    print("   5. Provide clear, actionable reason messages")
    
    print("\n📚 Learn More:")
    print("   - Dingo rule base class: dingo/model/rule/base.py")
    print("   - Built-in rules: dingo/model/rule/")
    print("   - Registration system: dingo/model/model.py")


def main():
    """
    Main entry point
    """
    demo_custom_rules()


if __name__ == "__main__":
    main()

