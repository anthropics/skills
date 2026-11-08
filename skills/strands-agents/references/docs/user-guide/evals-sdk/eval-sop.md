# Eval SOP - AI-Powered Evaluation Workflow

## Overview

Eval SOP is an AI-powered assistant that transforms the complex process of agent evaluation from a manual, error-prone task into a structured, high-quality workflow. Built as an Agent SOP (Standard Operating Procedure), it guides you through the entire evaluation lifecycle—from planning and test data generation to evaluation execution and reporting.

## Why Agent Evaluation is Challenging

Designing effective agent evaluations is notoriously difficult and time-consuming:

### **Evaluation Design Complexity**

- **Metric Selection**: Choosing appropriate evaluators (output quality, trajectory analysis, helpfulness) requires deep understanding of evaluation theory
- **Test Case Coverage**: Creating comprehensive test cases that cover edge cases, failure modes, and diverse scenarios is labor-intensive
- **Evaluation Bias**: Manual evaluation design often reflects creator assumptions rather than real-world usage patterns
- **Inconsistent Standards**: Different team members create evaluations with varying quality and coverage

### **Technical Implementation Barriers**

- **SDK Learning Curve**: Understanding Strands Evaluation SDK APIs, evaluator configurations, and best practices
- **Code Generation**: Writing evaluation scripts requires both evaluation expertise and programming skills
- **Integration Complexity**: Connecting agents, evaluators, test data, and reporting into cohesive workflows

### **Quality and Reliability Issues**

- **Incomplete Coverage**: Manual test case creation often misses critical scenarios
- **Evaluation Drift**: Ad-hoc evaluation approaches lead to inconsistent results over time
- **Poor Documentation**: Evaluation rationale and methodology often poorly documented
- **Reproducibility**: Manual processes are difficult to replicate across teams and projects

## How Eval SOP Solves These Problems

Eval SOP addresses these challenges through AI-powered automation and structured workflows:

### **Intelligent Evaluation Planning**

- **Automated Analysis**: Analyzes your agent architecture and requirements to recommend appropriate evaluation strategies
- **Comprehensive Coverage**: Generates evaluation plans that systematically cover functionality, edge cases, and failure modes
- **Best Practice Integration**: Applies evaluation methodology best practices automatically
- **Stakeholder Alignment**: Creates clear evaluation plans that technical and non-technical stakeholders can understand

### **High-Quality Test Data Generation**

- **Scenario-Based Generation**: Creates realistic test cases aligned with actual usage patterns
- **Edge Case Discovery**: Automatically identifies and generates tests for boundary conditions and failure scenarios
- **Diverse Coverage**: Ensures test cases span different difficulty levels, input types, and expected behaviors
- **Contextual Relevance**: Generates test data specific to your agent's domain and capabilities

### **Expert-Level Implementation**

- **Code Generation**: Automatically writes evaluation scripts using Strands Evaluation SDK best practices
- **Evaluator Selection**: Intelligently chooses and configures appropriate evaluators for your use case
- **Integration Handling**: Manages the complexity of connecting agents, evaluators, and test data
- **Error Recovery**: Provides debugging guidance when evaluation execution encounters issues

### **Professional Reporting**

- **Actionable Insights**: Generates reports with specific recommendations for agent improvement
- **Trend Analysis**: Identifies patterns in agent performance across different scenarios
- **Stakeholder Communication**: Creates reports suitable for both technical teams and business stakeholders
- **Reproducible Results**: Documents methodology and configuration for future reference

## What is Eval SOP?

Eval SOP is implemented as an [Agent SOP](https://github.com/strands-agents/agent-sop)—a markdown-based standard for encoding AI agent workflows as natural language instructions with parameterized inputs and constraint-based execution. This approach provides:

- **Structured Workflow**: Four-phase process (Plan → Data → Eval → Report) with clear entry conditions and success criteria
- **RFC 2119 Constraints**: Uses MUST, SHOULD, MAY constraints to ensure reliable execution while preserving AI reasoning
- **Multi-Modal Distribution**: Available through MCP servers, Anthropic Skills, and direct integration
- **Reproducible Process**: Standardized workflow that produces consistent results across different AI assistants

## Installation and Setup

### Install strands-agents-sops

```bash
# Using pip
pip install strands-agents-sops

# Or using Homebrew
brew install strands-agents-sops
```

### Setup Evaluation Project

Create a self-contained evaluation workspace:

```bash
mkdir agent-evaluation-project
cd agent-evaluation-project

# Copy your agent to evaluate (must be self-contained)
cp -r /path/to/your/agent .
```

Expected structure:
```
agent-evaluation-project/
├── your-agent/           # Agent to evaluate
├── evals-main/          # Strands Evals SDK (optional)
└── eval/                # Generated evaluation artifacts
    ├── eval-plan.md
    ├── test-cases.jsonl
    ├── results/
    ├── run_evaluation.py
    └── eval-report.md
```

## Usage Options

### Option 1: MCP Integration (Recommended)

Set up MCP server for AI assistant integration:

```bash
# Download Eval SOP
mkdir ~/my-sops
# Copy eval.sop.md to ~/my-sops/

# Configure MCP server
strands-agents-sops mcp --sop-paths ~/my-sops
```

Add to your AI assistant's MCP configuration:
```json
{
  "mcpServers": {
    "Eval": {
      "command": "strands-agents-sops",
      "args": ["mcp", "--sop-paths", "~/my-sops"]
    }
  }
}
```

#### Usage with Claude Code

```bash
cd agent-evaluation-project
claude

# In Claude session:
 /my-sops:eval (MCP) generate an evaluation plan for this agent at ./your-agent using strands evals sdk at ./evals-main
```

The workflow proceeds through four phases:

1. **Planning**: `/Eval generate an evaluation plan`
2. **Data Generation**: `yes` (when prompted) or `/Eval generate the test data`
3. **Evaluation**: `yes` (when prompted) or `/Eval evaluate the agent using strands evals`
4. **Reporting**: `/Eval generate an evaluation report based on /path/to/results.json`

### Option 2: Direct Strands Agent Integration

```python
from strands import Agent
from strands_tools import editor, shell
from strands_agents_sops import eval 

agent = Agent(
    system_prompt=eval,
    tools=[editor, shell],
)

# Initial message to start the evaluation
agent("Start Eval sop for evaluating my QA agent")

# Multi-turn conversation loop
while True:
    user_input = input("\nYou: ")
    if user_input.lower() in ("exit", "quit", "done"):
        print("Evaluation session ended.")
        break

    agent(user_input)
```

You can bypass tool consent when running Eval SOP by setting the following environment variable:

```python
import os 

os.environ["BYPASS_TOOL_CONSENT"] = "true"
```

### Option 3: Anthropic Skills

Convert to Claude Skills format:

```bash
strands-agents-sops skills --sop-paths ~/my-sops --output-dir ./skills
```

Upload the generated `skills/eval/SKILL.md` to Claude.ai or use via Claude API.

## Evaluation Workflow

### Phase 1: Intelligent Planning

Eval analyzes your agent and creates a comprehensive evaluation plan:

- **Architecture Analysis**: Examines agent code, tools, and capabilities
- **Use Case Identification**: Determines primary and secondary use cases
- **Evaluator Selection**: Recommends appropriate evaluators (output, trajectory, helpfulness)
- **Success Criteria**: Defines measurable success metrics
- **Risk Assessment**: Identifies potential failure modes and edge cases

**Output**: `eval/eval-plan.md` with structured evaluation methodology

### Phase 2: Test Data Generation

Creates high-quality, diverse test cases:

- **Scenario Coverage**: Generates tests for normal operation, edge cases, and failure modes
- **Difficulty Gradation**: Creates tests ranging from simple to complex scenarios
- **Domain Relevance**: Ensures test cases match your agent's intended use cases
- **Bias Mitigation**: Generates diverse inputs to avoid evaluation bias

**Output**: `eval/test-cases.jsonl` with structured test cases

### Phase 3: Evaluation Execution

Implements and runs comprehensive evaluations:

- **Script Generation**: Creates evaluation scripts using Strands Evaluation SDK best practices
- **Evaluator Configuration**: Properly configures evaluators with appropriate rubrics and parameters
- **Execution Management**: Handles evaluation execution with error recovery
- **Results Collection**: Aggregates results across all test cases and evaluators

**Output**: `eval/results/` directory with detailed evaluation data

### Phase 4: Actionable Reporting

Generates insights and recommendations:

- **Performance Analysis**: Analyzes results across different dimensions and scenarios
- **Failure Pattern Identification**: Identifies common failure modes and their causes
- **Improvement Recommendations**: Provides specific, actionable suggestions for agent enhancement
- **Stakeholder Communication**: Creates reports suitable for different audiences

**Output**: `eval/eval-report.md` with comprehensive analysis and recommendations

## Example Output

### Generated Evaluation Plan

The evaluation plan follows a comprehensive structured format with detailed analysis and implementation guidance:

```markdown
# Evaluation Plan for QA+Search Agent

## 1. Evaluation Requirements
- **User Input:** "generate an evaluation plan for this qa agent..."
- **Interpreted Evaluation Requirements:** Evaluate the QA agent's ability to answer questions using web search capabilities...

## 2. Agent Analysis
| **Attribute**         | **Details**                                                 |
| :-------------------- | :---------------------------------------------------------- |
| **Agent Name**        | QA+Search                                                   |
| **Purpose**           | Answer questions by searching the web using Tavily API... |
| **Core Capabilities** | Web search integration, information synthesis...            |

**Agent Architecture Diagram:**
(Mermaid diagram showing User Query → Agent → WebSearchTool → Tavily API flow)

## 3. Evaluation Metrics
### Answer Quality Score
- **Evaluation Area:** Final response quality
- **Method:** LLM-as-Judge (using OutputEvaluator with custom rubric)
- **Scoring Scale:** 0.0 to 1.0
- **Pass Threshold:** 0.75 or higher

## 4. Test Data Generation
- **Simple Factual Questions**: Questions requiring basic web search...
- **Multi-Step Reasoning Questions**: Questions requiring synthesis...

## 5. Evaluation Implementation Design
### 5.1 Evaluation Code Structure
./                           # Repository root directory
├── requirements.txt         # Consolidated dependencies
└── eval/                    # Evaluation workspace
    ├── README.md            # Running instructions
    ├── run_evaluation.py    # Strands Evals SDK implementation
    └── results/             # Evaluation outputs

## 6. Progress Tracking
### 6.1 User Requirements Log
| **Timestamp** | **Source** | **Requirement** |
| :------------ | :--------- | :-------------- |
| 2025-12-01    | eval sop    | Generate evaluation plan... |
```

### Generated Test Cases
Test cases are generated in JSONL format with structured metadata:
```json
{
  "name": "factual-question-1",
  "input": "What is the capital of France?",
  "expected_output": "The capital of France is Paris.",
  "metadata": {"category": "factual", "difficulty": "easy"}
}
```

### Generated Evaluation Report

The evaluation report provides comprehensive analysis with actionable insights:

```markdown
# Agent Evaluation Report for QA+Search Agent

## Executive Summary
- **Test Scale**: 2 test cases
- **Success Rate**: 100%
- **Overall Score**: 1.000 (Perfect)
- **Status**: Excellent
- **Action Priority**: Continue monitoring; consider expanding test coverage...

## Evaluation Results
### Test Case Coverage
- **Simple Factual Questions (Geography)**: Questions requiring basic factual information...
- **Simple Factual Questions (Sports/Time-sensitive)**: Questions requiring current event information...

### Results
| **Metric**              | **Score** | **Target** | **Status** |
| :---------------------- | :-------- | :--------- | :--------- |
| Answer Quality Score    | 1.00      | 0.75+      | Pass ✅    |
| Overall Test Pass Rate  | 100%      | 75%+       | Pass ✅    |

## Agent Success Analysis
### Strengths
- **Perfect Accuracy**: The agent correctly answered 100% of test questions...
- **Evidence**: Both test cases scored 1.0/1.0 (perfect scores)
- **Contributing Factors**: Effective use of web search tool...

## Agent Failure Analysis
### No Failures Detected
The evaluation identified zero failures across all test cases...

## Action Items & Recommendations
### Expand Test Coverage - Priority 1 (Enhancement)
- **Description**: Increase the number and diversity of test cases...
- **Actions**:
  - [ ] Add 5-10 additional test cases covering edge cases
  - [ ] Include multi-step reasoning scenarios
  - [ ] Add test cases for error conditions

## Artifacts & Reproduction
### Reference Materials
- **Agent Code**: `qa_agent/qa_agent.py`
- **Test Cases**: `eval/test-cases.jsonl`
- **Results**: `eval/results/.../evaluation_report.json`

### Reproduction Steps
source .venv/bin/activate
python eval/run_evaluation.py

## Evaluation Limitations and Improvement
### Test Data Improvement
- **Current Limitations**: Only 2 test cases, limited scenario diversity...
- **Recommended Improvements**: Increase test case count to 10-20 cases...
```

## Best Practices

### Evaluation Design
- **Start Simple**: Begin with basic functionality before testing edge cases
- **Iterate Frequently**: Run evaluations regularly during development
- **Document Assumptions**: Clearly document evaluation rationale and limitations
- **Validate Results**: Manually review a sample of evaluation results for accuracy

### Agent Preparation
- **Self-Contained Code**: Ensure your agent directory has no external dependencies
- **Tool Dependencies**: Document all required tools and their purposes

### Result Interpretation
- **Statistical Significance**: Consider running multiple evaluation rounds for reliability
- **Failure Analysis**: Focus on understanding why failures occur, not just counting them
- **Comparative Analysis**: Compare results across different agent configurations
- **Stakeholder Alignment**: Ensure evaluation metrics align with business objectives

## Troubleshooting

### Common Issues

**Issue**: "Agent directory not found"
**Solution**: Ensure agent path is correct and directory is self-contained

**Issue**: "Evaluation script fails to run"
**Solution**: Check that all dependencies are installed and agent code is valid

**Issue**: "Poor test case quality"
**Solution**: Provide more detailed agent documentation and example usage

**Issue**: "Inconsistent evaluation results"
**Solution**: Review evaluator configurations and consider multiple evaluation runs

### Getting Help

- **Agent SOP Repository**: [https://github.com/strands-agents/agent-sop](https://github.com/strands-agents/agent-sop)
- **Strands Eval SDK**: [Eval SDK Documentation](quickstart.md)

## Related Tools

- [**Strands Evaluation SDK**](quickstart.md): Core evaluation framework and evaluators
- [**Experiment Generator**](experiment_generator.md): Automated test case generation
- [**Output Evaluator**](evaluators/output_evaluator.md): Custom rubric-based evaluation
- [**Trajectory Evaluator**](evaluators/trajectory_evaluator.md): Tool usage and sequence analysis
- [**Agent SOP Repository**](https://github.com/strands-agents/agent-sop): Standard operating procedures for AI agents
