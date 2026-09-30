# AgentCore Evaluation Dashboard Configuration

This guide explains how to configure AWS Distro for OpenTelemetry (ADOT) to send Strands evaluation results to Amazon CloudWatch, enabling visualization in the **GenAI Observability: Bedrock AgentCore Observability** dashboard.

## Overview

The Strands Evals SDK integrates with AWS Bedrock AgentCore's observability infrastructure to provide comprehensive evaluation metrics and dashboards. By configuring ADOT environment variables, you can:

- Send evaluation results to CloudWatch Logs in EMF (Embedded Metric Format)
- View evaluation metrics in the GenAI Observability dashboard
- Track evaluation scores, pass/fail rates, and detailed explanations
- Correlate evaluations with agent traces and sessions

## Prerequisites

Before configuring the evaluation dashboard, ensure you have:

1. **AWS Account** with appropriate permissions for CloudWatch and Bedrock AgentCore
2. **CloudWatch Transaction Search enabled** (one-time setup)
3. **ADOT SDK** installed in your environment ([guidance](https://docs.aws.amazon.com/bedrock-agentcore/latest/devguide/observability-configure.html))
4. **Strands Evals SDK** installed (`pip install strands-evals`)

## Step 1: Enable CloudWatch Transaction Search

CloudWatch Transaction Search must be enabled to view evaluation data in the GenAI Observability dashboard. This is a one-time setup per AWS account and region.

### Using the CloudWatch Console

1. Open the [CloudWatch console](https://console.aws.amazon.com/cloudwatch)
2. In the navigation pane, expand **Application Signals (APM)** and choose **Transaction search**
3. Choose **Enable Transaction Search**
4. Select the checkbox to **ingest spans as structured logs**
5. Choose **Save**

## Step 2: Configure Environment Variables

Configure the following environment variables to enable ADOT integration and send evaluation results to CloudWatch.

### Complete Environment Variable Configuration

```bash
# Enable agent observability
export AGENT_OBSERVABILITY_ENABLED="true"

# Configure ADOT for Python
export OTEL_PYTHON_DISTRO="aws_distro"
export OTEL_PYTHON_CONFIGURATOR="aws_configurator"

# Set log level for debugging (optional, use "info" for production)
export OTEL_LOG_LEVEL="debug"

# Configure exporters
export OTEL_METRICS_EXPORTER="awsemf"
export OTEL_TRACES_EXPORTER="otlp"
export OTEL_LOGS_EXPORTER="otlp"

# Set OTLP protocol
export OTEL_EXPORTER_OTLP_PROTOCOL="http/protobuf"

# Configure service name and log group
export OTEL_RESOURCE_ATTRIBUTES="service.name=my-evaluation-service,aws.log.group.names=/aws/bedrock-agentcore/runtimes/my-eval-logs"

# Enable Python logging auto-instrumentation
export OTEL_PYTHON_LOGGING_AUTO_INSTRUMENTATION_ENABLED="true"

# Capture GenAI message content
export OTEL_INSTRUMENTATION_GENAI_CAPTURE_MESSAGE_CONTENT="true"

# Disable AWS Application Signals (not needed for evaluations)
export OTEL_AWS_APPLICATION_SIGNALS_ENABLED="true"

# Configure OTLP endpoints
export OTEL_EXPORTER_OTLP_TRACES_ENDPOINT="https://xray.us-east-1.amazonaws.com/v1/traces"
export OTEL_EXPORTER_OTLP_LOGS_ENDPOINT="https://logs.us-east-1.amazonaws.com/v1/logs"

# Configure log export headers
export OTEL_EXPORTER_OTLP_LOGS_HEADERS="x-aws-log-group=/aws/bedrock-agentcore/runtimes/my-eval-logs,x-aws-log-stream=default,x-aws-metric-namespace=my-evaluation-namespace"

# Disable unnecessary instrumentations for better performance
export OTEL_PYTHON_DISABLED_INSTRUMENTATIONS="http,sqlalchemy,psycopg2,pymysql,sqlite3,aiopg,asyncpg,mysql_connector,urllib3,requests,system_metrics,google-genai"

# Configure evaluation results log group (used by Strands Evals)
export EVALUATION_RESULTS_LOG_GROUP="my-evaluation-results"

# AWS configuration
export AWS_REGION="us-east-1"
export AWS_DEFAULT_REGION="us-east-1"
```

### Environment Variable Descriptions

| Variable | Description | Example Value |
|----------|-------------|---------------|
| `AGENT_OBSERVABILITY_ENABLED` | Enables CloudWatch logging for evaluations | `true` |
| `OTEL_PYTHON_DISTRO` | Specifies ADOT distribution | `aws_distro` |
| `OTEL_PYTHON_CONFIGURATOR` | Configures ADOT for AWS | `aws_configurator` |
| `OTEL_LOG_LEVEL` | Sets OpenTelemetry log level | `debug` or `info` |
| `OTEL_METRICS_EXPORTER` | Metrics exporter type | `awsemf` |
| `OTEL_TRACES_EXPORTER` | Traces exporter type | `otlp` |
| `OTEL_LOGS_EXPORTER` | Logs exporter type | `otlp` |
| `OTEL_EXPORTER_OTLP_PROTOCOL` | OTLP protocol format | `http/protobuf` |
| `OTEL_RESOURCE_ATTRIBUTES` | Service name and log group for resource attributes | `service.name=my-service,aws.log.group.names=/aws/bedrock-agentcore/runtimes/logs` |
| `OTEL_PYTHON_LOGGING_AUTO_INSTRUMENTATION_ENABLED` | Auto-instrument Python logging | `true` |
| `OTEL_INSTRUMENTATION_GENAI_CAPTURE_MESSAGE_CONTENT` | Capture GenAI message content | `true` |
| `OTEL_AWS_APPLICATION_SIGNALS_ENABLED` | Enable AWS Application Signals | `false` |
| `OTEL_EXPORTER_OTLP_TRACES_ENDPOINT` | X-Ray traces endpoint | `https://xray.us-east-1.amazonaws.com/v1/traces` |
| `OTEL_EXPORTER_OTLP_LOGS_ENDPOINT` | CloudWatch logs endpoint | `https://logs.us-east-1.amazonaws.com/v1/logs` |
| `OTEL_EXPORTER_OTLP_LOGS_HEADERS` | CloudWatch log destination headers | `x-aws-log-group=/aws/bedrock-agentcore/runtimes/logs,x-aws-log-stream=default,x-aws-metric-namespace=namespace` |
| `OTEL_PYTHON_DISABLED_INSTRUMENTATIONS` | Disable unnecessary instrumentations | `http,sqlalchemy,psycopg2,...` |
| `EVALUATION_RESULTS_LOG_GROUP` | Base name for evaluation results log group | `my-evaluation-results` |
| `AWS_REGION` | AWS region for CloudWatch | `us-east-1` |

## Step 3: Install ADOT SDK

Install the AWS Distro for OpenTelemetry SDK in your Python environment:

```bash
pip install aws-opentelemetry-distro>=0.10.0 boto3
```

Or add to your `requirements.txt`:

```text
aws-opentelemetry-distro>=0.10.0
boto3
strands-evals
```

## Step 4: Run Evaluations with ADOT

Execute your evaluation script using the OpenTelemetry auto-instrumentation command:

```bash
opentelemetry-instrument python my_evaluation_script.py
```

### Complete Setup and Execution Script

```bash
#!/bin/bash

# AWS Configuration
export AWS_REGION="us-east-1"
export AWS_DEFAULT_REGION="us-east-1"

# Enable Agent Observability
export AGENT_OBSERVABILITY_ENABLED="true"

# ADOT Configuration
export OTEL_LOG_LEVEL="debug"
export OTEL_METRICS_EXPORTER="awsemf"
export OTEL_TRACES_EXPORTER="otlp"
export OTEL_LOGS_EXPORTER="otlp"
export OTEL_PYTHON_DISTRO="aws_distro"
export OTEL_PYTHON_CONFIGURATOR="aws_configurator"
export OTEL_EXPORTER_OTLP_PROTOCOL="http/protobuf"

# Service Configuration
SERVICE_NAME="test-agent-3"
LOG_GROUP="/aws/bedrock-agentcore/runtimes/strands-agents-tests"
METRIC_NAMESPACE="test-strands-agentcore"

export OTEL_RESOURCE_ATTRIBUTES="service.name=${SERVICE_NAME},aws.log.group.names=${LOG_GROUP}"
export OTEL_PYTHON_LOGGING_AUTO_INSTRUMENTATION_ENABLED="true"
export OTEL_INSTRUMENTATION_GENAI_CAPTURE_MESSAGE_CONTENT="true"
export OTEL_AWS_APPLICATION_SIGNALS_ENABLED="false"

# OTLP Endpoints
export OTEL_EXPORTER_OTLP_TRACES_ENDPOINT="https://xray.${AWS_REGION}.amazonaws.com/v1/traces"
export OTEL_EXPORTER_OTLP_LOGS_ENDPOINT="https://logs.${AWS_REGION}.amazonaws.com/v1/logs"
export OTEL_EXPORTER_OTLP_LOGS_HEADERS="x-aws-log-group=${LOG_GROUP},x-aws-log-stream=default,x-aws-metric-namespace=${METRIC_NAMESPACE}"

# Disable Unnecessary Instrumentations
export OTEL_PYTHON_DISABLED_INSTRUMENTATIONS="http,sqlalchemy,psycopg2,pymysql,sqlite3,aiopg,asyncpg,mysql_connector,urllib3,requests,system_metrics,google-genai"

# Evaluation Results Configuration
export EVALUATION_RESULTS_LOG_GROUP="strands-agents-tests"

# Run evaluations with ADOT instrumentation
opentelemetry-instrument python evaluation_agentcore_dashboard.py
```

### Example Evaluation Script

```python
from strands_evals import Experiment, Case
from strands_evals.evaluators import OutputEvaluator

# Create evaluation cases
cases = [
    Case(
        name="Knowledge Test",
        input="What is the capital of France?",
        expected_output="The capital of France is Paris.",
        metadata={"category": "knowledge"}
    ),
    Case(
        name="Math Test",
        input="What is 2+2?",
        expected_output="2+2 equals 4.",
        metadata={"category": "math"}
    )
]

# Create evaluator
evaluator = OutputEvaluator(
    rubric="The output is accurate and complete. Score 1 if correct, 0 if incorrect."
)

# Create experiment
experiment = Experiment(cases=cases, evaluator=evaluator)

# Define your task function
def my_agent_task(case: Case) -> str:
    # Your agent logic here
    # This should return the agent's response
    return f"Response to: {case.input}"

# Run evaluations
reports = experiment.run_evaluations(my_agent_task)

print(f"Overall Score: {report.overall_score}")
print(f"Pass Rate: {sum(report.test_passes)}/{len(report.test_passes)}")
```

### For Containerized Environments (Docker)

Add the OpenTelemetry instrumentation to your Dockerfile CMD:

```dockerfile
FROM python:3.11

WORKDIR /app

# Install dependencies
COPY requirements.txt .
RUN pip install -r requirements.txt

# Copy application code
COPY . .

# Set environment variables
ENV AGENT_OBSERVABILITY_ENABLED=true \
    OTEL_PYTHON_DISTRO=aws_distro \
    OTEL_PYTHON_CONFIGURATOR=aws_configurator \
    OTEL_METRICS_EXPORTER=awsemf \
    OTEL_TRACES_EXPORTER=otlp \
    OTEL_LOGS_EXPORTER=otlp \
    OTEL_EXPORTER_OTLP_PROTOCOL=http/protobuf

# Run with ADOT instrumentation
CMD ["opentelemetry-instrument", "python", "evaluation_agentcore_dashboard.py"]
```

## Step 5: View Evaluation Results in CloudWatch

Once your evaluations are running with ADOT configured, you can view the results in multiple locations:

### GenAI Observability Dashboard

1. Open the [CloudWatch GenAI Observability](https://console.aws.amazon.com/cloudwatch/home#gen-ai-observability) page
2. Navigate to **Bedrock AgentCore Observability** section
3. View evaluation metrics including:
   - Evaluation scores by service name
   - Pass/fail rates by label
   - Evaluation trends over time
   - Detailed evaluation explanations

### CloudWatch Logs

Evaluation results are stored in the log group:
```
/aws/bedrock-agentcore/evaluations/results/{EVALUATION_RESULTS_LOG_GROUP}
```

Each log entry contains:
- Evaluation score and label (YES/NO)
- Evaluator name (e.g., `Custom.OutputEvaluator`)
- Trace ID for correlation
- Session ID
- Detailed explanation
- Input/output data

### CloudWatch Metrics

Metrics are published to the namespace specified in `x-aws-metric-namespace` with dimensions:
- `service.name`: Your service name
- `label`: Evaluation label (YES/NO)
- `onlineEvaluationConfigId`: Configuration identifier

## Advanced Configuration

### Custom Service Names

Set a custom service name to organize evaluations:

```bash
export OTEL_RESOURCE_ATTRIBUTES="service.name=my-custom-agent,aws.log.group.names=/aws/bedrock-agentcore/runtimes/custom-logs"
```

### Session ID Propagation

To correlate evaluations with agent sessions, set the session ID in your cases:

```python
case = Case(
    name="Test Case",
    input="Test input",
    expected_output="Expected output",
    session_id="my-session-123"  # Links evaluation to agent session
)
```

### Async Evaluations

For better performance with multiple test cases, use async evaluations:

```python
import asyncio

async def run_async_evaluations():
    report = await experiment.run_evaluations_async(
        my_agent_task,
        max_workers=10  # Parallel execution
    )
    return report

# Run async evaluations
report = asyncio.run(run_async_evaluations())
```

### Custom Evaluators

Create custom evaluators with specific scoring logic:

```python
from strands_evals.evaluators import Evaluator
from strands_evals.types.evaluation import EvaluationData, EvaluationOutput

class CustomEvaluator(Evaluator):
    def __init__(self, threshold: float = 0.8):
        super().__init__()
        self.threshold = threshold
        self._score_mapping = {"PASS": 1.0, "FAIL": 0.0}
    
    def evaluate(self, data: EvaluationData) -> list[EvaluationOutput]:
        # Your custom evaluation logic
        score = 1.0 if self._check_quality(data.actual_output) else 0.0
        label = "PASS" if score >= self.threshold else "FAIL"
        
        return [EvaluationOutput(
            score=score,
            passed=(score >= self.threshold),
            reason=f"Quality check: {label}"
        )]
    
    def _check_quality(self, output) -> bool:
        # Implement your quality check
        return True
```

### Performance Optimization

Disable unnecessary instrumentations to improve performance:

```bash
export OTEL_PYTHON_DISABLED_INSTRUMENTATIONS="http,sqlalchemy,psycopg2,pymysql,sqlite3,aiopg,asyncpg,mysql_connector,urllib3,requests,system_metrics,google-genai"
```

This disables instrumentation for libraries that aren't needed for evaluation telemetry, reducing overhead.

## Troubleshooting

### Evaluations Not Appearing in Dashboard

1. **Verify CloudWatch Transaction Search is enabled**
   ```bash
   aws xray get-trace-segment-destination
   ```
   Should return: `{"Destination": "CloudWatchLogs"}`

2. **Check environment variables are set correctly**
   ```bash
   echo $AGENT_OBSERVABILITY_ENABLED
   echo $OTEL_RESOURCE_ATTRIBUTES
   echo $OTEL_EXPORTER_OTLP_LOGS_ENDPOINT
   ```

3. **Verify log group exists**
   ```bash
   aws logs describe-log-groups \
     --log-group-name-prefix "/aws/bedrock-agentcore"
   ```

4. **Check IAM permissions** - Ensure your execution role has:
   - `logs:CreateLogGroup`
   - `logs:CreateLogStream`
   - `logs:PutLogEvents`
   - `xray:PutTraceSegments`
   - `xray:PutTelemetryRecords`

### Missing Metrics

If metrics aren't appearing in CloudWatch:

1. Verify the `OTEL_EXPORTER_OTLP_LOGS_HEADERS` includes `x-aws-metric-namespace`
2. Check that `OTEL_METRICS_EXPORTER="awsemf"` is set
3. Ensure evaluations are completing successfully (no exceptions)
4. Wait 5-10 minutes for metrics to propagate to CloudWatch

### Log Format Issues

If logs aren't in the correct format:

1. Ensure `OTEL_PYTHON_DISTRO=aws_distro` is set
2. Verify `OTEL_PYTHON_CONFIGURATOR=aws_configurator` is set
3. Check that `aws-opentelemetry-distro>=0.10.0` is installed
4. Verify `OTEL_EXPORTER_OTLP_PROTOCOL=http/protobuf` is set

### Debug Mode

Enable debug logging to troubleshoot issues:

```bash
export OTEL_LOG_LEVEL="debug"
```

This will output detailed ADOT logs to help identify configuration problems.

## Best Practices

1. **Use Consistent Service Names**: Use the same service name across related evaluations for easier filtering and analysis

2. **Include Session IDs**: Always include session IDs in your test cases to correlate evaluations with agent interactions

3. **Set Appropriate Sampling**: For high-volume evaluations, adjust the X-Ray sampling percentage to balance cost and visibility

4. **Monitor Log Group Size**: Evaluation logs can grow quickly; set up log retention policies:
   ```bash
   aws logs put-retention-policy \
     --log-group-name "/aws/bedrock-agentcore/evaluations/results/my-eval" \
     --retention-in-days 30
   ```

5. **Use Descriptive Evaluator Names**: Custom evaluators should have clear, descriptive names that appear in the dashboard

6. **Optimize Performance**: Disable unnecessary instrumentations to reduce overhead in production environments

7. **Tag Evaluations**: Use metadata in test cases to add context:
   ```python
   Case(
       name="Test",
       input="...",
       expected_output="...",
       metadata={
           "environment": "production",
           "version": "v1.2.3",
           "category": "accuracy"
       }
   )
   ```

8. **Use Info Log Level in Production**: Set `OTEL_LOG_LEVEL="info"` in production to reduce log volume

## Additional Resources

- [AWS Bedrock AgentCore Observability Documentation](https://docs.aws.amazon.com/bedrock-agentcore/latest/devguide/observability-configure.html)
- [ADOT Python Documentation](https://aws-otel.github.io/docs/getting-started/python-sdk)
- [CloudWatch GenAI Observability](https://console.aws.amazon.com/cloudwatch/home#gen-ai-observability)
- [Strands Evals SDK Documentation](../quickstart.md)
