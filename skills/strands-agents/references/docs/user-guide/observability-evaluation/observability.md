# Observability

{{ ts_not_supported("The 0.1.0 release of the TypeScript SDK does not include OpenTelemetry observability features. Support is planned for a future version. See issue [#69](https://github.com/strands-agents/sdk-typescript/issues/69) to track progress or contribute to the implementation.") }}

In the Strands Agents SDK, observability refers to the ability to measure system behavior and performance. Observability is the combination of instrumentation, data collection, and analysis techniques that provide insights into an agent's behavior and performance. It enables Strands Agents developers to effectively build, debug and maintain agents to better serve their unique customer needs and reliably complete their tasks. This guide provides background on what type of data (or "Primitives") makes up observability as well as best practices for implementing agent observability with the Strands Agents SDK. 

##  Embedded in Strands Agents
All observability APIs are embedded directly within the Strands Agents SDK.

While this document provides high-level information about observability, look to the following specific documents on how to instrument these primitives in your system:

 * [Metrics](./metrics.md)
 * [Traces](./traces.md)
 * [Logs](./logs.md)
 * [Evaluation](./evaluation.md)


## Telemetry Primitives

Building observable agents starts with monitoring the right telemetry. While we leverage the same fundamental building blocks as traditional software — **traces**, **metrics**, and **logs** — their application to agents requires special consideration. We need to capture not only standard application telemetry but also AI-specific signals like model interactions, reasoning steps, and tool usage.

### Traces

A trace represents an end-to-end request to your application. Traces consist of spans which represent the intermediate steps the application took to generate a response. Agent traces typically contain spans which represent model and tool invocations. Spans are enriched by context associated with the step they are tracking. For example:

* A model invocation span may include:
    * System prompt
    * Model parameters (e.g. `temperature`, `top_p`, `top_k`, `max_tokens`)
    * Input and output message list
    * Input and output token usage
* A tool invocation span may include the tool input and output

Traces provide deep insight into how an agent or workflow arrived at its final response. AI engineers can translate this insight into prompt, tool and context management improvements.

### Metrics

Metrics are measurements of events in applications. Key metrics to monitor include: 

* **Agent Metrics**
    * Tool Metrics
        * Number of invocations
        * Execution time
        * Error rates and types
    * Latency (time to first byte and time to last byte)
    * Number of agent loops executed
* **Model-Specific Metrics**
    * Token usage (input/output)
    * Model latency
    * Model API errors and rate limits
* **System Metrics**
    * Memory utilization
    * CPU utilization
    * Availability
* **Customer Feedback and Retention Metrics**
    * Number of interactions with thumbs up/down
    * Free form text feedback
    * Length and duration of agent interactions
    * Daily, weekly, monthly active users

Metrics provide both request level and aggregate performance characteristics of the agentic system. They are signals which must be monitored to ensure the operational health and positive customer impact of the agentic system.

### Logs

Logs are unstructured or structured text records emitted at specific timestamps in an application. Logging is one of the most traditional forms of debugging. 

## End-to-End Observability Framework

Agent observability combines traditional software reliability and observability practices with data engineering, MLOps, and business intelligence.

For teams building agentic applications, this will typically involve:

1. **Agent Engineering**
    1. Building, testing and deploying the agentic application
    2. Adding instrumentation to collect metrics, traces, and logs for agent interactions
    3. Creating dashboards and alarms for errors, latency, resource utilization and faulty agent behavior.
2. **Data Engineering and Business Intelligence:**
    1. Exporting telemetry data to data warehouses for long-term storage and analysis
    2. Building ETL pipelines to transform and aggregate telemetry data
    3. Creating business intelligence dashboards to analyze cost, usage trends and customer satisfaction.
3. **Research and Applied science:**
    1. Visualizing traces to analyze failure modes and edge cases
    2. Collecting traces for evaluation and benchmarking
    3. Building datasets for model fine-tuning 


With these components in place, a continuous improvement flywheel emerges which enables:

* Incorporating user feedback and satisfaction metrics to inform product strategy
* Leveraging traces to improve agent design and the underlying models
* Detecting regressions and measuring the impact of new features

## Best Practices

1. **Standardize Instrumentation:** Adopt industry standards like [OpenTelemetry](https://opentelemetry.io/) for transmitting traces, metrics, and logs. 
2. **Design for Multiple Consumers**: Implement a fan-out architecture for telemetry data to serve different stakeholders and use cases. Specifically, [OpenTelemetry collectors](https://opentelemetry.io/docs/collector/) can serve as this routing layer.
3. **Optimize for Large Data Volume**: Identify which data attributes are important for downstream tasks and implement filtering to send specific data to those downstream systems. Incorporate sampling and batching wherever possible.
4. **Shift Observability Left**: Use telemetry data when building agents to improve prompts and tool implementations. 
5. **Raise the Security and Privacy Bar**: Implement proper data access controls and retention policies for all sensitive data. Redact or omit data containing personal identifiable information. Regularly audit data collection processes. 

## Conclusion

Effective observability is crucial for developing agents that reliably complete customers’ tasks. The key to success is treating observability not as an afterthought, but as a core component of agent engineering from day one. This investment will pay dividends in improved reliability, faster development cycles, and better customer experiences.
