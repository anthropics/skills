import { Agent } from '@strands-agents/sdk'
import { notebook } from '@strands-agents/sdk/vended_tools/notebook'

// Basic metrics example
async function basicMetricsExample() {
  // --8<-- [start:basic_metrics]
  const agent = new Agent({
    tools: [notebook],
  })

  // Metrics are only available via streaming
  for await (const event of agent.stream('Calculate 2+2')) {
    if (event.type === 'modelMetadataEvent') {
      console.log('Token usage:', event.usage)
      console.log('Latency:', event.metrics?.latencyMs)
    }
  }
  // --8<-- [end:basic_metrics]
}

// Detailed metrics tracking
async function detailedMetricsTracking() {
  // --8<-- [start:detailed_tracking]
  const agent = new Agent({
    tools: [notebook],
  })

  let totalInputTokens = 0
  let totalOutputTokens = 0
  let totalLatency = 0

  for await (const event of agent.stream('What is the square root of 144?')) {
    if (event.type === 'modelMetadataEvent') {
      if (event.usage) {
        totalInputTokens += event.usage.inputTokens
        totalOutputTokens += event.usage.outputTokens
        console.log(`Input tokens: ${event.usage.inputTokens}`)
        console.log(`Output tokens: ${event.usage.outputTokens}`)
        console.log(`Total tokens: ${event.usage.totalTokens}`)

        // Cache metrics (when available)
        if (event.usage.cacheReadInputTokens) {
          console.log(`Cache read tokens: ${event.usage.cacheReadInputTokens}`)
        }
        if (event.usage.cacheWriteInputTokens) {
          console.log(`Cache write tokens: ${event.usage.cacheWriteInputTokens}`)
        }
      }

      if (event.metrics) {
        totalLatency += event.metrics.latencyMs
        console.log(`Latency: ${event.metrics.latencyMs}ms`)
      }
    }
  }

  console.log(`\nTotal input tokens: ${totalInputTokens}`)
  console.log(`Total output tokens: ${totalOutputTokens}`)
  console.log(`Total latency: ${totalLatency}ms`)
  // --8<-- [end:detailed_tracking]
}
