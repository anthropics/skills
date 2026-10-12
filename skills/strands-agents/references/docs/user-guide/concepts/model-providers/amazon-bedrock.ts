/**
 * TypeScript examples for Amazon Bedrock model provider documentation.
 * These examples demonstrate common usage patterns for the BedrockModel.
 */
// @ts-nocheck
// Imports are in amazon-bedrock_imports.ts

import { Agent, BedrockModel, DocumentBlock, CachePointBlock, Message } from '@strands-agents/sdk'

// Basic usage examples
async function basicUsageDefault() {
  // --8<-- [start:basic_default]
  const agent = new Agent()

  const response = await agent.invoke('Tell me about Amazon Bedrock.')
  // --8<-- [end:basic_default]
}

async function basicUsageModelId() {
  // --8<-- [start:basic_model_id]
  // Create an agent using the model
  const agent = new Agent({ model: 'anthropic.claude-sonnet-4-20250514-v1:0' })

  const response = await agent.invoke('Tell me about Amazon Bedrock.')
  // --8<-- [end:basic_model_id]
}

async function basicUsageModelInstance() {
  // --8<-- [start:basic_model_instance]
  // Create a Bedrock model instance
  const bedrockModel = new BedrockModel({
    modelId: 'us.amazon.nova-premier-v1:0',
    temperature: 0.3,
    topP: 0.8,
  })

  // Create an agent using the BedrockModel instance
  const agent = new Agent({ model: bedrockModel })

  // Use the agent
  const response = await agent.invoke('Tell me about Amazon Bedrock.')
  // --8<-- [end:basic_model_instance]
}

// Configuration example
async function configurationExample() {
  // --8<-- [start:configuration]
  // Create a configured Bedrock model
  const bedrockModel = new BedrockModel({
    modelId: 'anthropic.claude-sonnet-4-20250514-v1:0',
    region: 'us-east-1', // Specify a different region than the default
    temperature: 0.3,
    topP: 0.8,
    stopSequences: ['###', 'END'],
    clientConfig: {
      retryMode: 'standard',
      maxAttempts: 3,
    },
  })

  // Create an agent with the configured model
  const agent = new Agent({ model: bedrockModel })

  // Use the agent
  const response = await agent.invoke('Write a short story about an AI assistant.')
  // --8<-- [end:configuration]
}

// Streaming vs non-streaming
async function streamingExample() {
  // --8<-- [start:streaming]
  // Streaming model (default)
  const streamingModel = new BedrockModel({
    modelId: 'anthropic.claude-sonnet-4-20250514-v1:0',
    stream: true, // This is the default
  })

  // Non-streaming model
  const nonStreamingModel = new BedrockModel({
    modelId: 'us.meta.llama3-2-90b-instruct-v1:0',
    stream: false, // Disable streaming
  })
  // --8<-- [end:streaming]
}

// Update configuration at runtime
async function updateConfiguration() {
  // --8<-- [start:update_config]
  // Create the model with initial configuration
  const bedrockModel = new BedrockModel({
    modelId: 'anthropic.claude-sonnet-4-20250514-v1:0',
    temperature: 0.7,
  })

  // Update configuration later
  bedrockModel.updateConfig({
    temperature: 0.3,
    topP: 0.2,
  })
  // --8<-- [end:update_config]
}

// Tool-based configuration update
async function toolBasedConfigUpdate() {
  // --8<-- [start:tool_update_config]
  // Define a tool that updates model configuration
  const updateTemperature = tool({
    name: 'update_temperature',
    description: 'Update the temperature of the agent',
    inputSchema: z.object({
      temperature: z.number().describe('Temperature value for the model to use'),
    }),
    callback: async ({ temperature }, context) => {
      if (context.agent?.model && 'updateConfig' in context.agent.model) {
        context.agent.model.updateConfig({ temperature })
        return `Temperature updated to ${temperature}`
      }
      return 'Failed to update temperature'
    },
  })

  const agent = new Agent({
    model: new BedrockModel({ modelId: 'anthropic.claude-sonnet-4-20250514-v1:0' }),
    tools: [updateTemperature],
  })
  // --8<-- [end:tool_update_config]
}

// Reasoning support
async function reasoningSupport() {
  // --8<-- [start:reasoning]
  // Create a Bedrock model with reasoning configuration
  const bedrockModel = new BedrockModel({
    modelId: 'anthropic.claude-sonnet-4-20250514-v1:0',
    additionalRequestFields: {
      thinking: {
        type: 'enabled',
        budget_tokens: 4096, // Minimum of 1,024
      },
    },
  })

  // Create an agent with the reasoning-enabled model
  const agent = new Agent({ model: bedrockModel })

  // Ask a question that requires reasoning
  const response = await agent.invoke(
    'If a train travels at 120 km/h and needs to cover 450 km, how long will the journey take?'
  )
  // --8<-- [end:reasoning]
}

// Custom credentials configuration
async function customCredentials() {
  // --8<-- [start:custom_credentials]
  // AWS credentials are configured through the clientConfig parameter
  // See AWS SDK for JavaScript documentation for all credential options:
  // https://docs.aws.amazon.com/sdk-for-javascript/v3/developer-guide/setting-credentials-node.html

  const bedrockModel = new BedrockModel({
    modelId: 'anthropic.claude-sonnet-4-20250514-v1:0',
    region: 'us-west-2',
    clientConfig: {
      credentials: {
        accessKeyId: 'your_access_key',
        secretAccessKey: 'your_secret_key',
        sessionToken: 'your_session_token', // If using temporary credentials
      },
    },
  })
  // --8<-- [end:custom_credentials]
}

// Multimodal support
async function multimodalSupport() {
  // --8<-- [start:multimodal_full]
  const bedrockModel = new BedrockModel({
    modelId: 'anthropic.claude-sonnet-4-20250514-v1:0',
  })

  const agent = new Agent({ model: bedrockModel })

  const documentBytes = Buffer.from('Once upon a time...')

  // Send multimodal content directly to invoke
  const response = await agent.invoke([
    new DocumentBlock({
      format: 'txt',
      name: 'example',
      source: { bytes: documentBytes },
    }),
    'Tell me about the document.',
  ])
  // --8<-- [end:multimodal_full]
}

// S3 location support for multimodal content
async function s3LocationSupport() {
  // --8<-- [start:s3_location]
  const agent = new Agent({ model: new BedrockModel() })

  const response = await agent.invoke([
    new DocumentBlock({
      format: 'pdf',
      name: 'report.pdf',
      source: {
        s3Location: {
          uri: 's3://my-bucket/documents/report.pdf',
          bucketOwner: '123456789012', // Optional: for cross-account access
        },
      },
    }),
    'Summarize this document.',
  ])
  // --8<-- [end:s3_location]
}

// System prompt caching
async function systemPromptCachingFull() {
  // --8<-- [start:system_prompt_caching_full]
  const systemContent = [
    'You are a helpful assistant that provides concise answers. ' +
      'This is a long system prompt with detailed instructions...' +
      '...'.repeat(1600), // needs to be at least 1,024 tokens
    new CachePointBlock({ cacheType: 'default' }),
  ]

  const agent = new Agent({ systemPrompt: systemContent })

  // First request will cache the system prompt
  let cacheWriteTokens = 0
  let cacheReadTokens = 0

  for await (const event of agent.stream('Tell me about Python')) {
    if (event.type === 'modelMetadataEvent' && event.usage) {
      cacheWriteTokens = event.usage.cacheWriteInputTokens || 0
      cacheReadTokens = event.usage.cacheReadInputTokens || 0
    }
  }
  console.log(`Cache write tokens: ${cacheWriteTokens}`)
  console.log(`Cache read tokens: ${cacheReadTokens}`)

  // Second request will reuse the cached system prompt
  for await (const event of agent.stream('Tell me about JavaScript')) {
    if (event.type === 'modelMetadataEvent' && event.usage) {
      cacheWriteTokens = event.usage.cacheWriteInputTokens || 0
      cacheReadTokens = event.usage.cacheReadInputTokens || 0
    }
  }
  console.log(`Cache write tokens: ${cacheWriteTokens}`)
  console.log(`Cache read tokens: ${cacheReadTokens}`)
  // --8<-- [end:system_prompt_caching_full]
}

// Tool caching
async function toolCachingFull() {
  // --8<-- [start:tool_caching_full]
  const bedrockModel = new BedrockModel({
    modelId: 'anthropic.claude-sonnet-4-20250514-v1:0',
    cacheTools: 'default',
  })

  const agent = new Agent({
    model: bedrockModel,
    // Add your tools here when they become available
  })

  // First request will cache the tools
  await agent.invoke('What time is it?')

  // Second request will reuse the cached tools
  await agent.invoke('What is the square root of 1764?')

  // Note: Cache metrics are not yet available in the TypeScript SDK
  // --8<-- [end:tool_caching_full]
}

// Messages caching
async function messagesCachingFull() {
  // --8<-- [start:messages_caching_full]
  const documentBytes = Buffer.from('This is a sample document!')

  const userMessage = new Message({
    role: 'user',
    content: [
      new DocumentBlock({
        format: 'txt',
        name: 'example',
        source: { bytes: documentBytes },
      }),
      'Use this document in your response.',
      new CachePointBlock({ cacheType: 'default' }),
    ],
  })

  const assistantMessage = new Message({
    role: 'assistant',
    content: ['I will reference that document in my following responses.'],
  })

  const agent = new Agent({
    messages: [userMessage, assistantMessage],
  })

  // First request will cache the message
  await agent.invoke('What is in that document?')

  // Second request will reuse the cached message
  await agent.invoke('How long is the document?')

  // Note: Cache metrics are not yet available in the TypeScript SDK
  // --8<-- [end:messages_caching_full]
}

// Cache metrics
async function cacheMetrics() {
  // --8<-- [start:cache_metrics]
  const agent = new Agent()

  for await (const event of agent.stream('Hello!')) {
    if (event.type === 'modelMetadataEvent' && event.usage) {
      console.log(`Cache write tokens: ${event.usage.cacheWriteInputTokens || 0}`)
      console.log(`Cache read tokens: ${event.usage.cacheReadInputTokens || 0}`)
    }
  }
  // --8<-- [end:cache_metrics]
}
