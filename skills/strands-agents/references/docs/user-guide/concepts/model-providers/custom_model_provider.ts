/**
 * TypeScript examples for custom model provider documentation.
 * These examples demonstrate how to implement a custom model provider.
 */

import { Agent, BedrockModel, type BedrockModelConfig } from '@strands-agents/sdk'
import type {
  Model,
  BaseModelConfig,
  Message,
  ContentBlock,
  ToolSpec,
  ModelStreamEvent,
  ModelMessageStartEventData,
  ModelContentBlockDeltaEventData,
  ModelMessageStopEventData,
} from '@strands-agents/sdk'

// Example wrapper around BedrockModel for demonstration
class YourCustomModel extends BedrockModel {
  constructor(config: BedrockModelConfig = {
  modelId: 'anthropic.claude-3-5-sonnet-20241022-v2:0'
}) {
    super(config)
    // Add any custom initialization here
  }
}

// --8<-- [start:basic_usage]
const yourCustomModel = new YourCustomModel()

const agent = new Agent({ model: yourCustomModel })
const response = await agent.invoke('Hello, how can you help me today?')
// --8<-- [end:basic_usage]

// --8<-- [start:create_model_class]
// src/models/custom-model.ts

// Mock client for documentation purposes
interface CustomModelClient {
  streamCompletion: (request: any) => AsyncIterable<any>
}

/**
 * Configuration interface for the custom model.
 */
export interface CustomModelConfig extends BaseModelConfig {
  apiKey?: string
  modelId?: string
  maxTokens?: number
  temperature?: number
  topP?: number
  // Add any additional configuration parameters specific to your model
}

/**
 * Custom model provider implementation.
 * 
 * Note: In practice, you would extend the Model abstract class from the SDK.
 * This example shows the interface implementation for documentation purposes.
 */
export class CustomModel {
  private client: CustomModelClient
  private config: CustomModelConfig

  constructor(config: CustomModelConfig) {
    this.config = { ...config }
    // Initialize your custom model client
    this.client = {
      streamCompletion: async function* () {
        yield { type: 'message_start', role: 'assistant' }
      },
    }
  }

  updateConfig(config: Partial<CustomModelConfig>): void {
    this.config = { ...this.config, ...config }
  }

  getConfig(): CustomModelConfig {
    return { ...this.config }
  }

  async *stream(
    messages: Message[],
    options?: {
      systemPrompt?: string | string[]
      toolSpecs?: ToolSpec[]
      toolChoice?: any
    }
  ): AsyncIterable<ModelStreamEvent> {
    // Implementation in next section
    // This is a placeholder that yields nothing
    if (false) yield {} as ModelStreamEvent
  }
}
// --8<-- [end:create_model_class]



// --8<-- [start:implement_stream]
// Implementation of the stream method and helper methods

export class CustomModelStreamExample {
  private config: CustomModelConfig
  private client: CustomModelClient

  constructor(config: CustomModelConfig) {
    this.config = config
    this.client = {
      streamCompletion: async function* () {
        yield { type: 'message_start', role: 'assistant' }
      },
    }
  }

  updateConfig(config: Partial<CustomModelConfig>): void {
    this.config = { ...this.config, ...config }
  }

  getConfig(): CustomModelConfig {
    return { ...this.config }
  }

  async *stream(
    messages: Message[],
    options?: {
      systemPrompt?: string | string[]
      toolSpecs?: ToolSpec[]
      toolChoice?: any
    }
  ): AsyncIterable<ModelStreamEvent> {
    // 1. Format messages for your model's API
    const formattedMessages = this.formatMessages(messages)
    const formattedTools = options?.toolSpecs ? this.formatTools(options.toolSpecs) : undefined

    // 2. Prepare the API request
    const request = {
      model: this.config.modelId,
      messages: formattedMessages,
      systemPrompt: options?.systemPrompt,
      tools: formattedTools,
      maxTokens: this.config.maxTokens,
      temperature: this.config.temperature,
      topP: this.config.topP,
      stream: true,
    }

    // 3. Call your model's API and stream responses
    const response = await this.client.streamCompletion(request)

    // 4. Convert API events to Strands ModelStreamEvent format
    for await (const chunk of response) {
      yield this.convertToModelStreamEvent(chunk)
    }
  }

  private formatMessages(messages: Message[]): any[] {
    return messages.map((message) => ({
      role: message.role,
      content: this.formatContent(message.content),
    }))
  }

  private formatContent(content: ContentBlock[]): any {
    // Convert Strands content blocks to your model's format
    return content.map((block) => {
      if (block.type === 'textBlock') {
        return { type: 'text', text: block.text }
      }
      // Handle other content types...
      return block
    })
  }

  private formatTools(toolSpecs: ToolSpec[]): any[] {
    return toolSpecs.map((tool) => ({
      name: tool.name,
      description: tool.description,
      parameters: tool.inputSchema,
    }))
  }

  private convertToModelStreamEvent(chunk: any): ModelStreamEvent {
    // Convert your model's streaming response to ModelStreamEvent

    if (chunk.type === 'message_start') {
      const event: ModelMessageStartEventData = {
        type: 'modelMessageStartEvent',
        role: chunk.role,
      }
      return event
    }

    if (chunk.type === 'content_block_delta') {
      if (chunk.delta.type === 'text_delta') {
        const event: ModelContentBlockDeltaEventData = {
          type: 'modelContentBlockDeltaEvent',
          delta: {
            type: 'textDelta',
            text: chunk.delta.text,
          },
        }
        return event
      }
    }

    if (chunk.type === 'message_stop') {
      const event: ModelMessageStopEventData = {
        type: 'modelMessageStopEvent',
        stopReason: this.mapStopReason(chunk.stopReason),
      }
      return event
    }

    throw new Error(`Unsupported chunk type: ${chunk.type}`)
  }

  private mapStopReason(reason: string): 'endTurn' | 'maxTokens' | 'toolUse' | 'stopSequence' {
    const stopReasonMap: Record<string, 'endTurn' | 'maxTokens' | 'toolUse' | 'stopSequence'> = {
      end_turn: 'endTurn',
      max_tokens: 'maxTokens',
      tool_use: 'toolUse',
      stop_sequence: 'stopSequence',
    }
    return stopReasonMap[reason] || 'endTurn'
  }
}
// --8<-- [end:implement_stream]

// --8<-- [start:usage_example]
async function usageExample() {
  // Initialize your custom model provider
  const customModel = new YourCustomModel({
    maxTokens: 2000,
    temperature: 0.7,
  })

  // Create a Strands agent using your model
  const agent = new Agent({ model: customModel })

  // Use the agent as usual
  const response = await agent.invoke('Hello, how are you today?')
}
// --8<-- [end:usage_example]
