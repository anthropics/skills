/**
 * TypeScript examples for OpenAI model provider documentation.
 * These examples demonstrate common usage patterns for the OpenAIModel.
 */
// @ts-nocheck
// Imports are in openai_imports.ts

import { Agent } from '@strands-agents/sdk'
import { OpenAIModel } from '@strands-agents/sdk/openai'

// Basic usage
async function basicUsage() {
  // --8<-- [start:basic_usage]
  const model = new OpenAIModel({
    apiKey: process.env.OPENAI_API_KEY || '<KEY>',
    modelId: 'gpt-4o',
    maxTokens: 1000,
    temperature: 0.7,
  })

  const agent = new Agent({ model })
  const response = await agent.invoke('What is 2+2')
  console.log(response)
  // --8<-- [end:basic_usage]
}

// Custom server
async function customServer() {
  // --8<-- [start:custom_server]
  const model = new OpenAIModel({
    apiKey: '<KEY>',
    clientConfig: {
      baseURL: '<URL>',
    },
    modelId: 'gpt-4o',
  })

  const agent = new Agent({ model })
  const response = await agent.invoke('Hello!')
  // --8<-- [end:custom_server]
}

// Configuration
async function customConfig() {
  // --8<-- [start:custom_config]
  const model = new OpenAIModel({
    apiKey: process.env.OPENAI_API_KEY || '<KEY>',
    modelId: 'gpt-4o',
    maxTokens: 1000,
    temperature: 0.7,
    topP: 0.9,
    frequencyPenalty: 0.5,
    presencePenalty: 0.5,
  })

  const agent = new Agent({ model })
  const response = await agent.invoke('Write a short poem')
  console.log(response)
  // --8<-- [end:custom_config]
}

// Update configuration
async function updateConfig() {
  // --8<-- [start:update_config]
  const model = new OpenAIModel({
    apiKey: process.env.OPENAI_API_KEY || '<KEY>',
    modelId: 'gpt-4o',
    temperature: 0.7,
  })

  // Update configuration later
  model.updateConfig({
    temperature: 0.3,
    maxTokens: 500,
  })

  const agent = new Agent({ model })
  const response = await agent.invoke('Summarize this in one sentence')
  // --8<-- [end:update_config]
}

// Structured output
async function structuredOutput() {
  // --8<-- [start:structured_output]
  // Note: Structured output is not yet supported in the TypeScript SDK
  // This feature is coming soon. For now, you can use tool calling to achieve similar results.
  //
  // In Python, you can use agent.structured_output() with Pydantic models.
  // Follow the TypeScript SDK roadmap for updates on this feature.
  // --8<-- [end:structured_output]
}
