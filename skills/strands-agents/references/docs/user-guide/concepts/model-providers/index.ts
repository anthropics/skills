/**
 * TypeScript examples for model providers index documentation.
 * These examples demonstrate model interchangeability.
 */
// @ts-nocheck
// Imports are in index_imports.ts

import { Agent } from '@strands-agents/sdk'
import { BedrockModel } from '@strands-agents/sdk/models/bedrock'
import { OpenAIModel } from '@strands-agents/sdk/models/openai'

async function basicUsage() {
  // --8<-- [start:basic_usage]
  // Use Bedrock
  const bedrockModel = new BedrockModel({
    modelId: 'anthropic.claude-sonnet-4-20250514-v1:0',
  })
  let agent = new Agent({ model: bedrockModel })
  let response = await agent.invoke('What can you help me with?')

  // Alternatively, use OpenAI by just switching model provider
  const openaiModel = new OpenAIModel({
    apiKey: process.env.OPENAI_API_KEY,
    modelId: 'gpt-4o',
  })
  agent = new Agent({ model: openaiModel })
  response = await agent.invoke('What can you help me with?')
  // --8<-- [end:basic_usage]
}
