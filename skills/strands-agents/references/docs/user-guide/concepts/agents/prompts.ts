import { Agent, ImageBlock, TextBlock, Message } from '@strands-agents/sdk'
import { readFileSync } from 'fs'

// System prompt configuration example
async function systemPromptExample() {
  // --8<-- [start:systemPrompt]
  const agent = new Agent({
    systemPrompt:
      'You are a financial advisor specialized in retirement planning. ' +
      'Use tools to gather information and provide personalized advice. ' +
      'Always explain your reasoning and cite sources when possible.',
  })
  // --8<-- [end:systemPrompt]
}

// Simple text prompt example
async function textPromptExample() {
  const agent = new Agent()

  // --8<-- [start:textPrompt]
  const response = await agent.invoke('What is the time in Seattle')
  // --8<-- [end:textPrompt]
}

// Multi-modal prompting example
async function multimodalPromptExample() {
  const agent = new Agent()

  // --8<-- [start:multimodalPrompt]
  const imageBytes = readFileSync('path/to/image.png')

  const response = await agent.invoke([
    new TextBlock('What can you see in this image?'),
    new ImageBlock({
      format: 'png',
      source: {
        bytes: new Uint8Array(imageBytes),
      },
    }),
  ])
  // --8<-- [end:multimodalPrompt]
}
