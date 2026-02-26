// --8<-- [start:custom-tool]
// Define a custom tool as a TypeScript function
import { Agent, tool } from '@strands-agents/sdk'
import z from 'zod'

const letterCounter = tool({
  name: 'letter_counter',
  description: 'Count occurrences of a specific letter in a word. Performs case-insensitive matching.',
  // Zod schema for letter counter input validation
  inputSchema: z
    .object({
      word: z.string().describe('The input word to search in'),
      letter: z.string().describe('The specific letter to count'),
    })
    .refine((data) => data.letter.length === 1, {
      message: "The 'letter' parameter must be a single character",
    }),
  callback: (input) => {
    const { word, letter } = input

    // Convert both to lowercase for case-insensitive comparison
    const lowerWord = word.toLowerCase()
    const lowerLetter = letter.toLowerCase()

    // Count occurrences
    let count = 0
    for (const char of lowerWord) {
      if (char === lowerLetter) {
        count++
      }
    }

    // Return result as string (following the pattern of other tools in this project)
    return `The letter '${letter}' appears ${count} time(s) in '${word}'`
  },
})
// --8<-- [end:custom-tool]

// --8<-- [start:create-agent]
// Create an agent with tools with our custom letterCounter tool
const agent = new Agent({
  tools: [letterCounter],
})
// --8<-- [end:create-agent]

async function invokeAgent() {
  // --8<-- [start:invoke-agent]
  // Ask the agent a question that uses the available tools
  const message = `Tell me how many letter R's are in the word "strawberry" 🍓`
  const result = await agent.invoke(message)
  console.log(result.lastMessage)
  // --8<-- [end:invoke-agent]
}

// --8<-- [start:disable-console]
const quietAgent = new Agent({
  tools: [letterCounter],
  printer: false, // Disable console output
})
// --8<-- [end:disable-console]

// --8<-- [start:model-config]
// Check the model configuration
const myAgent = new Agent()
console.log(myAgent['model'].getConfig().modelId)
// Output: { modelId: 'global.anthropic.claude-sonnet-4-5-20250929-v1:0' }
// --8<-- [end:model-config]

// --8<-- [start:model-string]
// Create an agent with a specific model by passing the model ID string
const specificAgent = new Agent({
  model: 'anthropic.claude-sonnet-4-20250514-v1:0',
})
// --8<-- [end:model-string]

// --8<-- [start:bedrock-model]
import { BedrockModel } from '@strands-agents/sdk'

// Create a BedrockModel with custom configuration
const bedrockModel = new BedrockModel({
  modelId: 'anthropic.claude-sonnet-4-20250514-v1:0',
  region: 'us-west-2',
  temperature: 0.3,
})

const bedrockAgent = new Agent({ model: bedrockModel })
// --8<-- [end:bedrock-model]

// --8<-- [start:streaming-async]
// Async function that iterates over streamed agent events
async function processStreamingResponse() {
  const prompt = 'What is 25 * 48 and explain the calculation'

  // Stream the response as it's generated from the agent:
  for await (const event of agent.stream(prompt)) {
    console.log('Event:', event.type)
  }
}

// Run the streaming example
await processStreamingResponse()
// --8<-- [end:streaming-async]

async function accessMessages() {
  // --8<-- [start:agentMessages]
  // Access the agent's message array
  const result = await agent.invoke('What is the square root of 144?')
  console.log(agent.messages)
  // --8<-- [end:agentMessages]
}
