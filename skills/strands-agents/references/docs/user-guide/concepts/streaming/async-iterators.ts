import { Agent } from '@strands-agents/sdk'
import { notebook } from '@strands-agents/sdk/vended_tools/notebook'
import express from 'express'

// Basic Usage Example
async function basicUsage() {
  // --8<-- [start:basic_usage]
  // Initialize our agent without a printer
  const agent = new Agent({
    tools: [notebook],
    printer: false,
  })

  // Async function that iterates over streamed agent events
  async function processStreamingResponse(): Promise<void> {
    for await (const event of agent.stream('Record that my favorite color is blue!')) {
      console.log(event)
    }
  }

  // Run the agent
  await processStreamingResponse()
  // --8<-- [end:basic_usage]
}

async function expressExample() {
  // --8<-- [start:express_example]
  // Install Express: npm install express @types/express

  interface PromptRequest {
    prompt: string
  }

  async function handleStreamRequest(req: any, res: any) {
    console.log(`Got Request: ${JSON.stringify(req.body)}`)
    const { prompt } = req.body as PromptRequest

    const agent = new Agent({
      tools: [notebook],
      printer: false,
    })

    for await (const event of agent.stream(prompt)) {
      res.write(`${JSON.stringify(event)}\n`)
    }
    res.end()
  }

  const app = express()
  app.use(express.json())
  app.post('/stream', handleStreamRequest)
  app.listen(3000)
  // --8<-- [end:express_example]
}