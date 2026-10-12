import { Agent } from '@strands-agents/sdk'
import express, { type Request, type Response } from 'express'
import { OpenAIModel } from '@strands-agents/sdk/openai'

// --8<-- [start: agent]
const PORT = Number(process.env.PORT) || 8080

// Note: Any supported model provider can be configured
// Automatically uses process.env.OPENAI_API_KEY
const model = new OpenAIModel()

const agent = new Agent({ model })

const app = express()

// Middleware to parse JSON
app.use(express.json())

// Health check endpoint
app.get('/ping', (_: Request, res: Response) =>
  res.json({
    status: 'healthy',
  })
)

// Agent invocation endpoint
app.post('/invocations', async (req: Request, res: Response) => {
  try {
    const { input } = req.body
    const prompt = input?.prompt || ''

    if (!prompt) {
      return res.status(400).json({
        detail: 'No prompt found in input. Please provide a "prompt" key in the input.'
      })
    }

    // Invoke the agent
    const result = await agent.invoke(prompt)

    const response = {
      message: result,
      timestamp: new Date().toISOString(),
      model: 'strands-agent',
    }

    return res.json({ output: response })
  } catch (err) {
    console.error('Error processing request:', err)
    return res.status(500).json({
      detail: `Agent processing failed: ${err instanceof Error ? err.message : 'Unknown error'}`
    })
  }
})

// Start server
app.listen(PORT, '0.0.0.0', () => {
  console.log(`🚀 Strands Agent Server listening on port ${PORT}`)
  console.log(`📍 Endpoints:`)
  console.log(`   POST http://0.0.0.0:${PORT}/invocations`)
  console.log(`   GET  http://0.0.0.0:${PORT}/ping`)
})
// --8<-- [end: agent]
