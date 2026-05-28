import { Agent, tool } from '@strands-agents/sdk'
import { notebook } from '@strands-agents/sdk/vended_tools/notebook'
import type { AgentStreamEvent } from '@strands-agents/sdk'
import { z } from 'zod'

// Quick Examples - Async Iterator Pattern
async function quickExampleAsyncIterator() {
  // --8<-- [start:quick_example_async_iterator]
  const agent = new Agent({ tools: [notebook] })

  for await (const event of agent.stream('Calculate 2+2')) {
    if (event.type === 'modelContentBlockDeltaEvent' && event.delta.type === 'textDelta') {
      // Print out the model text delta event data
      process.stdout.write(event.delta.text)
    }
  }
  console.log("\nDone!")
  // --8<-- [end:quick_example_async_iterator]
}

// Agent Loop Lifecycle Example - Shared processor
async function agentLoopLifecycleExample() {
  const agent = new Agent({ tools: [notebook], printer: false})

  // --8<-- [start:agent_loop_lifecycle]
  function processEvent(event: AgentStreamEvent): void {
    // Track agent loop lifecycle
    switch (event.type) {
      case 'beforeInvocationEvent':
        console.log('🔄 Agent loop initialized')
        break
      case 'beforeModelCallEvent':
        console.log('▶️ Agent loop cycle starting')
        break
      case 'afterModelCallEvent':
        console.log(`📬 New message created: ${event.stopData?.message.role}`)
        break
      case 'beforeToolsEvent':
        console.log("About to execute tool!")
        break
      case 'beforeToolsEvent':
        console.log("Finished execute tool!")
        break
      case 'afterInvocationEvent':
        console.log('✅ Agent loop completed')
        break
    }

    // Track tool usage
    if (event.type === 'modelContentBlockStartEvent' && event.start?.type === 'toolUseStart') {
      console.log(`\n🔧 Using tool: ${event.start.name}`)
    }

    // Show text snippets
    if (event.type === 'modelContentBlockDeltaEvent' && event.delta.type === 'textDelta') {
      process.stdout.write(event.delta.text)
    }
  }
  const responseGenerator = agent.stream(
    'What is the capital of France and what is 42+7? Record in the notebook.'
  )
  for await (const event of responseGenerator) {
    processEvent(event)
  }
  // --8<-- [end:agent_loop_lifecycle]
}

// Sub-Agent Streaming Example - Using agents as tools
async function subAgentStreamingExample() {
  // --8<-- [start:sub_agent_basic]

  // Create the math agent
  const mathAgent = new Agent({
    systemPrompt: 'You are a math expert. Answer a math problem in one sentence',
    printer: false,
  })

  const calculator = tool({
    name: 'mathAgent',
    description: 'Agent that calculates the answer to a math problem input.',
    inputSchema: z.object({input: z.string()}),
    callback: async function* (input): AsyncGenerator<string, string, unknown> {
      // Stream from the sub-agent
      const generator = mathAgent.stream(input.input)
      let result = await generator.next()
      while (!result.done) {
        // Process events from the sub-agent
        if (result.value.type === 'modelContentBlockDeltaEvent' && result.value.delta.type === 'textDelta') {
          yield result.value.delta.text
        }
        result = await generator.next()
      }
      return result.value.lastMessage.content[0]!.type === "textBlock" 
        ? result.value.lastMessage.content[0]!.text
        : result.value.lastMessage.content[0]!.toString()
    }
  })

  const agent = new Agent({tools: [calculator]})
  for await (const event of agent.stream("What is 2 * 3? Use your tool.")) {
    if (event.type === "toolStreamEvent") {
      console.log(`Tool Event: ${JSON.stringify(event.data)}`)
    }
  }
  console.log("\nDone!")
  
  // --8<-- [end:sub_agent_basic]
}