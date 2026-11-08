import { Agent, tool } from '@strands-agents/sdk'
import type { ToolContext } from '@strands-agents/sdk'
import { z } from 'zod'

// --8<-- [start:conversation_manager_import]

import { SlidingWindowConversationManager } from '@strands-agents/sdk'

// --8<-- [end:conversation_manager_import]

// Conversation history example
async function conversationHistoryExample() {
  // --8<-- [start:conversation_history]
  // Create an agent
  const agent = new Agent()

  // Send a message and get a response
  await agent.invoke('Hello!')

  // Access the conversation history
  console.log(agent.messages) // Shows all messages exchanged so far
  // --8<-- [end:conversation_history]
}

// Message initialization example
async function messageInitializationExample() {
  // --8<-- [start:message_initialization]
  // Create an agent with initial messages
  const agent = new Agent({
    messages: [
      { role: 'user', content: [{ text: 'Hello, my name is Strands!' }] },
      { role: 'assistant', content: [{ text: 'Hi there! How can I help you today?' }] },
    ],
  })

  // Continue the conversation
  await agent.invoke("What's my name?")
  // --8<-- [end:message_initialization]
}

// conversation_manager example
async function conversationManagerExample() {
  // --8<-- [start:conversation_manager]
  // Create a conversation manager with custom window size
  // By default, SlidingWindowConversationManager is used even if not specified
  const conversationManager = new SlidingWindowConversationManager({
    windowSize: 10
  })
  
  const agent = new Agent({
    conversationManager
  })
  // --8<-- [end:conversation_manager]
}

// Agent state basic usage example
async function agentStateBasicExample() {
  // --8<-- [start:agent_state_basic]
  // Create an agent with initial state
  const agent = new Agent({
    state: { user_preferences: { theme: 'dark' }, session_count: 0 },
  })

  // Access state values
  const theme = agent.state.get('user_preferences')
  console.log(theme) // { theme: 'dark' }

  // Set new state values
  agent.state.set('last_action', 'login')
  agent.state.set('session_count', 1)

  // Get state values individually
  console.log(agent.state.get('user_preferences'))
  console.log(agent.state.get('session_count'))

  // Delete state values
  agent.state.delete('last_action')
  // --8<-- [end:agent_state_basic]
}

// State validation example
async function stateValidationExample() {
  // --8<-- [start:state_validation]
  const agent = new Agent()

  // Valid JSON-serializable values
  agent.state.set('string_value', 'hello')
  agent.state.set('number_value', 42)
  agent.state.set('boolean_value', true)
  agent.state.set('list_value', [1, 2, 3])
  agent.state.set('dict_value', { nested: 'data' })
  agent.state.set('null_value', null)

  // Invalid values will raise an error
  try {
    agent.state.set('function', () => 'test') // Not JSON serializable
  } catch (error) {
    console.log(`Error: ${error}`)
  }
  // --8<-- [end:state_validation]
}

// State in tools example
async function stateInToolsExample() {
  // --8<-- [start:state_in_tools]
  const trackUserActionTool = tool({
    name: 'track_user_action',
    description: 'Track user actions in agent state',
    inputSchema: z.object({
      action: z.string().describe('The action to track'),
    }),
    callback: (input, context?: ToolContext) => {
      if (!context) {
        throw new Error('Context is required')
      }

      // Get current action count
      const actionCount = (context.agent.state.get('action_count') as number) || 0

      // Update state
      context.agent.state.set('action_count', actionCount + 1)
      context.agent.state.set('last_action', input.action)

      return `Action '${input.action}' recorded. Total actions: ${actionCount + 1}`
    },
  })

  const getUserStatsTool = tool({
    name: 'get_user_stats',
    description: 'Get user statistics from agent state',
    inputSchema: z.object({}),
    callback: (input, context?: ToolContext) => {
      if (!context) {
        throw new Error('Context is required')
      }

      const actionCount = (context.agent.state.get('action_count') as number) || 0
      const lastAction = (context.agent.state.get('last_action') as string) || 'none'

      return `Actions performed: ${actionCount}, Last action: ${lastAction}`
    },
  })

  // Create agent with tools
  const agent = new Agent({
    tools: [trackUserActionTool, getUserStatsTool],
  })

  // Use tools that modify and read state
  await agent.invoke('Track that I logged in')
  await agent.invoke('Track that I viewed my profile')
  console.log(`Actions taken: ${agent.state.get('action_count')}`)
  console.log(`Last action: ${agent.state.get('last_action')}`)
  // --8<-- [end:state_in_tools]
}
