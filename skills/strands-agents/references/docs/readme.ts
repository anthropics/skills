// --8<-- [start:basicAgent]
// Create a basic agent
import { Agent } from '@strands-agents/sdk'

// Create an agent with default settings
const agent = new Agent();

// Ask the agent a question
const response = await agent.invoke("Tell me about agentic AI");
console.log(response.lastMessage);
// --8<-- [end:basicAgent]
