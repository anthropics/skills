import {
  BedrockAgentCoreClient,
  InvokeAgentRuntimeCommand,
} from '@aws-sdk/client-bedrock-agentcore'

const input_text = 'Calculate 5 plus 3 using the calculator tool'

const client = new BedrockAgentCoreClient({
  region: 'ap-southeast-2',
})

const input = {
  // Generate unique session ID
  runtimeSessionId: 'test-session-' + Date.now() + '-' + Math.random().toString(36).substring(7),
  // Replace with your actual runtime ARN
  agentRuntimeArn:
    'arn:aws:bedrock-agentcore:ap-southeast-2:YOUR_ACCOUNT_ID:runtime/my-agent-service-XXXXXXXXXX',
  qualifier: 'DEFAULT',
  payload: new TextEncoder().encode(input_text),
}

const command = new InvokeAgentRuntimeCommand(input)
const response = await client.send(command)
const textResponse = await response.response.transformToString()

console.log('Response:', textResponse)
