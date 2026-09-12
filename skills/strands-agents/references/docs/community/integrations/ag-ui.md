# Build chat experiences with AG-UI and CopilotKit

{{ community_contribution_banner }}

As an agent builder, you want users to interact with your agents through a rich
and responsive interface. Building UIs from scratch requires a lot of effort,
especially to support streaming events and client state. That's exactly what
[AG-UI](https://docs.ag-ui.com/) was designed for - rich user experiences
directly connected to an agent.

[AG-UI](https://github.com/ag-ui-protocol/ag-ui) provides a consistent interface
to empower rich clients across technology stacks, from mobile to the web and
even the command line. There are a number of different clients that support
AG-UI:

- [CopilotKit](https://copilotkit.ai) provides tooling and components to tightly integrate your agent with web applications
- Clients for [Kotlin](https://github.com/ag-ui-protocol/ag-ui/tree/main/sdks/community/kotlin), [Java](https://github.com/ag-ui-protocol/ag-ui/tree/main/sdks/community/java), [Go](https://github.com/ag-ui-protocol/ag-ui/tree/main/sdks/community/go/example/client), and [CLI implementations](https://github.com/ag-ui-protocol/ag-ui/tree/main/apps/client-cli-example/src) in TypeScript

This tutorial uses CopilotKit to create a sample app backed by a Strands agent that
demonstrates some of the features supported by AG-UI.

## Quickstart

To get started, let's create a sample application with a Strands agent and a simple
web client:

```
npx copilotkit create -f aws-strands-py
```

### Chat

Chat is a familiar interface for exposing your agent, and AG-UI handles
streaming messages between your users and agents:

```jsx title="src/app/page.tsx"
const labels = {
    title: "Popup Assistant",
    initial: "Hi, there! You\'re chatting with an agent. This agent comes with a few tools to get you started."
  }
<CopilotSidebar
  clickOutsideToClose={false}
  defaultOpen={true}
  labels={labels}
/>
```

Learn more about the chat UI
[in the CopilotKit docs](https://docs.copilotkit.ai/aws-strands/agentic-chat-ui).

### Tool Based Generative UI (Rendering Tools)

AG-UI lets you share tool information with a Generative UI so that it can be
displayed to users:

```jsx title="src/app/page.tsx"
useCopilotAction({
  name: "get_weather",
  description: "Get the weather for a given location.",
  available: "disabled",
  parameters: [
    { name: "location", type: "string", required: true },
  ],
  render: ({ args }) => {
    return <WeatherCard location={args.location} themeColor={themeColor} />
  },
});
```

Learn more about the Tool-based Generative UI
[in the CopilotKit docs](https://docs.copilotkit.ai/aws-strands/generative-ui/backend-tools).

### Shared State

Strands agents are stateful, and synchronizing that state between your agents and
your UIs enables powerful and fluid user experiences. State can be synchronized
both ways so agents are automatically aware of changes made by your user or
other parts of your application:

```jsx
const { state, setState } = useCoAgent<AgentState>({
  name: "my_agent",
  initialState: {
    proverbs: [
      "CopilotKit may be new, but its the best thing since sliced bread.",
    ],
  },
})
```

Learn more about shared state
[in the CopilotKit docs](https://docs.copilotkit.ai/aws-strands/shared-state/in-app-agent-read).

### Try it out!

```
npm install && npm run dev
```

## Deploy to AgentCore

Once you've built your agent with AG-UI, you can deploy it to AWS Bedrock AgentCore for production use. Install the [bedrock-agentcore](https://pypi.org/project/bedrock-agentcore/) CLI tool to get started.

!!! note
    This guide is adapted for AG-UI. For general AgentCore deployment documentation, see [Deploy to Bedrock AgentCore](../../user-guide/deploy/deploy_to_bedrock_agentcore/index.md).

### Setup Authentication

First, configure Cognito for authentication:

```bash
agentcore identity setup-cognito
```

This creates a Cognito user pool and outputs:

- Pool ID
- Client ID
- Discovery URL

Follow the instructions for loading the environment variables:

```bash
export $(grep -v '^#' .agentcore_identity_user.env | xargs)
```

### Configure Your Agent

Navigate to your agent directory and run:

```bash
cd agent
agentcore configure -e main.py
```

Respond to the prompts:

1. **Agent name**: Press Enter to use the inferred name `main`, or provide your own
2. **Dependency file**: Enter `pyproject.toml`
3. **Deployment type**: Enter `2` for Container
4. **Execution role**: Press Enter to auto-create
5. **ECR Repository**: Press Enter to auto-create
6. **OAuth authorizer**: Enter `yes`
7. **OAuth discovery URL**: Paste the Discovery URL from the previous step
8. **OAuth client IDs**: Paste the Client ID from the previous step
9. **OAuth audience/scopes/claims**: Press Enter to skip
10. **Request header allowlist**: Enter `no`
11. **Memory configuration**: Enter `s` to skip

### Launch Your Agent

Deploy your agent with the required environment variables. AgentCore Runtime requires:

- `POST /invocations` - Agent interaction endpoint (configured via `AGENT_PATH`)
- `GET /ping` - Health check endpoint (created automatically by AG-UI)

```bash
agentcore launch --env AGENT_PORT=8080 --env AGENT_PATH=/invocations --env OPENAI_API_KEY=<your-api-key>
```

Your agent is now deployed and accessible through AgentCore!

### Connect Your Frontend

Return to the root directory and configure the environment variables to connect your UI to the deployed agent:

```bash
cd ..
export STRANDS_AGENT_URL="https://bedrock-agentcore.us-east-1.amazonaws.com/runtimes/{runtime-id}/invocations?accountId={account-id}&qualifier=DEFAULT"
export STRANDS_AGENT_BEARER_TOKEN=$(agentcore identity get-cognito-inbound-token)
```

Replace `{runtime-id}` and `{account-id}` with your actual values from the AgentCore deployment output.

Start the UI:

```bash
npm run dev:ui
```

## Resources

To see what other features you can build into your UI with AG-UI, refer to the CopilotKit docs:

- [Agentic Generative UI](https://docs.copilotkit.ai/aws-strands/generative-ui/agentic)
- [Frontend Actions](https://docs.copilotkit.ai/aws-strands/frontend-actions)

Or try them out in the [AG-UI Dojo](https://dojo.ag-ui.com).
