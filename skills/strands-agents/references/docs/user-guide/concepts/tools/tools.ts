import { Agent, tool, FunctionTool } from '@strands-agents/sdk'
import type { ToolContext, InvokableTool } from '@strands-agents/sdk'
import { notebook } from '@strands-agents/sdk/vended_tools/notebook'
import { fileEditor } from '@strands-agents/sdk/vended_tools/file_editor'
import { z } from 'zod'

// Basic tool example
async function basicToolExample() {
  // --8<-- [start:basic_tool]
  const weatherTool = tool({
    name: 'weather_forecast',
    description: 'Get weather forecast for a city',
    inputSchema: z.object({
      city: z.string().describe('The name of the city'),
      days: z.number().default(3).describe('Number of days for the forecast'),
    }),
    callback: (input) => {
      return `Weather forecast for ${input.city} for the next ${input.days} days...`
    },
  })
  // --8<-- [end:basic_tool]
}

// Zod schema validation example
async function zodSchemaExample() {
  // --8<-- [start:zod_schema]
  const calculateAreaTool = tool({
    name: 'calculate_area',
    description: 'Calculate area of a shape',
    inputSchema: z.object({
      shape: z.enum(['circle', 'rectangle']).describe('The shape type'),
      radius: z.number().optional().describe('Radius for circle'),
      width: z.number().optional().describe('Width for rectangle'),
      height: z.number().optional().describe('Height for rectangle'),
    }),
    callback: (input) => {
      if (input.shape === 'circle' && input.radius) {
        return 3.14159 * input.radius ** 2
      } else if (input.shape === 'rectangle' && input.width && input.height) {
        return input.width * input.height
      }
      return 0.0
    },
  })
  // --8<-- [end:zod_schema]
}

// Async tool example
async function asyncToolExample() {
  // --8<-- [start:async_tool]
  const callApiTool = tool({
    name: 'call_api',
    description: 'Call API asynchronously',
    inputSchema: z.object({}),
    callback: async (): Promise<string> => {
      await new Promise((resolve) => setTimeout(resolve, 5000)) // simulated api call
      return 'API result'
    },
  })

  const agent = new Agent({ tools: [callApiTool] })
  await agent.invoke('Can you call my API?')
  // --8<-- [end:async_tool]
}

// AsyncGenerator callback example
async function asyncGeneratorCallbackExample() {
  // --8<-- [start:async_generator_callback]
  const insertDataTool = tool({
    name: 'insert_data',
    description: 'Insert data with progress updates',
    inputSchema: z.object({
      table: z.string().describe('The table name'),
      data: z.record(z.string(), z.any()).describe('The data to insert'),
    }),
    callback: async function* (input: { table: string; data: Record<string, any> }): AsyncGenerator<string, string, unknown> {
      yield 'Starting data insertion...'
      await new Promise((resolve) => setTimeout(resolve, 1000))
      yield 'Validating data...'
      await new Promise((resolve) => setTimeout(resolve, 1000))
      return `Inserted data into ${input.table}: ${JSON.stringify(input.data)}`
    },
  })
  // --8<-- [end:async_generator_callback]
}

// Class-based tool example using FunctionTool
// --8<-- [start:class_tool]
class DatabaseTool extends FunctionTool {
  private connection: { connected: boolean; db: string }

  constructor(connectionString: string) {
    // Establish connection first
    const connection = { connected: true, db: 'example_db' }

    // Initialize FunctionTool with the connection captured in closure
    super({
      name: 'query_database',
      description: 'Run a SQL query against the database',
      inputSchema: {
        type: 'object',
        properties: {
          sql: {
            type: 'string',
            description: 'The SQL query to execute',
          },
        },
        required: ['sql'],
      },
      callback: (input: any) => {
        // Uses the shared connection
        return { results: `Query results for: ${input.sql}`, connection }
      },
    })

    // Store connection for potential future use
    this.connection = connection
  }
}
// --8<-- [end:class_tool]

// Multiple tools in a class
// --8<-- [start:class_multiple_tools]
class DatabaseTools {
  private connection: { connected: boolean; db: string }
  readonly queryTool: ReturnType<typeof tool>
  readonly insertTool: ReturnType<typeof tool>

  constructor(connectionString: string) {
    // Establish connection
    this.connection = { connected: true, db: 'example_db' }

    const connection = this.connection

    // Create query tool
    this.queryTool = tool({
      name: 'query_database',
      description: 'Run a SQL query against the database',
      inputSchema: z.object({
        sql: z.string().describe('The SQL query to execute'),
      }),
      callback: (input) => {
        return { results: `Query results for: ${input.sql}`, connection }
      },
    })

    // Create insert tool
    this.insertTool = tool({
      name: 'insert_record',
      description: 'Insert a new record into the database',
      inputSchema: z.object({
        table: z.string().describe('The table name'),
        data: z.record(z.string(), z.any()).describe('The data to insert'),
      }),
      callback: (input) => {
        return `Inserted data into ${input.table}: ${JSON.stringify(input.data)}`
      },
    })
  }
}

// Usage
async function useDatabaseTools() {
  const dbTools = new DatabaseTools('example_connection_string')
  const agent = new Agent({
    tools: [dbTools.queryTool, dbTools.insertTool],
  })
}
// --8<-- [end:class_multiple_tools]

// ToolContext example
async function toolContextExample() {
  // --8<-- [start:tool_context]
  const getAgentInfoTool = tool({
    name: 'get_agent_info',
    description: 'Get information about the agent',
    inputSchema: z.object({}),
    callback: (input, context?: ToolContext): string => {
      // Access agent state through context
      return `Agent has ${context?.agent.messages.length} messages in history`
    },
  })

  const getToolUseIdTool = tool({
    name: 'get_tool_use_id',
    description: 'Get the tool use ID',
    inputSchema: z.object({}),
    callback: (input, context?: ToolContext): string => {
      return `Tool use is ${context?.toolUse.toolUseId}`
    },
  })

  const agent = new Agent({ tools: [getAgentInfoTool, getToolUseIdTool] })

  await agent.invoke('What is your information?')
  await agent.invoke('What is the tool use id?')
  // --8<-- [end:tool_context]
}

// ToolContext with invocation state
async function toolContextInvocationStateExample() {
  // --8<-- [start:tool_context_invocation_state]
  const apiCallTool = tool({
    name: 'api_call',
    description: 'Make an API call with user context',
    inputSchema: z.object({
      query: z.string().describe('The search query to send to the API'),
    }),
    callback: async (input, context) => {
      if (!context) {
        throw new Error('Context is required')
      }

      // Access state via context.agent.state
      const userId = context.agent.state.get('userId') as string | undefined

      const response = await fetch('https://api.example.com/search', {
        method: 'GET',
        headers: {
          'X-User-ID': userId || '',
        },
      })

      return response.json()
    },
  })

  const agent = new Agent({ tools: [apiCallTool] })

  // Set state before invoking
  agent.state.set('userId', 'user123')

  const result = await agent.invoke('Get my profile data')
  // --8<-- [end:tool_context_invocation_state]
}

// Vended tools example
async function vendedToolsExample() {
  // --8<-- [start:vended_tools]
  const agent = new Agent({
    tools: [notebook, fileEditor],
  })
  // --8<-- [end:vended_tools]
}

// Adding tools to agents example
async function addingToolsExample() {
  // --8<-- [start:adding_tools]
  const agent = new Agent({
    tools: [fileEditor],
  })

  // Agent will use the file_editor tool when appropriate
  await agent.invoke('Show me the contents of a single file in this directory')
  // --8<-- [end:adding_tools]
}

// Direct invocation example
async function directInvocationExample() {
  // --8<-- [start:direct_invocation]
  // Create an agent with tools
  const agent = new Agent({
    tools: [notebook],
  })

  // Find the tool by name and cast to InvokableTool
  const notebookTool = agent.tools.find((t: { name: string }) => t.name === 'notebook') as InvokableTool<any, any>

  // Directly invoke the tool
  const result = await notebookTool.invoke(
    { mode: 'read', name: 'default' },
    {
      toolUse: {
        name: 'notebook',
        toolUseId: 'direct-invoke-123',
        input: { mode: 'read', name: 'default' },
      },
      agent: agent,
    }
  )

  console.log(result)
  // --8<-- [end:direct_invocation]
}

// Tool override configuration
async function toolOverrideExample() {
  // --8<-- [start:tool_override]
  const weatherTool = tool({
    name: 'get_weather',
    description: 'Retrieves weather forecast for a specified location',
    inputSchema: z.object({
      city: z.string().describe('The name of the city'),
      days: z.number().default(3).describe('Number of days for the forecast'),
    }),
    callback: (input: { city: any; days: any }) => {
      return `Weather forecast for ${input.city} for the next ${input.days} days...`
    },
  })
  // --8<-- [end:tool_override]
}

// Tool response format - success
async function toolResponseSuccessExample() {
  // --8<-- [start:tool_response_success]
  const weatherTool = tool({
    name: 'get_weather',
    description: 'Retrieves weather forecast for a specified location',
    inputSchema: z.object({
      city: z.string().describe('The name of the city'),
      days: z.number().default(3).describe('Number of days for the forecast'),
    }),
    callback: (input: { city: any; days: any }) => {
      return {
        city: input.city,
        days: input.days,
        forecast: `Weather forecast for ${input.city} for the next ${input.days} days...`
      }
    },
  })
  // --8<-- [end:tool_response_success]
}

// Tool streaming example
async function toolStreamingExample() {
  // --8<-- [start:tool_streaming]
  const processDatasetTool = tool({
    name: 'process_dataset',
    description: 'Process records with progress updates',
    inputSchema: z.object({
      records: z.number().describe('Number of records to process'),
    }),
    callback: async function* (input: { records: number }) : AsyncGenerator<string, string, unknown> {
      const start = Date.now()

      for (let i = 0; i < input.records; i++) {
        await new Promise((resolve) => setTimeout(resolve, 100))
        if (i % 10 === 0) {
          const elapsed = (Date.now() - start) / 1000
          yield `Processed ${i}/${input.records} records in ${elapsed.toFixed(1)}s`
        }
      }

      const elapsed = (Date.now() - start) / 1000
      return `Completed ${input.records} records in ${elapsed.toFixed(1)}s`
    },
  })

  const agent = new Agent({ tools: [processDatasetTool] })

  for await (const event of agent.stream('Process 50 records')) {
    if (event.type === 'toolStreamEvent') {
      console.log(`Progress: ${event.data}`)
    }
  }
  // --8<-- [end:tool_streaming]
}

// Natural language invocation
async function naturalLanguageInvocationExample() {
  // --8<-- [start:natural_language_invocation]
  const agent = new Agent({
    tools: [notebook],
  })

  // Agent decides when to use tools based on the request
  await agent.invoke('Please read the default notebook')
  // --8<-- [end:natural_language_invocation]
}

// Search database tool with comprehensive description
async function searchDatabaseExample() {
  // --8<-- [start:search_database]
const searchDatabaseTool = tool({
  name: 'search_database',
  description: `Search the product database for items matching the query string.

Use this tool when you need to find detailed product information based on keywords,
product names, or categories. The search is case-insensitive and supports fuzzy
matching to handle typos and variations in search terms.

This tool connects to the enterprise product catalog database and performs a semantic
search across all product fields, providing comprehensive results with all available
product metadata.

Example response:
[
  {
    "id": "P12345",
    "name": "Ultra Comfort Running Shoes",
    "description": "Lightweight running shoes with...",
    "price": 89.99,
    "category": ["Footwear", "Athletic", "Running"]
  }
]

Notes:
- This tool only searches the product catalog and does not provide inventory or availability information
- Results are cached for 15 minutes to improve performance
- The search index updates every 6 hours, so very recent products may not appear
- For real-time inventory status, use a separate inventory check tool`,
  inputSchema: z.object({
    query: z
      .string()
      .describe('The search string (product name, category, or keywords). Example: "red running shoes"'),
    maxResults: z.number().default(10).describe('Maximum number of results to return (default: 10, range: 1-100)'),
  }),
  callback: () => {
    // Implementation would go here
    return []
  },
})
  // --8<-- [end:search_database]
}
