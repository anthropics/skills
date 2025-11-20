#!/usr/bin/env node

/**
 * Deal Machine MCP Server
 * Your AI-powered real estate investment expert
 */

import { Server } from '@modelcontextprotocol/sdk/server/index.js';
import { StdioServerTransport } from '@modelcontextprotocol/sdk/server/stdio.js';
import {
  CallToolRequestSchema,
  ListToolsRequestSchema,
} from '@modelcontextprotocol/sdk/types.js';
import { z } from 'zod';
import { DealMachineAPIClient } from './api-client.js';
import {
  analyzeLead,
  rankLeads,
  createCampaignPlan,
  estimateCampaignCost,
  generateInvestmentStrategy,
  analyzeCampaignPerformance,
} from './analytics.js';
import type { Lead } from './types.js';

// Initialize API client
const apiKey = process.env.DEALMACHINE_API_KEY;
if (!apiKey) {
  console.error('Error: DEALMACHINE_API_KEY environment variable is required');
  console.error('Get your API key from: DealMachine Account > Automation > API Docs');
  process.exit(1);
}

const apiClient = new DealMachineAPIClient(apiKey);

// Initialize MCP server
const server = new Server(
  {
    name: 'deal-machine-mcp',
    version: '1.0.0',
  },
  {
    capabilities: {
      tools: {},
    },
  }
);

/**
 * Tool 1: Analyze Lead
 * Provides AI-powered analysis of a single lead
 */
const analyzeLeadSchema = z.object({
  lead: z.object({
    address: z.string().describe('Property address'),
    city: z.string().describe('City'),
    state: z.string().describe('State'),
    zip: z.string().describe('ZIP code'),
    owner_name: z.string().optional().describe('Property owner name'),
    owner_phone: z.string().optional().describe('Owner phone number'),
    owner_email: z.string().optional().describe('Owner email'),
    property_type: z.string().optional().describe('Type of property (e.g., single_family, multi_family)'),
    estimated_value: z.number().optional().describe('Estimated property value'),
    estimated_equity: z.number().optional().describe('Estimated equity in the property'),
    bedrooms: z.number().optional().describe('Number of bedrooms'),
    bathrooms: z.number().optional().describe('Number of bathrooms'),
    square_feet: z.number().optional().describe('Square footage'),
    year_built: z.number().optional().describe('Year the property was built'),
    last_sale_date: z.string().optional().describe('Date of last sale'),
    last_sale_price: z.number().optional().describe('Last sale price'),
  }).describe('Lead information to analyze'),
});

/**
 * Tool 2: Rank Leads
 * Ranks multiple leads by likelihood to sell
 */
const rankLeadsSchema = z.object({
  leads: z.array(z.object({
    address: z.string(),
    city: z.string(),
    state: z.string(),
    zip: z.string(),
    owner_name: z.string().optional(),
    property_type: z.string().optional(),
    estimated_value: z.number().optional(),
    estimated_equity: z.number().optional(),
    year_built: z.number().optional(),
    last_sale_date: z.string().optional(),
    last_sale_price: z.number().optional(),
  })).describe('Array of leads to rank'),
});

/**
 * Tool 3: Add Property Lead
 * Adds a new property lead to Deal Machine
 */
const addLeadSchema = z.object({
  address: z.string().describe('Property address'),
  city: z.string().describe('City'),
  state: z.string().describe('State'),
  zip: z.string().describe('ZIP code'),
  owner_name: z.string().optional().describe('Property owner name'),
  owner_phone: z.string().optional().describe('Owner phone number'),
  owner_email: z.string().optional().describe('Owner email'),
  property_type: z.string().optional().describe('Type of property'),
  estimated_value: z.number().optional().describe('Estimated property value'),
  notes: z.string().optional().describe('Additional notes about the lead'),
  tags: z.array(z.string()).optional().describe('Tags to categorize the lead'),
});

/**
 * Tool 4: Update Lead Status
 * Updates a lead's status and adds notes
 */
const updateLeadSchema = z.object({
  lead_id: z.string().describe('ID of the lead to update'),
  status: z.string().optional().describe('New status for the lead'),
  notes: z.string().optional().describe('Notes to add to the lead'),
  tags: z.array(z.string()).optional().describe('Tags to add to the lead'),
});

/**
 * Tool 5: Create Marketing Campaign Plan
 * Creates a detailed marketing campaign plan based on budget
 */
const createCampaignSchema = z.object({
  budget: z.number().positive().describe('Total budget for the campaign'),
  target_count: z.number().positive().describe('Number of properties to target'),
  campaign_type: z.enum(['direct_mail', 'postcards', 'letters', 'combo']).describe('Type of marketing campaign'),
  min_equity: z.number().optional().describe('Minimum equity requirement for targeting'),
  property_types: z.array(z.string()).optional().describe('Types of properties to target'),
});

/**
 * Tool 6: Estimate Campaign Cost
 * Estimates the cost and ROI of a marketing campaign
 */
const estimateCostSchema = z.object({
  lead_count: z.number().positive().describe('Number of leads to mail'),
  campaign_type: z.enum(['direct_mail', 'postcards', 'letters', 'combo']).describe('Type of campaign'),
  mailing_frequency: z.number().positive().default(1).describe('Number of mailings per lead'),
});

/**
 * Tool 7: Track Campaign Performance
 * Monitors and analyzes campaign performance metrics
 */
const trackCampaignSchema = z.object({
  campaign_name: z.string().describe('Name of the campaign'),
  budget: z.number().describe('Campaign budget'),
  target_count: z.number().describe('Target count'),
  cost_per_piece: z.number().describe('Cost per piece'),
  campaign_type: z.string().describe('Campaign type'),
  sent_count: z.number().describe('Number of pieces sent'),
  responses: z.number().describe('Number of responses received'),
  deals_closed: z.number().optional().default(0).describe('Number of deals closed'),
  revenue_generated: z.number().optional().default(0).describe('Revenue generated'),
});

/**
 * Tool 8: Generate Investment Strategy
 * Creates a personalized investment strategy based on goals and budget
 */
const generateStrategySchema = z.object({
  budget: z.number().positive().describe('Total investment budget'),
  timeline_months: z.number().positive().describe('Investment timeline in months'),
  goals: z.array(z.enum(['wholesaling', 'rental_income', 'fix_and_flip', 'buy_and_hold']))
    .describe('Investment goals'),
});

/**
 * Tool 9: Find High-Value Leads
 * Searches for leads with high investment potential
 */
const findHighValueSchema = z.object({
  min_equity: z.number().optional().describe('Minimum equity threshold'),
  max_price: z.number().optional().describe('Maximum property price'),
  property_types: z.array(z.string()).optional().describe('Property types to search for'),
  min_age: z.number().optional().describe('Minimum property age in years'),
});

/**
 * Tool 10: Get Lead Details
 * Retrieves detailed information about a specific lead
 */
const getLeadSchema = z.object({
  lead_id: z.string().describe('ID of the lead to retrieve'),
});

// Register all tools
server.setRequestHandler(ListToolsRequestSchema, async () => {
  return {
    tools: [
      {
        name: 'analyze_lead',
        description: 'Analyze a property lead with AI-powered insights including likelihood to sell, risk factors, opportunities, and recommended actions. Provides a comprehensive score (0-100) and detailed investment recommendations.',
        inputSchema: {
          type: 'object',
          properties: {
            lead: {
              type: 'object',
              properties: {
                address: { type: 'string', description: 'Property address' },
                city: { type: 'string', description: 'City' },
                state: { type: 'string', description: 'State' },
                zip: { type: 'string', description: 'ZIP code' },
                owner_name: { type: 'string', description: 'Property owner name' },
                owner_phone: { type: 'string', description: 'Owner phone number' },
                owner_email: { type: 'string', description: 'Owner email' },
                property_type: { type: 'string', description: 'Type of property' },
                estimated_value: { type: 'number', description: 'Estimated property value' },
                estimated_equity: { type: 'number', description: 'Estimated equity' },
                bedrooms: { type: 'number', description: 'Number of bedrooms' },
                bathrooms: { type: 'number', description: 'Number of bathrooms' },
                square_feet: { type: 'number', description: 'Square footage' },
                year_built: { type: 'number', description: 'Year built' },
                last_sale_date: { type: 'string', description: 'Last sale date' },
                last_sale_price: { type: 'number', description: 'Last sale price' },
              },
              required: ['address', 'city', 'state', 'zip'],
            },
          },
          required: ['lead'],
        },
      },
      {
        name: 'rank_leads',
        description: 'Rank multiple property leads by likelihood to sell. Returns leads sorted from highest to lowest potential, with detailed analysis for each. Ideal for prioritizing your outreach efforts.',
        inputSchema: {
          type: 'object',
          properties: {
            leads: {
              type: 'array',
              description: 'Array of leads to rank',
              items: {
                type: 'object',
                properties: {
                  address: { type: 'string' },
                  city: { type: 'string' },
                  state: { type: 'string' },
                  zip: { type: 'string' },
                  owner_name: { type: 'string' },
                  property_type: { type: 'string' },
                  estimated_value: { type: 'number' },
                  estimated_equity: { type: 'number' },
                  year_built: { type: 'number' },
                  last_sale_date: { type: 'string' },
                  last_sale_price: { type: 'number' },
                },
                required: ['address', 'city', 'state', 'zip'],
              },
            },
          },
          required: ['leads'],
        },
      },
      {
        name: 'add_property_lead',
        description: 'Add a new property lead to your Deal Machine account. Automatically syncs with your Deal Machine dashboard for tracking and follow-up.',
        inputSchema: {
          type: 'object',
          properties: {
            address: { type: 'string', description: 'Property address' },
            city: { type: 'string', description: 'City' },
            state: { type: 'string', description: 'State' },
            zip: { type: 'string', description: 'ZIP code' },
            owner_name: { type: 'string', description: 'Owner name' },
            owner_phone: { type: 'string', description: 'Owner phone' },
            owner_email: { type: 'string', description: 'Owner email' },
            property_type: { type: 'string', description: 'Property type' },
            estimated_value: { type: 'number', description: 'Estimated value' },
            notes: { type: 'string', description: 'Additional notes' },
            tags: { type: 'array', items: { type: 'string' }, description: 'Tags' },
          },
          required: ['address', 'city', 'state', 'zip'],
        },
      },
      {
        name: 'update_lead_status',
        description: 'Update an existing lead\'s status, add notes, and manage tags. Keeps your pipeline organized and up-to-date.',
        inputSchema: {
          type: 'object',
          properties: {
            lead_id: { type: 'string', description: 'Lead ID' },
            status: { type: 'string', description: 'New status' },
            notes: { type: 'string', description: 'Notes to add' },
            tags: { type: 'array', items: { type: 'string' }, description: 'Tags to add' },
          },
          required: ['lead_id'],
        },
      },
      {
        name: 'create_marketing_campaign',
        description: 'Create a detailed marketing campaign plan based on your budget, target audience, and goals. Includes cost estimates, expected response rates, and ROI projections for direct mail, postcards, or letters.',
        inputSchema: {
          type: 'object',
          properties: {
            budget: { type: 'number', description: 'Total campaign budget' },
            target_count: { type: 'number', description: 'Number of properties to target' },
            campaign_type: {
              type: 'string',
              enum: ['direct_mail', 'postcards', 'letters', 'combo'],
              description: 'Type of campaign'
            },
            min_equity: { type: 'number', description: 'Minimum equity requirement' },
            property_types: { type: 'array', items: { type: 'string' }, description: 'Property types' },
          },
          required: ['budget', 'target_count', 'campaign_type'],
        },
      },
      {
        name: 'estimate_campaign_cost',
        description: 'Get detailed cost estimates for your marketing campaign including cost per piece, total cost, expected response rate, and cost per response. Helps with budget planning and ROI forecasting.',
        inputSchema: {
          type: 'object',
          properties: {
            lead_count: { type: 'number', description: 'Number of leads to mail' },
            campaign_type: {
              type: 'string',
              enum: ['direct_mail', 'postcards', 'letters', 'combo'],
              description: 'Campaign type'
            },
            mailing_frequency: { type: 'number', description: 'Mailings per lead', default: 1 },
          },
          required: ['lead_count', 'campaign_type'],
        },
      },
      {
        name: 'track_campaign_performance',
        description: 'Monitor and analyze your marketing campaign performance with detailed metrics including response rate, cost per response, ROI, and deal conversion rates.',
        inputSchema: {
          type: 'object',
          properties: {
            campaign_name: { type: 'string', description: 'Campaign name' },
            budget: { type: 'number', description: 'Campaign budget' },
            target_count: { type: 'number', description: 'Target count' },
            cost_per_piece: { type: 'number', description: 'Cost per piece' },
            campaign_type: { type: 'string', description: 'Campaign type' },
            sent_count: { type: 'number', description: 'Pieces sent' },
            responses: { type: 'number', description: 'Responses received' },
            deals_closed: { type: 'number', description: 'Deals closed', default: 0 },
            revenue_generated: { type: 'number', description: 'Revenue generated', default: 0 },
          },
          required: ['campaign_name', 'budget', 'target_count', 'cost_per_piece', 'campaign_type', 'sent_count', 'responses'],
        },
      },
      {
        name: 'generate_investment_strategy',
        description: 'Create a personalized real estate investment strategy based on your budget, timeline, and goals. Includes recommended lead counts, marketing budgets, expected deal flow, and detailed action steps.',
        inputSchema: {
          type: 'object',
          properties: {
            budget: { type: 'number', description: 'Total investment budget' },
            timeline_months: { type: 'number', description: 'Timeline in months' },
            goals: {
              type: 'array',
              items: {
                type: 'string',
                enum: ['wholesaling', 'rental_income', 'fix_and_flip', 'buy_and_hold']
              },
              description: 'Investment goals'
            },
          },
          required: ['budget', 'timeline_months', 'goals'],
        },
      },
      {
        name: 'find_high_value_leads',
        description: 'Search and filter leads to find high-value investment opportunities based on equity, price range, property type, and age. Returns leads that match your criteria sorted by potential.',
        inputSchema: {
          type: 'object',
          properties: {
            min_equity: { type: 'number', description: 'Minimum equity threshold' },
            max_price: { type: 'number', description: 'Maximum property price' },
            property_types: { type: 'array', items: { type: 'string' }, description: 'Property types' },
            min_age: { type: 'number', description: 'Minimum property age' },
          },
        },
      },
      {
        name: 'get_lead_details',
        description: 'Retrieve detailed information about a specific lead from your Deal Machine account including all property data, owner information, and interaction history.',
        inputSchema: {
          type: 'object',
          properties: {
            lead_id: { type: 'string', description: 'Lead ID to retrieve' },
          },
          required: ['lead_id'],
        },
      },
    ],
  };
});

// Handle tool execution
server.setRequestHandler(CallToolRequestSchema, async (request) => {
  const { name, arguments: args } = request.params;

  try {
    switch (name) {
      case 'analyze_lead': {
        const { lead } = analyzeLeadSchema.parse(args);
        const analysis = analyzeLead(lead as Lead);

        return {
          content: [
            {
              type: 'text',
              text: JSON.stringify(analysis, null, 2),
            },
          ],
        };
      }

      case 'rank_leads': {
        const { leads } = rankLeadsSchema.parse(args);
        const rankings = rankLeads(leads as Lead[]);

        return {
          content: [
            {
              type: 'text',
              text: JSON.stringify(rankings, null, 2),
            },
          ],
        };
      }

      case 'add_property_lead': {
        const leadData = addLeadSchema.parse(args);
        const result = await apiClient.addLead(leadData);

        // If tags were provided, add them
        if (leadData.tags && result.data?.id) {
          await apiClient.addTagsToLead(result.data.id, leadData.tags);
        }

        // If notes were provided, create a note
        if (leadData.notes && result.data?.id) {
          await apiClient.createNote(result.data.id, leadData.notes);
        }

        return {
          content: [
            {
              type: 'text',
              text: JSON.stringify(result, null, 2),
            },
          ],
        };
      }

      case 'update_lead_status': {
        const { lead_id, status, notes, tags } = updateLeadSchema.parse(args);

        // Update lead status
        if (status) {
          await apiClient.updateLead(lead_id, { status });
        }

        // Add tags if provided
        if (tags && tags.length > 0) {
          await apiClient.addTagsToLead(lead_id, tags);
        }

        // Add notes if provided
        if (notes) {
          await apiClient.createNote(lead_id, notes);
        }

        return {
          content: [
            {
              type: 'text',
              text: JSON.stringify({ success: true, message: 'Lead updated successfully' }, null, 2),
            },
          ],
        };
      }

      case 'create_marketing_campaign': {
        const { budget, target_count, campaign_type, min_equity, property_types } =
          createCampaignSchema.parse(args);

        const campaign = createCampaignPlan(budget, target_count, campaign_type);

        // Update criteria if provided
        if (min_equity) {
          campaign.target_criteria.min_equity = min_equity;
        }
        if (property_types) {
          campaign.target_criteria.property_types = property_types;
        }

        return {
          content: [
            {
              type: 'text',
              text: JSON.stringify(campaign, null, 2),
            },
          ],
        };
      }

      case 'estimate_campaign_cost': {
        const { lead_count, campaign_type, mailing_frequency } = estimateCostSchema.parse(args);
        const estimate = estimateCampaignCost(lead_count, campaign_type, mailing_frequency);

        return {
          content: [
            {
              type: 'text',
              text: JSON.stringify(estimate, null, 2),
            },
          ],
        };
      }

      case 'track_campaign_performance': {
        const data = trackCampaignSchema.parse(args);
        const campaign = {
          name: data.campaign_name,
          budget: data.budget,
          target_count: data.target_count,
          cost_per_piece: data.cost_per_piece,
          campaign_type: data.campaign_type,
          estimated_response_rate: 1.2,
          estimated_leads: 0,
          target_criteria: {
            property_types: [],
          },
        };

        const performance = analyzeCampaignPerformance(
          campaign,
          data.sent_count,
          data.responses,
          data.deals_closed,
          data.revenue_generated
        );

        return {
          content: [
            {
              type: 'text',
              text: JSON.stringify(performance, null, 2),
            },
          ],
        };
      }

      case 'generate_investment_strategy': {
        const { budget, timeline_months, goals } = generateStrategySchema.parse(args);
        const strategy = generateInvestmentStrategy(budget, timeline_months, goals);

        return {
          content: [
            {
              type: 'text',
              text: JSON.stringify(strategy, null, 2),
            },
          ],
        };
      }

      case 'find_high_value_leads': {
        const filters = findHighValueSchema.parse(args);

        try {
          // Try to get leads from API
          const leads = await apiClient.getLeads(filters);

          // Analyze and rank them
          const rankedLeads = rankLeads(leads);

          // Filter based on criteria
          let filtered = rankedLeads;

          if (filters.min_equity) {
            filtered = filtered.filter(a =>
              a.lead.estimated_equity && a.lead.estimated_equity >= filters.min_equity!
            );
          }

          if (filters.max_price) {
            filtered = filtered.filter(a =>
              a.lead.estimated_value && a.lead.estimated_value <= filters.max_price!
            );
          }

          if (filters.min_age && filters.min_age > 0) {
            const currentYear = new Date().getFullYear();
            filtered = filtered.filter(a =>
              a.lead.year_built && (currentYear - a.lead.year_built) >= filters.min_age!
            );
          }

          return {
            content: [
              {
                type: 'text',
                text: JSON.stringify({
                  total_found: filtered.length,
                  leads: filtered.slice(0, 20) // Return top 20
                }, null, 2),
              },
            ],
          };
        } catch (error) {
          // If API call fails, return helpful message
          return {
            content: [
              {
                type: 'text',
                text: JSON.stringify({
                  message: 'To find leads, please first add leads to your Deal Machine account or use the analyze_lead and rank_leads tools with your existing lead data.',
                  filters_applied: filters
                }, null, 2),
              },
            ],
          };
        }
      }

      case 'get_lead_details': {
        const { lead_id } = getLeadSchema.parse(args);
        const lead = await apiClient.getLead(lead_id);
        const analysis = analyzeLead(lead);

        return {
          content: [
            {
              type: 'text',
              text: JSON.stringify({ lead, analysis }, null, 2),
            },
          ],
        };
      }

      default:
        throw new Error(`Unknown tool: ${name}`);
    }
  } catch (error) {
    if (error instanceof z.ZodError) {
      throw new Error(`Invalid arguments: ${error.errors.map(e => `${e.path.join('.')}: ${e.message}`).join(', ')}`);
    }
    throw error;
  }
});

// Start server
async function main() {
  const transport = new StdioServerTransport();
  await server.connect(transport);
  console.error('Deal Machine MCP Server running on stdio');
}

main().catch((error) => {
  console.error('Fatal error:', error);
  process.exit(1);
});
