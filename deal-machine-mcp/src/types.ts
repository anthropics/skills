/**
 * Type definitions for Deal Machine MCP Server
 */

export interface Lead {
  id?: string;
  address: string;
  city: string;
  state: string;
  zip: string;
  owner_name?: string;
  owner_phone?: string;
  owner_email?: string;
  property_type?: string;
  estimated_value?: number;
  estimated_equity?: number;
  bedrooms?: number;
  bathrooms?: number;
  square_feet?: number;
  year_built?: number;
  last_sale_date?: string;
  last_sale_price?: number;
  status?: string;
  tags?: string[];
  notes?: string;
  created_at?: string;
  updated_at?: string;
}

export interface LeadAnalysis {
  lead: Lead;
  likelihood_score: number; // 0-100
  confidence_level: string; // "low", "medium", "high"
  key_indicators: string[];
  risk_factors: string[];
  opportunity_factors: string[];
  recommended_action: string;
  estimated_roi_potential: string;
}

export interface MarketingCampaign {
  name: string;
  budget: number;
  target_count: number;
  cost_per_piece: number;
  estimated_response_rate: number;
  estimated_leads: number;
  campaign_type: string; // "direct_mail", "postcards", "letters", "combo"
  message_template?: string;
  target_criteria: {
    min_equity?: number;
    property_types?: string[];
    locations?: string[];
    price_range?: {
      min: number;
      max: number;
    };
  };
}

export interface CampaignPerformance {
  campaign_name: string;
  sent_count: number;
  delivered_count: number;
  response_count: number;
  response_rate: number;
  cost_per_response: number;
  total_cost: number;
  roi_estimate: number;
  active_leads: number;
  deals_closed: number;
  revenue_generated: number;
}

export interface InvestmentStrategy {
  budget: number;
  timeline_months: number;
  target_market: string[];
  property_types: string[];
  investment_goals: string[];
  recommended_lead_count: number;
  monthly_marketing_budget: number;
  expected_deal_flow: number;
  strategy_description: string;
  action_steps: string[];
}

export interface DealMachineAPIResponse<T = any> {
  success: boolean;
  data?: T;
  error?: string;
  message?: string;
}
