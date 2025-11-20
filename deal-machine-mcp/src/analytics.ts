/**
 * Analytics and Intelligence Layer for Deal Machine
 * Provides AI-powered lead analysis, ranking, and investment strategies
 */

import type { Lead, LeadAnalysis, MarketingCampaign, CampaignPerformance, InvestmentStrategy } from './types.js';

/**
 * Analyze a single lead and provide AI-powered insights
 */
export function analyzeLead(lead: Lead): LeadAnalysis {
  let score = 0;
  const indicators: string[] = [];
  const risks: string[] = [];
  const opportunities: string[] = [];

  // Equity analysis (most important factor)
  if (lead.estimated_equity && lead.estimated_value) {
    const equityPercent = (lead.estimated_equity / lead.estimated_value) * 100;
    if (equityPercent > 50) {
      score += 30;
      indicators.push(`High equity: ${equityPercent.toFixed(1)}%`);
      opportunities.push('Seller likely has financial flexibility for creative deals');
    } else if (equityPercent > 25) {
      score += 15;
      indicators.push(`Moderate equity: ${equityPercent.toFixed(1)}%`);
    } else {
      risks.push(`Low equity: ${equityPercent.toFixed(1)}% - may limit deal flexibility`);
    }
  }

  // Property age analysis
  if (lead.year_built) {
    const age = new Date().getFullYear() - lead.year_built;
    if (age > 30) {
      score += 15;
      indicators.push(`Older property (${age} years) - higher likelihood of deferred maintenance`);
      opportunities.push('Potential for value-add through renovations');
    } else if (age < 10) {
      score += 5;
      indicators.push(`Newer property (${age} years)`);
    }
  }

  // Last sale analysis
  if (lead.last_sale_date) {
    const saleDate = new Date(lead.last_sale_date);
    const monthsSinceSale = (Date.now() - saleDate.getTime()) / (1000 * 60 * 60 * 24 * 30);

    if (monthsSinceSale > 120) { // 10+ years
      score += 20;
      indicators.push(`Long-term ownership (${Math.floor(monthsSinceSale / 12)} years)`);
      opportunities.push('Long-term owners often more motivated to sell');
    } else if (monthsSinceSale < 12) {
      score += 5;
      risks.push('Recently purchased - may not be motivated to sell');
    }
  }

  // Property value analysis
  if (lead.estimated_value) {
    if (lead.estimated_value < 200000) {
      score += 10;
      opportunities.push('Lower price point - easier entry for investors');
    } else if (lead.estimated_value > 500000) {
      score += 5;
      indicators.push('Higher value property');
    }
  }

  // Owner contact information
  if (lead.owner_phone || lead.owner_email) {
    score += 10;
    opportunities.push('Contact information available for direct outreach');
  } else {
    risks.push('No direct contact information available');
  }

  // Property type analysis
  if (lead.property_type) {
    const type = lead.property_type.toLowerCase();
    if (type.includes('single') || type.includes('family')) {
      score += 10;
      indicators.push('Single-family home - most liquid property type');
    } else if (type.includes('multi')) {
      score += 15;
      indicators.push('Multi-family - potential for cash flow');
      opportunities.push('Income-producing property');
    }
  }

  // Determine confidence level
  let confidence = 'low';
  const dataPoints = [
    lead.estimated_equity,
    lead.estimated_value,
    lead.year_built,
    lead.last_sale_date,
    lead.property_type
  ].filter(Boolean).length;

  if (dataPoints >= 4) confidence = 'high';
  else if (dataPoints >= 2) confidence = 'medium';

  // Determine recommended action
  let action = '';
  if (score >= 70) {
    action = 'HIGH PRIORITY: Reach out immediately with a personalized offer. This lead shows strong motivation indicators.';
  } else if (score >= 50) {
    action = 'MEDIUM PRIORITY: Add to marketing campaign. Good potential but requires nurturing.';
  } else if (score >= 30) {
    action = 'LOW PRIORITY: Include in broad campaigns but don\'t invest heavily in personalization.';
  } else {
    action = 'HOLD: Monitor for changes in circumstances. Not recommended for immediate action.';
  }

  // Estimate ROI potential
  let roiPotential = 'Unknown';
  if (lead.estimated_equity && lead.estimated_value) {
    const equity = lead.estimated_equity;
    if (equity > 100000) roiPotential = 'High (>$100k potential equity)';
    else if (equity > 50000) roiPotential = 'Medium ($50k-$100k potential equity)';
    else roiPotential = 'Low (<$50k potential equity)';
  }

  return {
    lead,
    likelihood_score: Math.min(score, 100),
    confidence_level: confidence,
    key_indicators: indicators,
    risk_factors: risks,
    opportunity_factors: opportunities,
    recommended_action: action,
    estimated_roi_potential: roiPotential
  };
}

/**
 * Rank multiple leads by likelihood to sell
 */
export function rankLeads(leads: Lead[]): LeadAnalysis[] {
  const analyses = leads.map(analyzeLead);
  return analyses.sort((a, b) => b.likelihood_score - a.likelihood_score);
}

/**
 * Create a marketing campaign plan based on budget and criteria
 */
export function createCampaignPlan(
  budget: number,
  targetCount: number,
  campaignType: 'direct_mail' | 'postcards' | 'letters' | 'combo' = 'postcards'
): MarketingCampaign {
  // Average costs per piece (industry standards)
  const costs = {
    postcards: 0.85,
    letters: 1.50,
    direct_mail: 1.20,
    combo: 1.85
  };

  const costPerPiece = costs[campaignType];
  const maxMailings = Math.floor(budget / costPerPiece);
  const actualTarget = Math.min(targetCount, maxMailings);

  // Industry average response rates
  const responseRates = {
    postcards: 0.01,    // 1%
    letters: 0.015,     // 1.5%
    direct_mail: 0.012, // 1.2%
    combo: 0.02         // 2%
  };

  const responseRate = responseRates[campaignType];
  const estimatedLeads = Math.floor(actualTarget * responseRate);

  const campaign: MarketingCampaign = {
    name: `${campaignType.replace('_', ' ').toUpperCase()} Campaign`,
    budget,
    target_count: actualTarget,
    cost_per_piece: costPerPiece,
    estimated_response_rate: responseRate * 100,
    estimated_leads: estimatedLeads,
    campaign_type: campaignType,
    target_criteria: {
      min_equity: 50000,
      property_types: ['single_family', 'multi_family'],
      price_range: {
        min: 50000,
        max: 500000
      }
    }
  };

  // Add message template
  if (campaignType === 'letters') {
    campaign.message_template = 'Personalized handwritten-style letter expressing interest in purchasing the property';
  } else if (campaignType === 'postcards') {
    campaign.message_template = 'Eye-catching postcard with "We Buy Houses" message and call-to-action';
  }

  return campaign;
}

/**
 * Estimate campaign costs for budget planning
 */
export function estimateCampaignCost(
  leadCount: number,
  campaignType: 'direct_mail' | 'postcards' | 'letters' | 'combo',
  mailingFrequency: number = 1 // number of mailings per lead
): {
  total_cost: number;
  cost_breakdown: any;
  expected_responses: number;
  cost_per_response: number;
} {
  const costs = {
    postcards: 0.85,
    letters: 1.50,
    direct_mail: 1.20,
    combo: 1.85
  };

  const responseRates = {
    postcards: 0.01,
    letters: 0.015,
    direct_mail: 0.012,
    combo: 0.02
  };

  const costPerPiece = costs[campaignType];
  const totalPieces = leadCount * mailingFrequency;
  const totalCost = totalPieces * costPerPiece;
  const expectedResponses = Math.floor(totalPieces * responseRates[campaignType]);
  const costPerResponse = expectedResponses > 0 ? totalCost / expectedResponses : 0;

  return {
    total_cost: totalCost,
    cost_breakdown: {
      lead_count: leadCount,
      pieces_per_lead: mailingFrequency,
      total_pieces: totalPieces,
      cost_per_piece: costPerPiece
    },
    expected_responses: expectedResponses,
    cost_per_response: costPerResponse
  };
}

/**
 * Generate a personalized investment strategy
 */
export function generateInvestmentStrategy(
  budget: number,
  timelineMonths: number,
  goals: string[]
): InvestmentStrategy {
  const monthlyBudget = budget / timelineMonths;
  const marketingBudget = monthlyBudget * 0.3; // 30% for marketing

  // Calculate recommended lead count based on budget
  const avgCostPerLead = 1.20; // average direct mail cost
  const responseRate = 0.012;
  const mailingsPerMonth = Math.floor(marketingBudget / avgCostPerLead);
  const expectedLeads = Math.floor(mailingsPerMonth * responseRate);

  // Calculate expected deal flow (industry average: 1 deal per 10-20 leads)
  const dealsPerMonth = expectedLeads / 15;
  const totalDeals = Math.floor(dealsPerMonth * timelineMonths);

  let propertyTypes = ['single_family'];
  let targetMarkets = ['distressed_properties', 'long_term_owners'];

  if (budget > 100000) {
    propertyTypes.push('multi_family', 'commercial');
    targetMarkets.push('value_add_opportunities');
  }

  const actionSteps = [
    `Month 1: Build your lead list (target ${mailingsPerMonth * 3} properties)`,
    `Month 1-${timelineMonths}: Execute consistent monthly direct mail campaigns (${mailingsPerMonth} pieces/month)`,
    `Ongoing: Follow up with responding leads within 24 hours`,
    `Quarterly: Analyze campaign performance and adjust targeting`,
    `Expected outcome: ${totalDeals} deals over ${timelineMonths} months`
  ];

  if (goals.includes('wholesaling')) {
    actionSteps.push('Focus on deep-discount properties (60-70% of ARV) for wholesale assignments');
  }
  if (goals.includes('rental_income')) {
    actionSteps.push('Target properties with 1% rule potential (monthly rent = 1% of purchase price)');
  }
  if (goals.includes('fix_and_flip')) {
    actionSteps.push('Identify properties needing $20k-$50k in renovations for maximum ROI');
  }

  return {
    budget,
    timeline_months: timelineMonths,
    target_market: targetMarkets,
    property_types: propertyTypes,
    investment_goals: goals,
    recommended_lead_count: mailingsPerMonth * timelineMonths,
    monthly_marketing_budget: marketingBudget,
    expected_deal_flow: totalDeals,
    strategy_description: `Systematic direct mail campaign targeting ${mailingsPerMonth} properties per month with a focus on ${targetMarkets.join(', ')}. Expected to generate ${expectedLeads} leads per month and close ${totalDeals} deals over ${timelineMonths} months.`,
    action_steps: actionSteps
  };
}

/**
 * Track and analyze campaign performance
 */
export function analyzeCampaignPerformance(
  campaign: MarketingCampaign,
  actualSent: number,
  actualResponses: number,
  dealsTriggered: number = 0,
  revenueGenerated: number = 0
): CampaignPerformance {
  const responseRate = actualSent > 0 ? (actualResponses / actualSent) * 100 : 0;
  const totalCost = actualSent * campaign.cost_per_piece;
  const costPerResponse = actualResponses > 0 ? totalCost / actualResponses : 0;
  const roi = revenueGenerated > 0 ? ((revenueGenerated - totalCost) / totalCost) * 100 : 0;

  return {
    campaign_name: campaign.name,
    sent_count: actualSent,
    delivered_count: Math.floor(actualSent * 0.95), // assume 95% delivery rate
    response_count: actualResponses,
    response_rate: responseRate,
    cost_per_response: costPerResponse,
    total_cost: totalCost,
    roi_estimate: roi,
    active_leads: actualResponses - dealsTriggered,
    deals_closed: dealsTriggered,
    revenue_generated: revenueGenerated
  };
}
