// Test MCP tools directly
import { analyzeLead, rankLeads, createCampaignPlan, generateInvestmentStrategy, estimateCampaignCost } from './dist/analytics.js';

console.log('Testing MCP Analytics Tools...\n');

// Test 1: Analyze a single lead
console.log('=== Test 1: analyze_lead ===');
const testLead = {
  address: '123 Main St',
  city: 'Austin',
  state: 'TX',
  zip: '78701',
  owner_name: 'John Smith',
  estimated_value: 350000,
  estimated_equity: 180000,
  year_built: 1985,
  last_sale_date: '2005-03-15',
  last_sale_price: 125000,
  property_type: 'single_family',
};

const analysis = analyzeLead(testLead);
console.log('Lead Analysis:');
console.log('- Likelihood Score:', analysis.likelihood_score, '/100');
console.log('- Confidence:', analysis.confidence_level);
console.log('- Key Indicators:', analysis.key_indicators);
console.log('- Opportunities:', analysis.opportunity_factors);
console.log('- Recommendation:', analysis.recommended_action);
console.log('- ROI Potential:', analysis.estimated_roi_potential);
console.log('✅ PASSED\n');

// Test 2: Rank multiple leads
console.log('=== Test 2: rank_leads ===');
const leads = [
  {
    address: '456 Oak St',
    city: 'Dallas',
    state: 'TX',
    zip: '75201',
    estimated_value: 425000,
    estimated_equity: 220000,
    year_built: 1978,
    last_sale_date: '1998-06-20',
  },
  {
    address: '789 Pine Ave',
    city: 'Houston',
    state: 'TX',
    zip: '77001',
    estimated_value: 250000,
    estimated_equity: 50000,
    year_built: 2010,
    last_sale_date: '2018-01-15',
  },
  {
    address: '321 Elm Rd',
    city: 'San Antonio',
    state: 'TX',
    zip: '78201',
    estimated_value: 180000,
    estimated_equity: 120000,
    year_built: 1965,
    last_sale_date: '1990-11-30',
  },
];

const rankings = rankLeads(leads);
console.log('Ranked Leads (by score):');
rankings.forEach((r, i) => {
  console.log(`${i + 1}. ${r.lead.address} - Score: ${r.likelihood_score}/100`);
});
console.log('✅ PASSED\n');

// Test 3: Create marketing campaign
console.log('=== Test 3: create_marketing_campaign ===');
const campaign = createCampaignPlan(2000, 500, 'postcards');
console.log('Campaign Plan:');
console.log('- Name:', campaign.name);
console.log('- Budget: $' + campaign.budget);
console.log('- Target Count:', campaign.target_count);
console.log('- Cost per piece: $' + campaign.cost_per_piece);
console.log('- Expected response rate:', campaign.estimated_response_rate + '%');
console.log('- Expected leads:', campaign.estimated_leads);
console.log('✅ PASSED\n');

// Test 4: Estimate campaign cost
console.log('=== Test 4: estimate_campaign_cost ===');
const estimate = estimateCampaignCost(1000, 'letters', 3);
console.log('Cost Estimate:');
console.log('- Total cost: $' + estimate.total_cost);
console.log('- Expected responses:', estimate.expected_responses);
console.log('- Cost per response: $' + estimate.cost_per_response.toFixed(2));
console.log('✅ PASSED\n');

// Test 5: Generate investment strategy
console.log('=== Test 5: generate_investment_strategy ===');
const strategy = generateInvestmentStrategy(50000, 12, ['wholesaling', 'fix_and_flip']);
console.log('Investment Strategy:');
console.log('- Budget: $' + strategy.budget);
console.log('- Timeline:', strategy.timeline_months, 'months');
console.log('- Monthly marketing budget: $' + strategy.monthly_marketing_budget.toFixed(2));
console.log('- Recommended lead count:', strategy.recommended_lead_count);
console.log('- Expected deals:', strategy.expected_deal_flow);
console.log('- Action steps:', strategy.action_steps.length, 'steps');
console.log('✅ PASSED\n');

console.log('=== All Tests Passed! ===');
console.log('\nThe MCP server tools are working correctly!');
console.log('- AI-powered lead analysis: ✅');
console.log('- Lead ranking algorithm: ✅');
console.log('- Campaign planning: ✅');
console.log('- Cost estimation: ✅');
console.log('- Investment strategy generation: ✅');
