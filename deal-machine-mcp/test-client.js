// Test the API client with proxy support
import { DealMachineAPIClient } from './dist/api-client.js';

const API_KEY = process.env.DEALMACHINE_API_KEY || 'your_api_key_here';

async function testClient() {
  console.log('Testing Deal Machine API Client...\n');

  const client = new DealMachineAPIClient(API_KEY);

  // Test 1: Get team members
  try {
    console.log('1. Testing getTeamMembers()');
    const members = await client.getTeamMembers();
    console.log('✅ SUCCESS');
    console.log('Response:', JSON.stringify(members, null, 2));
    console.log('\n');
  } catch (error) {
    console.log('❌ FAILED:', error.message);
    console.log('\n');
  }

  // Test 2: Add a test lead
  try {
    console.log('2. Testing addLead()');
    const result = await client.addLead({
      address: '123 Test Street',
      city: 'Austin',
      state: 'TX',
      zip: '78701',
      owner_name: 'Test Owner',
      notes: 'Test lead from MCP server',
    });
    console.log('✅ SUCCESS');
    console.log('Response:', JSON.stringify(result, null, 2));
    console.log('\n');
  } catch (error) {
    console.log('❌ FAILED:', error.message);
    console.log('\n');
  }

  // Test 3: Try to get leads (may not be supported)
  try {
    console.log('3. Testing getLeads()');
    const leads = await client.getLeads();
    console.log('✅ SUCCESS');
    console.log('Found', Array.isArray(leads) ? leads.length : 0, 'leads');
    console.log('\n');
  } catch (error) {
    console.log('❌ FAILED (expected if endpoint not available):', error.message);
    console.log('\n');
  }

  // Test 4: Rate limit status
  console.log('4. Checking rate limit status');
  const status = client.getRateLimitStatus();
  console.log('Rate limit status:', status);
  console.log('\n');

  console.log('Client testing complete!');
}

testClient().catch(console.error);
