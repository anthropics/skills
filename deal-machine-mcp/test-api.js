// Quick API test script
import axios from 'axios';

const API_KEY = process.env.DEALMACHINE_API_KEY || 'your_api_key_here';
const BASE_URL = 'https://api.dealmachine.com/public/v1';

async function testEndpoints() {
  const client = axios.create({
    baseURL: BASE_URL,
    headers: {
      'Authorization': `Bearer ${API_KEY}`,
      'Content-Type': 'application/json',
      'Accept': 'application/json',
    },
    timeout: 10000,
    maxRedirects: 5,
    validateStatus: (status) => status < 500, // Don't throw on 4xx errors
  });

  console.log('Testing Deal Machine API endpoints...\n');

  // Test 1: Team members (known to work)
  try {
    console.log('1. Testing GET /team-members/');
    const response = await client.get('/team-members/');
    console.log('✅ SUCCESS:', response.status);
    console.log('Response:', JSON.stringify(response.data, null, 2).substring(0, 500));
    console.log('\n');
  } catch (error) {
    console.log('❌ FAILED:', error.response?.status, error.response?.data || error.message);
    console.log('\n');
  }

  // Test 2: Get leads
  try {
    console.log('2. Testing GET /leads/');
    const response = await client.get('/leads/');
    console.log('✅ SUCCESS:', response.status);
    console.log('Response:', JSON.stringify(response.data, null, 2).substring(0, 500));
    console.log('\n');
  } catch (error) {
    console.log('❌ FAILED:', error.response?.status, error.response?.data || error.message);
    console.log('\n');
  }

  // Test 3: Get lead statuses
  try {
    console.log('3. Testing GET /lead-statuses/');
    const response = await client.get('/lead-statuses/');
    console.log('✅ SUCCESS:', response.status);
    console.log('Response:', JSON.stringify(response.data, null, 2).substring(0, 500));
    console.log('\n');
  } catch (error) {
    console.log('❌ FAILED:', error.response?.status, error.response?.data || error.message);
    console.log('\n');
  }

  // Test 4: Get custom fields
  try {
    console.log('4. Testing GET /custom-fields/');
    const response = await client.get('/custom-fields/');
    console.log('✅ SUCCESS:', response.status);
    console.log('Response:', JSON.stringify(response.data, null, 2).substring(0, 500));
    console.log('\n');
  } catch (error) {
    console.log('❌ FAILED:', error.response?.status, error.response?.data || error.message);
    console.log('\n');
  }

  // Test 5: Get tags
  try {
    console.log('5. Testing GET /tags/');
    const response = await client.get('/tags/');
    console.log('✅ SUCCESS:', response.status);
    console.log('Response:', JSON.stringify(response.data, null, 2).substring(0, 500));
    console.log('\n');
  } catch (error) {
    console.log('❌ FAILED:', error.response?.status, error.response?.data || error.message);
    console.log('\n');
  }

  console.log('API testing complete!');
}

testEndpoints().catch(console.error);
