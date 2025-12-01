// Simpler API test to debug redirects
import axios from 'axios';

const API_KEY = process.env.DEALMACHINE_API_KEY || 'your_api_key_here';

async function testSimple() {
  console.log('Testing Deal Machine API with different approaches...\n');

  // Test 1: Try with trailing slash
  try {
    console.log('Test 1: GET https://api.dealmachine.com/public/v1/team-members/');
    const response = await axios({
      method: 'GET',
      url: 'https://api.dealmachine.com/public/v1/team-members/',
      headers: {
        'Authorization': `Bearer ${API_KEY}`,
        'Accept': 'application/json',
      },
      maxRedirects: 0, // Don't follow redirects
      validateStatus: () => true, // Don't throw on any status
    });
    console.log('Status:', response.status);
    console.log('Headers:', response.headers);
    if (response.data) {
      console.log('Data:', JSON.stringify(response.data, null, 2).substring(0, 300));
    }
    console.log('\n');
  } catch (error) {
    console.log('Error:', error.message);
    console.log('\n');
  }

  // Test 2: Try without trailing slash
  try {
    console.log('Test 2: GET https://api.dealmachine.com/public/v1/team-members');
    const response = await axios({
      method: 'GET',
      url: 'https://api.dealmachine.com/public/v1/team-members',
      headers: {
        'Authorization': `Bearer ${API_KEY}`,
        'Accept': 'application/json',
      },
      maxRedirects: 0,
      validateStatus: () => true,
    });
    console.log('Status:', response.status);
    console.log('Headers:', response.headers);
    if (response.data) {
      console.log('Data:', JSON.stringify(response.data, null, 2).substring(0, 300));
    }
    console.log('\n');
  } catch (error) {
    console.log('Error:', error.message);
    console.log('\n');
  }

  // Test 3: Try to add a lead (POST)
  try {
    console.log('Test 3: POST https://api.dealmachine.com/public/v1/leads/');
    const response = await axios({
      method: 'POST',
      url: 'https://api.dealmachine.com/public/v1/leads/',
      headers: {
        'Authorization': `Bearer ${API_KEY}`,
        'Content-Type': 'application/json',
        'Accept': 'application/json',
      },
      data: {
        address: '123 Test St',
        city: 'Test City',
        state: 'TX',
        zip: '12345',
      },
      maxRedirects: 0,
      validateStatus: () => true,
    });
    console.log('Status:', response.status);
    if (response.data) {
      console.log('Data:', JSON.stringify(response.data, null, 2).substring(0, 300));
    }
    console.log('\n');
  } catch (error) {
    console.log('Error:', error.message);
    console.log('\n');
  }

  // Test 4: Check what happens with redirect following
  try {
    console.log('Test 4: Following redirects for /team-members/');
    const response = await axios({
      method: 'GET',
      url: 'https://api.dealmachine.com/public/v1/team-members/',
      headers: {
        'Authorization': `Bearer ${API_KEY}`,
        'Accept': 'application/json',
      },
      maxRedirects: 10, // Follow up to 10 redirects
      validateStatus: () => true,
    });
    console.log('Final Status:', response.status);
    console.log('Final URL:', response.request?.res?.responseUrl || 'unknown');
    if (response.data) {
      console.log('Data:', JSON.stringify(response.data, null, 2).substring(0, 500));
    }
  } catch (error) {
    console.log('Error:', error.message);
    if (error.response) {
      console.log('Response status:', error.response.status);
      console.log('Response data:', error.response.data);
    }
  }
}

testSimple().catch(console.error);
