#!/usr/bin/env python3
"""
DealMachine API Test Script
Tests connection and basic functionality with the DealMachine API
"""

import os
import sys
import json
import requests
from datetime import datetime

# Load environment variables
API_KEY = os.getenv('DEALMACHINE_API_KEY', 'nqcymtWdwB16')
BASE_URL = os.getenv('DEALMACHINE_API_BASE_URL', 'https://api.dealmachine.com/public/v1')

def test_api_connection():
    """Test basic API connectivity"""
    print("=" * 60)
    print("DEALMACHINE API CONNECTION TEST")
    print("=" * 60)
    print(f"API Key: {API_KEY[:10]}..." if len(API_KEY) > 10 else API_KEY)
    print(f"Base URL: {BASE_URL}")
    print(f"Time: {datetime.now()}")
    print("=" * 60)

    headers = {
        'Authorization': f'Bearer {API_KEY}',
        'Content-Type': 'application/json'
    }

    # Test 1: Get Team Members (simplest endpoint)
    print("\n[TEST 1] Fetching Team Members...")
    try:
        response = requests.get(
            f'{BASE_URL}/team-members/',
            headers=headers,
            timeout=10
        )
        print(f"Status Code: {response.status_code}")

        if response.status_code == 200:
            data = response.json()
            print("✅ SUCCESS - Team Members Endpoint")
            print(f"Response: {json.dumps(data, indent=2)[:500]}...")
        elif response.status_code == 401:
            print("❌ FAILED - Invalid API Key (401 Unauthorized)")
            print(f"Response: {response.text}")
            return False
        else:
            print(f"⚠️  WARNING - Unexpected status code: {response.status_code}")
            print(f"Response: {response.text}")
    except Exception as e:
        print(f"❌ ERROR: {str(e)}")
        return False

    # Test 2: Get Leads
    print("\n[TEST 2] Fetching Leads...")
    try:
        response = requests.get(
            f'{BASE_URL}/leads/?page=1&limit=5',
            headers=headers,
            timeout=10
        )
        print(f"Status Code: {response.status_code}")

        if response.status_code == 200:
            data = response.json()
            print("✅ SUCCESS - Leads Endpoint")

            if isinstance(data, dict) and 'leads' in data:
                leads = data.get('leads', [])
                print(f"Found {len(leads)} leads")
                if leads:
                    print(f"First lead: {json.dumps(leads[0], indent=2)[:300]}...")
            else:
                print(f"Response: {json.dumps(data, indent=2)[:500]}...")
        else:
            print(f"⚠️  Status {response.status_code}: {response.text[:200]}")
    except Exception as e:
        print(f"❌ ERROR: {str(e)}")

    # Test 3: Get Tags
    print("\n[TEST 3] Fetching Tags...")
    try:
        response = requests.get(
            f'{BASE_URL}/tags/',
            headers=headers,
            timeout=10
        )
        print(f"Status Code: {response.status_code}")

        if response.status_code == 200:
            data = response.json()
            print("✅ SUCCESS - Tags Endpoint")

            if isinstance(data, dict) and 'tags' in data:
                tags = data.get('tags', [])
                print(f"Found {len(tags)} tags")
                if tags:
                    print(f"Sample tags: {json.dumps(tags[:3], indent=2)}")
            else:
                print(f"Response: {json.dumps(data, indent=2)[:500]}...")
        else:
            print(f"⚠️  Status {response.status_code}: {response.text[:200]}")
    except Exception as e:
        print(f"❌ ERROR: {str(e)}")

    print("\n" + "=" * 60)
    print("TEST COMPLETE")
    print("=" * 60)

    return True

if __name__ == '__main__':
    success = test_api_connection()
    sys.exit(0 if success else 1)
