#!/usr/bin/env python3
"""
DealMachine MCP Server
Model Context Protocol server for DealMachine API integration
"""

import os
import json
import asyncio
import requests
from typing import Any, Optional
from datetime import datetime

# Disable SSL warnings for development
import urllib3
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

# Configuration
API_KEY = os.getenv('DEALMACHINE_API_KEY', 'nqcymtWdwB16')
BASE_URL = os.getenv('DEALMACHINE_API_BASE_URL', 'https://api.dealmachine.com/public/v1')

class DealMachineClient:
    """DealMachine API Client"""

    def __init__(self, api_key: str = API_KEY, base_url: str = BASE_URL):
        self.api_key = api_key
        self.base_url = base_url
        self.headers = {
            'Authorization': f'Bearer {api_key}',
            'Content-Type': 'application/json'
        }

    def _request(self, method: str, endpoint: str, **kwargs) -> dict:
        """Make API request with error handling"""
        url = f"{self.base_url}{endpoint}"

        # Add verify=False to bypass SSL issues (for development)
        kwargs['verify'] = False
        kwargs['timeout'] = kwargs.get('timeout', 10)

        try:
            response = requests.request(
                method,
                url,
                headers=self.headers,
                **kwargs
            )

            if response.status_code == 200:
                return {
                    'success': True,
                    'data': response.json(),
                    'status_code': 200
                }
            elif response.status_code == 401:
                return {
                    'success': False,
                    'error': 'Invalid API key',
                    'status_code': 401
                }
            else:
                return {
                    'success': False,
                    'error': f'HTTP {response.status_code}: {response.text[:200]}',
                    'status_code': response.status_code
                }
        except Exception as e:
            return {
                'success': False,
                'error': str(e),
                'status_code': 0
            }

    # Team Members
    def get_team_members(self) -> dict:
        """Get all team members"""
        return self._request('GET', '/team-members/')

    # Leads
    def get_leads(self, page: int = 1, limit: int = 100) -> dict:
        """Get leads with pagination"""
        return self._request('GET', f'/leads/?page={page}&limit={limit}')

    def get_lead(self, lead_id: str) -> dict:
        """Get single lead by ID"""
        return self._request('GET', f'/leads/{lead_id}')

    def create_lead(self, address_data: dict) -> dict:
        """Create a new lead

        address_data format:
        {
            "addressType": 1,  # 1=full_address, 2=lat/long, 3=structured
            "full_address": "123 Main St, City, ST 12345"
            # OR
            # "latitude": "40.7128", "longitude": "-74.0060"
            # OR
            # "address": "123 Main St", "city": "City", "state": "ST", "zip": "12345"
        }
        """
        return self._request('POST', '/leads/', json=address_data)

    # Tags
    def get_tags(self) -> dict:
        """Get all available tags"""
        return self._request('GET', '/tags/')

    def add_tags_to_lead(self, lead_id: str, tag_ids: list) -> dict:
        """Add tags to a lead"""
        return self._request(
            'POST',
            f'/leads/{lead_id}/add-tags',
            json={'tag_ids': tag_ids}
        )

    def remove_tags_from_lead(self, lead_id: str, tag_ids: list) -> dict:
        """Remove tags from a lead"""
        return self._request(
            'POST',
            f'/leads/{lead_id}/remove-tags',
            json={'tag_ids': tag_ids}
        )

    # Notes
    def create_note(self, lead_id: str, note: str) -> dict:
        """Create a note for a lead"""
        return self._request(
            'POST',
            f'/leads/{lead_id}/create-note',
            json={'note': note}
        )

    # Mail Campaigns
    def start_mail_sequence(self, lead_id: str, sequence_config: dict) -> dict:
        """Start mail sequence for a lead"""
        return self._request(
            'POST',
            f'/leads/{lead_id}/start-mail-sequence',
            json=sequence_config
        )

    def pause_mail_sequence(self, lead_id: str) -> dict:
        """Pause mail sequence for a lead"""
        return self._request(
            'POST',
            f'/leads/{lead_id}/pause-mail-sequence'
        )

    def end_mail_sequence(self, lead_id: str) -> dict:
        """End mail sequence for a lead"""
        return self._request(
            'POST',
            f'/leads/{lead_id}/end-mail-sequence'
        )


class DealMachineMCP:
    """MCP Server for DealMachine"""

    def __init__(self):
        self.client = DealMachineClient()
        self.tools = self._register_tools()

    def _register_tools(self) -> dict:
        """Register available MCP tools"""
        return {
            'get_team_members': {
                'description': 'Get all team members from DealMachine',
                'parameters': {},
                'handler': self.client.get_team_members
            },
            'get_leads': {
                'description': 'Get leads with pagination',
                'parameters': {
                    'page': {'type': 'integer', 'default': 1},
                    'limit': {'type': 'integer', 'default': 100}
                },
                'handler': self.client.get_leads
            },
            'get_lead': {
                'description': 'Get a single lead by ID',
                'parameters': {
                    'lead_id': {'type': 'string', 'required': True}
                },
                'handler': self.client.get_lead
            },
            'create_lead': {
                'description': 'Create a new lead',
                'parameters': {
                    'address_data': {'type': 'object', 'required': True}
                },
                'handler': self.client.create_lead
            },
            'get_tags': {
                'description': 'Get all available tags',
                'parameters': {},
                'handler': self.client.get_tags
            },
            'add_tags_to_lead': {
                'description': 'Add tags to a lead',
                'parameters': {
                    'lead_id': {'type': 'string', 'required': True},
                    'tag_ids': {'type': 'array', 'required': True}
                },
                'handler': self.client.add_tags_to_lead
            },
            'create_note': {
                'description': 'Create a note for a lead',
                'parameters': {
                    'lead_id': {'type': 'string', 'required': True},
                    'note': {'type': 'string', 'required': True}
                },
                'handler': self.client.create_note
            },
            'start_mail_sequence': {
                'description': 'Start a mail campaign sequence for a lead',
                'parameters': {
                    'lead_id': {'type': 'string', 'required': True},
                    'sequence_config': {'type': 'object', 'required': True}
                },
                'handler': self.client.start_mail_sequence
            },
            'pause_mail_sequence': {
                'description': 'Pause mail sequence for a lead',
                'parameters': {
                    'lead_id': {'type': 'string', 'required': True}
                },
                'handler': self.client.pause_mail_sequence
            }
        }

    def call_tool(self, tool_name: str, **kwargs) -> dict:
        """Call a tool by name"""
        if tool_name not in self.tools:
            return {
                'success': False,
                'error': f'Unknown tool: {tool_name}'
            }

        try:
            handler = self.tools[tool_name]['handler']
            result = handler(**kwargs)
            return result
        except Exception as e:
            return {
                'success': False,
                'error': str(e)
            }

    def list_tools(self) -> list:
        """List all available tools"""
        return [
            {
                'name': name,
                'description': tool['description'],
                'parameters': tool['parameters']
            }
            for name, tool in self.tools.items()
        ]


# Global MCP instance
mcp_server = DealMachineMCP()


# Test functions
def test_mcp_server():
    """Test MCP server functionality"""
    print("=" * 60)
    print("DEALMACHINE MCP SERVER TEST")
    print("=" * 60)

    # List tools
    print("\n[1] Available Tools:")
    tools = mcp_server.list_tools()
    for tool in tools:
        print(f"  - {tool['name']}: {tool['description']}")

    # Test get_team_members
    print("\n[2] Testing: get_team_members")
    result = mcp_server.call_tool('get_team_members')
    if result['success']:
        data = result['data']
        if 'data' in data:
            members = data['data']
            print(f"  ✅ Found {len(members)} team members")
            if members:
                print(f"  First member: {members[0]['name']}")
    else:
        print(f"  ❌ Error: {result['error']}")

    # Test get_tags
    print("\n[3] Testing: get_tags")
    result = mcp_server.call_tool('get_tags')
    if result['success']:
        data = result['data']
        if 'data' in data:
            tags = data['data']
            print(f"  ✅ Found {len(tags)} tags")
            if tags:
                print(f"  Sample tags: {[t['label'] for t in tags[:5]]}")
    else:
        print(f"  ❌ Error: {result['error']}")

    # Test get_leads
    print("\n[4] Testing: get_leads")
    result = mcp_server.call_tool('get_leads', page=1, limit=5)
    if result['success']:
        data = result['data']
        print(f"  ✅ Successfully fetched leads")
        if 'data' in data and data['data']:
            leads = data['data']
            print(f"  Found {len(leads)} leads")
            if leads and isinstance(leads, list):
                print(f"  First lead has {len(leads[0].keys())} fields")
    else:
        print(f"  ❌ Error: {result['error']}")

    print("\n" + "=" * 60)
    print("MCP SERVER TEST COMPLETE")
    print("=" * 60)


if __name__ == '__main__':
    test_mcp_server()
