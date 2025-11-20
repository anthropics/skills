#!/usr/bin/env python3
"""
Detailed Lead Data Explorer
Shows the actual structure and data from your DealMachine leads
"""

import json
from mcp_server import mcp_server

def explore_lead_data():
    """Explore the structure of lead data"""
    print("=" * 70)
    print("  EXPLORING YOUR DEALMACHINE LEAD DATA")
    print("=" * 70)

    result = mcp_server.call_tool('get_leads', page=1, limit=3)

    if result['success']:
        data = result['data']

        if 'data' in data:
            leads = data['data']
            print(f"\n✅ Retrieved {len(leads)} leads\n")

            if leads:
                print("-" * 70)
                print("LEAD #1 - COMPLETE DATA STRUCTURE:")
                print("-" * 70)

                lead = leads[0]

                # Print all available fields
                print(json.dumps(lead, indent=2, default=str)[:5000])

                print("\n" + "-" * 70)
                print("KEY FIELDS EXTRACTED:")
                print("-" * 70)

                # Try to extract all possible address fields
                address_fields = [
                    'address', 'street_address', 'property_address',
                    'full_address', 'mailing_address', 'property_street',
                    'city', 'state', 'zip', 'zip_code', 'postal_code',
                    'county', 'latitude', 'longitude'
                ]

                print("\nAddress Information:")
                for field in address_fields:
                    if field in lead and lead[field]:
                        print(f"  {field}: {lead[field]}")

                # Owner information
                owner_fields = [
                    'owner_name', 'owner', 'owner_firstname', 'owner_lastname',
                    'owner_type', 'owner_mailing_address', 'owner_city',
                    'owner_state', 'owner_zip'
                ]

                print("\nOwner Information:")
                for field in owner_fields:
                    if field in lead and lead[field]:
                        print(f"  {field}: {lead[field]}")

                # Property details
                property_fields = [
                    'property_type', 'bedrooms', 'bathrooms', 'square_feet',
                    'year_built', 'lot_size', 'assessed_value', 'market_value',
                    'equity', 'mortgage_amount', 'tax_amount'
                ]

                print("\nProperty Details:")
                for field in property_fields:
                    if field in lead and lead[field]:
                        print(f"  {field}: {lead[field]}")

                # Status and tags
                status_fields = [
                    'status', 'lead_status', 'is_vacant', 'vacancy',
                    'tax_delinquent', 'absentee_owner', 'tags'
                ]

                print("\nStatus Information:")
                for field in status_fields:
                    if field in lead and lead[field]:
                        value = lead[field]
                        if isinstance(value, list):
                            print(f"  {field}: {len(value)} items")
                        else:
                            print(f"  {field}: {value}")

                # Show all top-level keys
                print("\n" + "-" * 70)
                print(f"ALL AVAILABLE FIELDS ({len(lead.keys())} total):")
                print("-" * 70)

                keys = sorted(lead.keys())
                for i in range(0, len(keys), 4):
                    row = keys[i:i+4]
                    print("  " + "  ".join(f"{k:25}" for k in row))

        else:
            print("No 'data' field in response")
            print(f"Response structure: {data.keys()}")

    else:
        print(f"❌ Error: {result['error']}")

    print("\n" + "=" * 70)

if __name__ == '__main__':
    explore_lead_data()
