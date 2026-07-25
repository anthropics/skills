#!/usr/bin/env python3
"""
CAC (Customer Acquisition Cost) Calculator

Calculate blended and channel-specific CAC for marketing campaigns.
Supports multiple time periods and channel breakdowns.
"""

import argparse
import sys
from typing import Dict, List

def calculate_cac(total_spend: float, customers_acquired: int) -> float:
    """Calculate basic CAC"""
    if customers_acquired == 0:
        return 0.0
    return round(total_spend / customers_acquired, 2)

def calculate_channel_cac(channel_data: List[Dict]) -> Dict:
    """
    Calculate CAC per channel
    
    Args:
        channel_data: List of dicts with 'channel', 'spend', 'customers' keys
        
    Returns:
        Dict with channel CAC breakdown and blended CAC
    """
    results = {}
    total_spend = 0
    total_customers = 0
    
    for channel in channel_data:
        name = channel['channel']
        spend = channel['spend']
        customers = channel['customers']
        
        cac = calculate_cac(spend, customers)
        results[name] = {
            'spend': spend,
            'customers': customers,
            'cac': cac
        }
        
        total_spend += spend
        total_customers += customers
    
    results['blended'] = {
        'total_spend': total_spend,
        'total_customers': total_customers,
        'blended_cac': calculate_cac(total_spend, total_customers)
    }
    
    return results

def print_results(results: Dict):
    """Pretty print CAC results"""
    print("\n" + "="*60)
    print("CAC CALCULATION RESULTS")
    print("="*60 + "\n")
    
    for channel, data in results.items():
        if channel == 'blended':
            print("-"*60)
            print(f"BLENDED CAC")
            print(f"  Total Spend: ${data['total_spend']:,.2f}")
            print(f"  Total Customers: {data['total_customers']:,}")
            print(f"  Blended CAC: ${data['blended_cac']:,.2f}")
        else:
            print(f"{channel.upper()}")
            print(f"  Spend: ${data['spend']:,.2f}")
            print(f"  Customers: {data['customers']:,}")
            print(f"  CAC: ${data['cac']:,.2f}")
            print()

def main():
    # TODO: accept channel data via --file <json> or stdin so the tool can be
    # automated without hand-editing this list (known limitation).
    # Example data - replace with your actual numbers
    example_data = [
        {'channel': 'LinkedIn Ads', 'spend': 15000, 'customers': 10},
        {'channel': 'Google Search', 'spend': 12000, 'customers': 20},
        {'channel': 'SEO/Organic', 'spend': 5000, 'customers': 15},
        {'channel': 'Partnerships', 'spend': 3000, 'customers': 5},
    ]
    
    print("Marketing CAC Calculator")
    print("Edit the script to input your actual channel data\n")
    
    results = calculate_channel_cac(example_data)
    print_results(results)
    
    # CAC benchmarks
    print("\n" + "="*60)
    print("B2B SAAS BENCHMARKS (Series A)")
    print("="*60)
    print("LinkedIn Ads:   $150-$400")
    print("Google Search:  $80-$250")
    print("SEO/Organic:    $50-$150")
    print("Partnerships:   $100-$300")
    print("Blended Target: <$300")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Calculate blended and channel-specific CAC.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="Current limitation: channel data is the `example_data` list in "
               "main() — edit it with your spend/customer numbers, then run with "
               "no args. CLI input (--file <json> / stdin) is a planned "
               "enhancement; until then this tool is not scriptable.")
    parser.parse_args()
    main()
