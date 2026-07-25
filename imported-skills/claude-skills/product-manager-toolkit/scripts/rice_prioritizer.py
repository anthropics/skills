#!/usr/bin/env python3
"""
RICE Prioritization Framework
Calculates RICE scores for feature prioritization
RICE = (Reach x Impact x Confidence) / Effort
"""

import json
import csv
from typing import List, Dict, Tuple
import argparse

class RICECalculator:
    """Calculate RICE scores for feature prioritization"""
    
    def __init__(self):
        self.impact_map = {
            'massive': 3.0,
            'high': 2.0,
            'medium': 1.0,
            'low': 0.5,
            'minimal': 0.25
        }
        
        self.confidence_map = {
            'high': 100,
            'medium': 80,
            'low': 50
        }
        
        self.effort_map = {
            'xl': 13,
            'l': 8,
            'm': 5,
            's': 3,
            'xs': 1
        }
    
    def calculate_rice(self, reach: int, impact: str, confidence: str, effort: str) -> float:
        """
        Calculate RICE score
        
        Args:
            reach: Number of users/customers affected per quarter
            impact: massive/high/medium/low/minimal
            confidence: high/medium/low (percentage)
            effort: xl/l/m/s/xs (person-months)
        """
        impact_score = self.impact_map.get(impact.lower(), 1.0)
        confidence_score = self.confidence_map.get(confidence.lower(), 50) / 100
        effort_score = self.effort_map.get(effort.lower(), 5)
        
        if effort_score == 0:
            return 0
        
        rice_score = (reach * impact_score * confidence_score) / effort_score
        return round(rice_score, 2)
    
    def prioritize_features(self, features: List[Dict]) -> List[Dict]:
        """
        Calculate RICE scores and rank features
        
        Args:
            features: List of feature dictionaries with RICE components
        """
        for feature in features:
            feature['rice_score'] = self.calculate_rice(
                feature.get('reach', 0),
                feature.get('impact', 'medium'),
                feature.get('confidence', 'medium'),
                feature.get('effort', 'm')
            )
        
        # Sort by RICE score descending
        return sorted(features, key=lambda x: x['rice_score'], reverse=True)
    
    def analyze_portfolio(self, features: List[Dict]) -> Dict:
        """
        Analyze the feature portfolio for balance and insights
        """
        if not features:
            return {}
        
        total_effort = sum(
            self.effort_map.get(f.get('effort', 'm').lower(), 5) 
            for f in features
        )
        
        total_reach = sum(f.get('reach', 0) for f in features)
        
        effort_distribution = {}
        impact_distribution = {}
        
        for feature in features:
            effort = feature.get('effort', 'm').lower()
            impact = feature.get('impact', 'medium').lower()
            
            effort_distribution[effort] = effort_distribution.get(effort, 0) + 1
            impact_distribution[impact] = impact_distribution.get(impact, 0) + 1
        
        # Calculate quick wins (high impact, low effort)
        quick_wins = [
            f for f in features 
            if f.get('impact', '').lower() in ['massive', 'high'] 
            and f.get('effort', '').lower() in ['xs', 's']
        ]
        
        # Calculate big bets (high impact, high effort)
        big_bets = [
            f for f in features 
            if f.get('impact', '').lower() in ['massive', 'high'] 
            and f.get('effort', '').lower() in ['l', 'xl']
        ]
        
        return {
            'total_features': len(features),
            'total_effort_months': total_effort,
            'total_reach': total_reach,
            'average_rice': round(sum(f['rice_score'] for f in features) / len(features), 2),
            'effort_distribution': effort_distribution,
            'impact_distribution': impact_distribution,
            'quick_wins': len(quick_wins),
            'big_bets': len(big_bets),
            'quick_wins_list': quick_wins[:3],  # Top 3 quick wins
            'big_bets_list': big_bets[:3]  # Top 3 big bets
        }
    
    def generate_roadmap(self, features: List[Dict], team_capacity: int = 10) -> List[Dict]:
        """
        Generate a quarterly roadmap based on team capacity
        
        Args:
            features: Prioritized feature list
            team_capacity: Person-months available per quarter
        """
        quarters = []
        current_quarter = {
            'quarter': 1,
            'features': [],
            'capacity_used': 0,
            'capacity_available': team_capacity
        }
        
        for feature in features:
            effort = self.effort_map.get(feature.get('effort', 'm').lower(), 5)
            
            if current_quarter['capacity_used'] + effort <= team_capacity:
                current_quarter['features'].append(feature)
                current_quarter['capacity_used'] += effort
            else:
                # Move to next quarter
                current_quarter['capacity_available'] = team_capacity - current_quarter['capacity_used']
                quarters.append(current_quarter)
                
                current_quarter = {
                    'quarter': len(quarters) + 1,
                    'features': [feature],
                    'capacity_used': effort,
                    'capacity_available': team_capacity - effort
                }
        
        if current_quarter['features']:
            current_quarter['capacity_available'] = team_capacity - current_quarter['capacity_used']
            quarters.append(current_quarter)
        
        return quarters

def format_output(features: List[Dict], analysis: Dict, roadmap: List[Dict]) -> str:
    """Format the results for display"""
    output = ["=" * 60]
    output.append("RICE PRIORITIZATION RESULTS")
    output.append("=" * 60)
    
    # Top prioritized features
    output.append("\n📊 TOP PRIORITIZED FEATURES\n")
    for i, feature in enumerate(features[:10], 1):
        output.append(f"{i}. {feature.get('name', 'Unnamed')}")
        output.append(f"   RICE Score: {feature['rice_score']}")
        output.append(f"   Reach: {feature.get('reach', 0)} | Impact: {feature.get('impact', 'medium')} | "
                     f"Confidence: {feature.get('confidence', 'medium')} | Effort: {feature.get('effort', 'm')}")
        output.append("")
    
    # Portfolio analysis
    output.append("\n📈 PORTFOLIO ANALYSIS\n")
    output.append(f"Total Features: {analysis.get('total_features', 0)}")
    output.append(f"Total Effort: {analysis.get('total_effort_months', 0)} person-months")
    output.append(f"Total Reach: {analysis.get('total_reach', 0):,} users")
    output.append(f"Average RICE Score: {analysis.get('average_rice', 0)}")
    
    output.append(f"\n🎯 Quick Wins: {analysis.get('quick_wins', 0)} features")
    for qw in analysis.get('quick_wins_list', []):
        output.append(f"   • {qw.get('name', 'Unnamed')} (RICE: {qw['rice_score']})")
    
    output.append(f"\n🚀 Big Bets: {analysis.get('big_bets', 0)} features")
    for bb in analysis.get('big_bets_list', []):
        output.append(f"   • {bb.get('name', 'Unnamed')} (RICE: {bb['rice_score']})")
    
    # Roadmap
    output.append("\n\n📅 SUGGESTED ROADMAP\n")
    for quarter in roadmap:
        output.append(f"\nQ{quarter['quarter']} - Capacity: {quarter['capacity_used']}/{quarter['capacity_used'] + quarter['capacity_available']} person-months")
        for feature in quarter['features']:
            output.append(f"   • {feature.get('name', 'Unnamed')} (RICE: {feature['rice_score']})")
    
    return "\n".join(output)

def load_features_from_csv(filepath: str) -> List[Dict]:
    """Load features from CSV file"""
    features = []
    with open(filepath, 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            feature = {
                'name': row.get('name', ''),
                'reach': int(row.get('reach', 0)),
                'impact': row.get('impact', 'medium'),
                'confidence': row.get('confidence', 'medium'),
                'effort': row.get('effort', 'm'),
                'description': row.get('description', '')
            }
            features.append(feature)
    return features

def create_sample_csv(filepath: str):
    """Create a sample CSV file for testing"""
    sample_features = [
        ['name', 'reach', 'impact', 'confidence', 'effort', 'description'],
        ['User Dashboard Redesign', '5000', 'high', 'high', 'l', 'Complete redesign of user dashboard'],
        ['Mobile Push Notifications', '10000', 'massive', 'medium', 'm', 'Add push notification support'],
        ['Dark Mode', '8000', 'medium', 'high', 's', 'Implement dark mode theme'],
        ['API Rate Limiting', '2000', 'low', 'high', 'xs', 'Add rate limiting to API'],
        ['Social Login', '12000', 'high', 'medium', 'm', 'Add Google/Facebook login'],
        ['Export to PDF', '3000', 'medium', 'low', 's', 'Export reports as PDF'],
        ['Team Collaboration', '4000', 'massive', 'low', 'xl', 'Real-time collaboration features'],
        ['Search Improvements', '15000', 'high', 'high', 'm', 'Enhance search functionality'],
        ['Onboarding Flow', '20000', 'massive', 'high', 's', 'Improve new user onboarding'],
        ['Analytics Dashboard', '6000', 'high', 'medium', 'l', 'Advanced analytics for users'],
    ]
    
    with open(filepath, 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerows(sample_features)
    
    print(f"Sample CSV created at: {filepath}")

def main():
    parser = argparse.ArgumentParser(description='RICE Framework for Feature Prioritization')
    parser.add_argument('input', nargs='?', help='CSV file with features or "sample" to create sample')
    parser.add_argument('--capacity', type=int, default=10, help='Team capacity per quarter (person-months)')
    parser.add_argument('--output', choices=['text', 'json', 'csv'], default='text', help='Output format')
    
    args = parser.parse_args()
    
    # Create sample if requested
    if args.input == 'sample':
        create_sample_csv('sample_features.csv')
        return
    
    # Use sample data if no input provided
    if not args.input:
        features = [
            {'name': 'User Dashboard', 'reach': 5000, 'impact': 'high', 'confidence': 'high', 'effort': 'l'},
            {'name': 'Push Notifications', 'reach': 10000, 'impact': 'massive', 'confidence': 'medium', 'effort': 'm'},
            {'name': 'Dark Mode', 'reach': 8000, 'impact': 'medium', 'confidence': 'high', 'effort': 's'},
            {'name': 'API Rate Limiting', 'reach': 2000, 'impact': 'low', 'confidence': 'high', 'effort': 'xs'},
            {'name': 'Social Login', 'reach': 12000, 'impact': 'high', 'confidence': 'medium', 'effort': 'm'},
        ]
    else:
        features = load_features_from_csv(args.input)
    
    # Calculate RICE scores
    calculator = RICECalculator()
    prioritized = calculator.prioritize_features(features)
    analysis = calculator.analyze_portfolio(prioritized)
    roadmap = calculator.generate_roadmap(prioritized, args.capacity)
    
    # Output results
    if args.output == 'json':
        result = {
            'features': prioritized,
            'analysis': analysis,
            'roadmap': roadmap
        }
        print(json.dumps(result, indent=2))
    elif args.output == 'csv':
        # Output prioritized features as CSV
        if prioritized:
            keys = prioritized[0].keys()
            print(','.join(keys))
            for feature in prioritized:
                print(','.join(str(feature.get(k, '')) for k in keys))
    else:
        print(format_output(prioritized, analysis, roadmap))

if __name__ == "__main__":
    main()
