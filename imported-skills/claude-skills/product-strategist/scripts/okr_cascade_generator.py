#!/usr/bin/env python3
"""
OKR Cascade Generator
Creates aligned OKRs from company strategy down to team level.

Features:
- Generates company → product → team OKR cascade
- Configurable team structure and contribution percentages
- Alignment scoring across vertical and horizontal dimensions
- Multiple output formats (dashboard, JSON)

Usage:
    python okr_cascade_generator.py growth
    python okr_cascade_generator.py retention --teams "Engineering,Design,Data"
    python okr_cascade_generator.py revenue --contribution 0.4 --json
"""

import json
import argparse
from typing import Dict, List
from datetime import datetime


class OKRGenerator:
    """Generate and cascade OKRs across the organization"""

    def __init__(self, teams: List[str] = None, product_contribution: float = 0.3):
        """
        Initialize OKR generator.

        Args:
            teams: List of team names (default: Growth, Platform, Mobile, Data)
            product_contribution: Fraction of company KRs that product owns (default: 0.3)
        """
        self.teams = teams or ['Growth', 'Platform', 'Mobile', 'Data']
        self.product_contribution = product_contribution

        self.okr_templates = {
            'growth': {
                'objectives': [
                    'Accelerate user acquisition and market expansion',
                    'Achieve product-market fit in new segments',
                    'Build sustainable growth engine'
                ],
                'key_results': [
                    'Increase MAU from {current} to {target}',
                    'Achieve {target}% MoM growth rate',
                    'Expand to {target} new markets',
                    'Reduce CAC by {target}%',
                    'Improve activation rate to {target}%'
                ]
            },
            'retention': {
                'objectives': [
                    'Create lasting customer value and loyalty',
                    'Deliver a superior user experience',
                    'Maximize customer lifetime value'
                ],
                'key_results': [
                    'Improve retention from {current}% to {target}%',
                    'Increase NPS from {current} to {target}',
                    'Reduce churn to below {target}%',
                    'Achieve {target}% product stickiness',
                    'Increase LTV/CAC ratio to {target}'
                ]
            },
            'revenue': {
                'objectives': [
                    'Drive sustainable revenue growth',
                    'Optimize monetization strategy',
                    'Expand revenue per customer'
                ],
                'key_results': [
                    'Grow ARR from ${current}M to ${target}M',
                    'Increase ARPU by {target}%',
                    'Launch {target} new revenue streams',
                    'Achieve {target}% gross margin',
                    'Reduce revenue churn to {target}%'
                ]
            },
            'innovation': {
                'objectives': [
                    'Lead the market through product innovation',
                    'Establish leadership in key capability areas',
                    'Build sustainable competitive differentiation'
                ],
                'key_results': [
                    'Launch {target} breakthrough features',
                    'Achieve {target}% of revenue from new products',
                    'File {target} patents/IP',
                    'Reduce time-to-market by {target}%',
                    'Achieve {target} innovation score'
                ]
            },
            'operational': {
                'objectives': [
                    'Improve organizational efficiency',
                    'Achieve operational excellence',
                    'Scale operations sustainably'
                ],
                'key_results': [
                    'Improve velocity by {target}%',
                    'Reduce cycle time to {target} days',
                    'Achieve {target}% automation',
                    'Improve team satisfaction to {target}',
                    'Reduce incidents by {target}%'
                ]
            }
        }

        # Team focus areas for objective relevance matching
        self.team_relevance = {
            'Growth': ['acquisition', 'growth', 'activation', 'viral', 'onboarding', 'conversion'],
            'Platform': ['infrastructure', 'reliability', 'scale', 'performance', 'efficiency', 'automation'],
            'Mobile': ['mobile', 'app', 'ios', 'android', 'native'],
            'Data': ['analytics', 'metrics', 'insights', 'data', 'measurement', 'experimentation'],
            'Engineering': ['delivery', 'velocity', 'quality', 'automation', 'infrastructure'],
            'Design': ['experience', 'usability', 'interface', 'user', 'accessibility'],
            'Product': ['features', 'roadmap', 'prioritization', 'strategy'],
        }

    def generate_company_okrs(self, strategy: str, metrics: Dict) -> Dict:
        """Generate company-level OKRs based on strategy"""

        if strategy not in self.okr_templates:
            strategy = 'growth'

        template = self.okr_templates[strategy]

        company_okrs = {
            'level': 'Company',
            'quarter': self._get_current_quarter(),
            'strategy': strategy,
            'objectives': []
        }

        for i in range(min(3, len(template['objectives']))):
            obj = {
                'id': f'CO-{i+1}',
                'title': template['objectives'][i],
                'key_results': [],
                'owner': 'CEO',
                'status': 'draft'
            }

            for j in range(3):
                if j < len(template['key_results']):
                    kr_template = template['key_results'][j]
                    kr = {
                        'id': f'CO-{i+1}-KR{j+1}',
                        'title': self._fill_metrics(kr_template, metrics),
                        'current': metrics.get('current', 0),
                        'target': metrics.get('target', 100),
                        'unit': self._extract_unit(kr_template),
                        'status': 'not_started'
                    }
                    obj['key_results'].append(kr)

            company_okrs['objectives'].append(obj)

        return company_okrs

    def cascade_to_product(self, company_okrs: Dict) -> Dict:
        """Cascade company OKRs to product organization"""

        product_okrs = {
            'level': 'Product',
            'quarter': company_okrs['quarter'],
            'parent': 'Company',
            'contribution': self.product_contribution,
            'objectives': []
        }

        for company_obj in company_okrs['objectives']:
            product_obj = {
                'id': f'PO-{company_obj["id"].split("-")[1]}',
                'title': self._translate_to_product(company_obj['title']),
                'parent_objective': company_obj['id'],
                'key_results': [],
                'owner': 'Head of Product',
                'status': 'draft'
            }

            for kr in company_obj['key_results']:
                product_kr = {
                    'id': f'PO-{product_obj["id"].split("-")[1]}-KR{kr["id"].split("KR")[1]}',
                    'title': self._translate_kr_to_product(kr['title']),
                    'contributes_to': kr['id'],
                    'current': kr['current'],
                    'target': kr['target'] * self.product_contribution,
                    'unit': kr['unit'],
                    'contribution_pct': self.product_contribution * 100,
                    'status': 'not_started'
                }
                product_obj['key_results'].append(product_kr)

            product_okrs['objectives'].append(product_obj)

        return product_okrs

    def cascade_to_teams(self, product_okrs: Dict) -> List[Dict]:
        """Cascade product OKRs to individual teams"""

        team_okrs = []
        team_contribution = 1.0 / len(self.teams) if self.teams else 0.25

        for team in self.teams:
            team_okr = {
                'level': 'Team',
                'team': team,
                'quarter': product_okrs['quarter'],
                'parent': 'Product',
                'contribution': team_contribution,
                'objectives': []
            }

            for product_obj in product_okrs['objectives']:
                if self._is_relevant_for_team(product_obj['title'], team):
                    team_obj = {
                        'id': f'{team[:3].upper()}-{product_obj["id"].split("-")[1]}',
                        'title': self._translate_to_team(product_obj['title'], team),
                        'parent_objective': product_obj['id'],
                        'key_results': [],
                        'owner': f'{team} PM',
                        'status': 'draft'
                    }

                    for kr in product_obj['key_results'][:2]:
                        team_kr = {
                            'id': f'{team[:3].upper()}-{team_obj["id"].split("-")[1]}-KR{kr["id"].split("KR")[1]}',
                            'title': self._translate_kr_to_team(kr['title'], team),
                            'contributes_to': kr['id'],
                            'current': kr['current'],
                            'target': kr['target'] * team_contribution,
                            'unit': kr['unit'],
                            'status': 'not_started'
                        }
                        team_obj['key_results'].append(team_kr)

                    team_okr['objectives'].append(team_obj)

            if team_okr['objectives']:
                team_okrs.append(team_okr)

        return team_okrs

    def generate_okr_dashboard(self, all_okrs: Dict) -> str:
        """Generate OKR dashboard view"""

        dashboard = ["=" * 60]
        dashboard.append("OKR CASCADE DASHBOARD")
        dashboard.append(f"Quarter: {all_okrs.get('quarter', 'Q1 2025')}")
        dashboard.append(f"Strategy: {all_okrs.get('strategy', 'growth').upper()}")
        dashboard.append(f"Teams: {', '.join(self.teams)}")
        dashboard.append(f"Product Contribution: {self.product_contribution * 100:.0f}%")
        dashboard.append("=" * 60)

        # Company OKRs
        if 'company' in all_okrs:
            dashboard.append("\n🏢 COMPANY OKRS\n")
            for obj in all_okrs['company']['objectives']:
                dashboard.append(f"📌 {obj['id']}: {obj['title']}")
                for kr in obj['key_results']:
                    dashboard.append(f"   └─ {kr['id']}: {kr['title']}")

        # Product OKRs
        if 'product' in all_okrs:
            dashboard.append("\n🚀 PRODUCT OKRS\n")
            for obj in all_okrs['product']['objectives']:
                dashboard.append(f"📌 {obj['id']}: {obj['title']}")
                dashboard.append(f"   ↳ Supports: {obj.get('parent_objective', 'N/A')}")
                for kr in obj['key_results']:
                    dashboard.append(f"   └─ {kr['id']}: {kr['title']}")

        # Team OKRs
        if 'teams' in all_okrs:
            dashboard.append("\n👥 TEAM OKRS\n")
            for team_okr in all_okrs['teams']:
                dashboard.append(f"\n{team_okr['team']} Team:")
                for obj in team_okr['objectives']:
                    dashboard.append(f"  📌 {obj['id']}: {obj['title']}")
                    for kr in obj['key_results']:
                        dashboard.append(f"     └─ {kr['id']}: {kr['title']}")

        # Alignment Matrix
        dashboard.append("\n\n📊 ALIGNMENT MATRIX\n")
        dashboard.append("Company → Product → Teams")
        dashboard.append("-" * 40)

        if 'company' in all_okrs and 'product' in all_okrs:
            for c_obj in all_okrs['company']['objectives']:
                dashboard.append(f"\n{c_obj['id']}")
                for p_obj in all_okrs['product']['objectives']:
                    if p_obj.get('parent_objective') == c_obj['id']:
                        dashboard.append(f"  ├─ {p_obj['id']}")
                        if 'teams' in all_okrs:
                            for team_okr in all_okrs['teams']:
                                for t_obj in team_okr['objectives']:
                                    if t_obj.get('parent_objective') == p_obj['id']:
                                        dashboard.append(f"    └─ {t_obj['id']} ({team_okr['team']})")

        return "\n".join(dashboard)

    def calculate_alignment_score(self, all_okrs: Dict) -> Dict:
        """Calculate alignment score across OKR cascade"""

        scores = {
            'vertical_alignment': 0,
            'horizontal_alignment': 0,
            'coverage': 0,
            'balance': 0,
            'overall': 0
        }

        # Vertical alignment: How well each level supports the above
        total_objectives = 0
        aligned_objectives = 0

        if 'product' in all_okrs:
            for obj in all_okrs['product']['objectives']:
                total_objectives += 1
                if 'parent_objective' in obj:
                    aligned_objectives += 1

        if 'teams' in all_okrs:
            for team in all_okrs['teams']:
                for obj in team['objectives']:
                    total_objectives += 1
                    if 'parent_objective' in obj:
                        aligned_objectives += 1

        if total_objectives > 0:
            scores['vertical_alignment'] = round((aligned_objectives / total_objectives) * 100, 1)

        # Horizontal alignment: How well teams coordinate
        if 'teams' in all_okrs and len(all_okrs['teams']) > 1:
            shared_objectives = set()
            for team in all_okrs['teams']:
                for obj in team['objectives']:
                    parent = obj.get('parent_objective')
                    if parent:
                        shared_objectives.add(parent)

            scores['horizontal_alignment'] = min(100, len(shared_objectives) * 25)

        # Coverage: How much of company OKRs are covered
        if 'company' in all_okrs and 'product' in all_okrs:
            company_krs = sum(len(obj['key_results']) for obj in all_okrs['company']['objectives'])
            covered_krs = sum(len(obj['key_results']) for obj in all_okrs['product']['objectives'])
            if company_krs > 0:
                scores['coverage'] = round((covered_krs / company_krs) * 100, 1)

        # Balance: Distribution across teams
        if 'teams' in all_okrs:
            objectives_per_team = [len(team['objectives']) for team in all_okrs['teams']]
            if objectives_per_team:
                avg_objectives = sum(objectives_per_team) / len(objectives_per_team)
                variance = sum((x - avg_objectives) ** 2 for x in objectives_per_team) / len(objectives_per_team)
                scores['balance'] = round(max(0, 100 - variance * 10), 1)

        # Overall score
        scores['overall'] = round(sum([
            scores['vertical_alignment'] * 0.4,
            scores['horizontal_alignment'] * 0.2,
            scores['coverage'] * 0.2,
            scores['balance'] * 0.2
        ]), 1)

        return scores

    def _get_current_quarter(self) -> str:
        """Get current quarter"""
        now = datetime.now()
        quarter = (now.month - 1) // 3 + 1
        return f"Q{quarter} {now.year}"

    def _fill_metrics(self, template: str, metrics: Dict) -> str:
        """Fill template with actual metrics"""
        result = template
        for key, value in metrics.items():
            result = result.replace(f'{{{key}}}', str(value))
        return result

    def _extract_unit(self, kr_template: str) -> str:
        """Extract measurement unit from KR template"""
        if '%' in kr_template:
            return '%'
        elif '$' in kr_template:
            return '$'
        elif 'days' in kr_template.lower():
            return 'days'
        elif 'score' in kr_template.lower():
            return 'points'
        return 'count'

    def _translate_to_product(self, company_objective: str) -> str:
        """Translate company objective to product objective"""
        translations = {
            'Accelerate user acquisition': 'Build viral product features',
            'Achieve product-market fit': 'Validate product hypotheses',
            'Build sustainable growth': 'Create product-led growth loops',
            'Create lasting customer value': 'Design sticky user experiences',
            'Drive sustainable revenue': 'Optimize product monetization',
            'Lead the market through': 'Ship innovative features to',
            'Improve organizational': 'Improve product delivery'
        }

        for key, value in translations.items():
            if key in company_objective:
                return company_objective.replace(key, value)
        return f"Product: {company_objective}"

    def _translate_kr_to_product(self, kr: str) -> str:
        """Translate KR to product context"""
        product_terms = {
            'MAU': 'product MAU',
            'growth rate': 'feature adoption rate',
            'CAC': 'product onboarding efficiency',
            'retention': 'product retention',
            'NPS': 'product NPS',
            'ARR': 'product-driven revenue',
            'churn': 'product churn'
        }

        result = kr
        for term, replacement in product_terms.items():
            if term in result:
                result = result.replace(term, replacement)
                break
        return result

    def _translate_to_team(self, objective: str, team: str) -> str:
        """Translate objective to team context"""
        team_focus = {
            'Growth': 'acquisition and activation',
            'Platform': 'infrastructure and reliability',
            'Mobile': 'mobile experience',
            'Data': 'analytics and insights',
            'Engineering': 'technical delivery',
            'Design': 'user experience',
            'Product': 'product strategy'
        }

        focus = team_focus.get(team, 'delivery')
        return f"{objective} through {focus}"

    def _translate_kr_to_team(self, kr: str, team: str) -> str:
        """Translate KR to team context"""
        return f"[{team}] {kr}"

    def _is_relevant_for_team(self, objective: str, team: str) -> bool:
        """Check if objective is relevant for team"""
        keywords = self.team_relevance.get(team, [])
        objective_lower = objective.lower()

        # Platform is always relevant (infrastructure supports everything)
        if team == 'Platform':
            return True

        return any(keyword in objective_lower for keyword in keywords)


def parse_teams(teams_str: str) -> List[str]:
    """Parse comma-separated team string into list"""
    if not teams_str:
        return None
    return [t.strip() for t in teams_str.split(',') if t.strip()]


def main():
    parser = argparse.ArgumentParser(
        description='Generate OKR cascade from company strategy to team level',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Generate growth strategy OKRs with default teams
  python okr_cascade_generator.py growth

  # Custom teams
  python okr_cascade_generator.py retention --teams "Engineering,Design,Data,Growth"

  # Custom product contribution percentage
  python okr_cascade_generator.py revenue --contribution 0.4

  # JSON output
  python okr_cascade_generator.py innovation --json

  # All options combined
  python okr_cascade_generator.py operational --teams "Core,Platform" --contribution 0.5 --json
        """
    )

    parser.add_argument(
        'strategy',
        nargs='?',
        choices=['growth', 'retention', 'revenue', 'innovation', 'operational'],
        default='growth',
        help='Strategy type (default: growth)'
    )

    parser.add_argument(
        '--teams', '-t',
        type=str,
        help='Comma-separated list of team names (default: Growth,Platform,Mobile,Data)'
    )

    parser.add_argument(
        '--contribution', '-c',
        type=float,
        default=0.3,
        help='Product contribution to company OKRs as decimal (default: 0.3 = 30%%)'
    )

    parser.add_argument(
        '--json', '-j',
        action='store_true',
        help='Output as JSON instead of dashboard'
    )

    parser.add_argument(
        '--metrics', '-m',
        type=str,
        help='Metrics as JSON string (default: sample metrics)'
    )

    args = parser.parse_args()

    # Parse teams
    teams = parse_teams(args.teams)

    # Parse metrics
    if args.metrics:
        metrics = json.loads(args.metrics)
    else:
        metrics = {
            'current': 100000,
            'target': 150000,
            'current_revenue': 10,
            'target_revenue': 15,
            'current_nps': 40,
            'target_nps': 60
        }

    # Validate contribution
    if not 0 < args.contribution <= 1:
        print("Error: Contribution must be between 0 and 1")
        return 1

    # Generate OKRs
    generator = OKRGenerator(teams=teams, product_contribution=args.contribution)

    company_okrs = generator.generate_company_okrs(args.strategy, metrics)
    product_okrs = generator.cascade_to_product(company_okrs)
    team_okrs = generator.cascade_to_teams(product_okrs)

    all_okrs = {
        'quarter': company_okrs['quarter'],
        'strategy': args.strategy,
        'company': company_okrs,
        'product': product_okrs,
        'teams': team_okrs
    }

    alignment = generator.calculate_alignment_score(all_okrs)

    if args.json:
        all_okrs['alignment_scores'] = alignment
        all_okrs['config'] = {
            'teams': generator.teams,
            'product_contribution': generator.product_contribution
        }
        print(json.dumps(all_okrs, indent=2))
    else:
        dashboard = generator.generate_okr_dashboard(all_okrs)
        print(dashboard)

        print("\n\n🎯 ALIGNMENT SCORES")
        print("-" * 40)
        for metric, score in alignment.items():
            status = "✓" if score >= 80 else "!" if score >= 60 else "✗"
            print(f"{status} {metric.replace('_', ' ').title()}: {score}%")

        if alignment['overall'] >= 80:
            print("\n✅ Overall alignment is GOOD (≥80%)")
        elif alignment['overall'] >= 60:
            print("\n⚠️  Overall alignment NEEDS ATTENTION (60-80%)")
        else:
            print("\n❌ Overall alignment is POOR (<60%)")


if __name__ == "__main__":
    main()
