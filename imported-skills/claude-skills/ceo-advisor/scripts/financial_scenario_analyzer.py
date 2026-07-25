#!/usr/bin/env python3
"""
Financial Scenario Analyzer - Model different business scenarios and their financial impact
"""

import json
from typing import Dict, List, Tuple
import math

class FinancialScenarioAnalyzer:
    def __init__(self):
        self.key_metrics = [
            'revenue', 'gross_margin', 'operating_expenses', 
            'ebitda', 'cash_flow', 'runway', 'valuation'
        ]
        
        self.growth_models = {
            'linear': lambda base, rate, period: base * (1 + rate * period),
            'exponential': lambda base, rate, period: base * math.pow(1 + rate, period),
            'logarithmic': lambda base, rate, period: base * (1 + rate * math.log(period + 1)),
            's_curve': lambda base, rate, period: base * (2 / (1 + math.exp(-rate * period)))
        }
    
    def analyze_scenarios(self, base_case: Dict, scenarios: List[Dict]) -> Dict:
        """Analyze multiple financial scenarios"""
        results = {
            'base_case_summary': self._summarize_financials(base_case),
            'scenario_analysis': [],
            'sensitivity_analysis': {},
            'recommendation': {},
            'risk_adjusted_view': {}
        }
        
        # Analyze each scenario
        for scenario in scenarios:
            scenario_result = self._analyze_scenario(base_case, scenario)
            results['scenario_analysis'].append(scenario_result)
        
        # Sensitivity analysis
        results['sensitivity_analysis'] = self._perform_sensitivity_analysis(
            base_case, 
            scenarios
        )
        
        # Risk-adjusted view
        results['risk_adjusted_view'] = self._calculate_risk_adjusted_returns(
            results['scenario_analysis']
        )
        
        # Generate recommendation
        results['recommendation'] = self._generate_recommendation(
            results['scenario_analysis'],
            results['risk_adjusted_view']
        )
        
        return results
    
    def _summarize_financials(self, financials: Dict) -> Dict:
        """Summarize key financial metrics"""
        revenue = financials.get('revenue', 0)
        cogs = financials.get('cogs', 0)
        opex = financials.get('operating_expenses', 0)
        
        gross_profit = revenue - cogs
        gross_margin = (gross_profit / revenue * 100) if revenue > 0 else 0
        ebitda = gross_profit - opex
        ebitda_margin = (ebitda / revenue * 100) if revenue > 0 else 0
        
        return {
            'revenue': revenue,
            'gross_profit': gross_profit,
            'gross_margin': gross_margin,
            'operating_expenses': opex,
            'ebitda': ebitda,
            'ebitda_margin': ebitda_margin,
            'cash': financials.get('cash', 0),
            'burn_rate': financials.get('burn_rate', 0),
            'runway_months': self._calculate_runway(
                financials.get('cash', 0),
                financials.get('burn_rate', 0)
            )
        }
    
    def _calculate_runway(self, cash: float, burn_rate: float) -> float:
        """Calculate months of runway"""
        if burn_rate <= 0:
            return float('inf')
        return cash / burn_rate
    
    def _analyze_scenario(self, base_case: Dict, scenario: Dict) -> Dict:
        """Analyze a single scenario"""
        name = scenario.get('name', 'Unnamed Scenario')
        probability = scenario.get('probability', 0.5)
        
        # Apply scenario changes
        projected_financials = self._apply_scenario_changes(base_case, scenario)
        
        # Calculate metrics for each year
        projections = []
        current_state = projected_financials.copy()
        
        for year in range(1, 4):  # 3-year projection
            year_projection = self._project_year(
                current_state,
                scenario,
                year
            )
            projections.append(year_projection)
            current_state = year_projection
        
        # Calculate NPV and IRR
        cash_flows = [p['free_cash_flow'] for p in projections]
        npv = self._calculate_npv(cash_flows, scenario.get('discount_rate', 0.1))
        irr = self._calculate_irr(cash_flows, base_case.get('initial_investment', 0))
        
        return {
            'name': name,
            'probability': probability,
            'projections': projections,
            'npv': npv,
            'irr': irr,
            'break_even_month': self._find_break_even(projections),
            'total_return': self._calculate_total_return(projections, base_case),
            'key_assumptions': scenario.get('assumptions', [])
        }
    
    def _apply_scenario_changes(self, base_case: Dict, scenario: Dict) -> Dict:
        """Apply scenario changes to base case"""
        result = base_case.copy()
        changes = scenario.get('changes', {})
        
        for key, change in changes.items():
            if key in result:
                if isinstance(change, dict):
                    # Relative change
                    if 'multiply' in change:
                        result[key] *= change['multiply']
                    elif 'add' in change:
                        result[key] += change['add']
                else:
                    # Absolute change
                    result[key] = change
        
        return result
    
    def _project_year(self, current_state: Dict, scenario: Dict, year: int) -> Dict:
        """Project financials for a specific year"""
        growth_model = scenario.get('growth_model', 'exponential')
        growth_rate = scenario.get('growth_rate', 0.3)
        
        # Apply growth model
        model_func = self.growth_models.get(growth_model, self.growth_models['linear'])
        
        revenue = model_func(
            current_state.get('revenue', 0),
            growth_rate,
            year
        )
        
        # Scale other metrics
        cogs = revenue * scenario.get('cogs_ratio', 0.3)
        opex = current_state.get('operating_expenses', 0) * (1 + scenario.get('opex_growth', 0.15))
        
        gross_profit = revenue - cogs
        ebitda = gross_profit - opex
        
        # Calculate free cash flow (simplified)
        capex = revenue * scenario.get('capex_ratio', 0.05)
        working_capital_change = (revenue - current_state.get('revenue', 0)) * 0.1
        free_cash_flow = ebitda - capex - working_capital_change
        
        return {
            'year': year,
            'revenue': revenue,
            'gross_profit': gross_profit,
            'gross_margin': (gross_profit / revenue * 100) if revenue > 0 else 0,
            'operating_expenses': opex,
            'ebitda': ebitda,
            'ebitda_margin': (ebitda / revenue * 100) if revenue > 0 else 0,
            'free_cash_flow': free_cash_flow,
            'cumulative_cash_flow': current_state.get('cumulative_cash_flow', 0) + free_cash_flow
        }
    
    def _calculate_npv(self, cash_flows: List[float], discount_rate: float) -> float:
        """Calculate Net Present Value"""
        npv = 0
        for i, cf in enumerate(cash_flows):
            npv += cf / math.pow(1 + discount_rate, i + 1)
        return npv
    
    def _calculate_irr(self, cash_flows: List[float], initial_investment: float) -> float:
        """Calculate Internal Rate of Return (simplified)"""
        if not cash_flows or initial_investment == 0:
            return 0
        
        # Simple IRR approximation
        total_return = sum(cash_flows)
        years = len(cash_flows)
        
        if initial_investment > 0:
            return math.pow(total_return / initial_investment, 1/years) - 1
        return 0
    
    def _find_break_even(self, projections: List[Dict]) -> int:
        """Find break-even month"""
        months = 0
        for projection in projections:
            months += 12
            if projection.get('ebitda', 0) > 0:
                # Interpolate to find exact month
                if months == 12:
                    return months
                prev_ebitda = projections[projection['year']-2].get('ebitda', 0) if projection['year'] > 1 else 0
                monthly_improvement = (projection['ebitda'] - prev_ebitda) / 12
                if monthly_improvement > 0:
                    months_to_breakeven = abs(prev_ebitda) / monthly_improvement
                    return int(months - 12 + months_to_breakeven)
        return -1  # Not reached
    
    def _calculate_total_return(self, projections: List[Dict], base_case: Dict) -> float:
        """Calculate total return multiple"""
        initial = base_case.get('valuation', 1000000)
        
        # Simple valuation at end (10x revenue multiple for SaaS)
        final_revenue = projections[-1]['revenue'] if projections else 0
        final_valuation = final_revenue * 10
        
        return (final_valuation / initial) if initial > 0 else 0
    
    def _perform_sensitivity_analysis(self, base_case: Dict, scenarios: List[Dict]) -> Dict:
        """Perform sensitivity analysis on key variables"""
        sensitivity = {}
        
        key_variables = ['growth_rate', 'gross_margin', 'customer_acquisition_cost']
        
        for variable in key_variables:
            sensitivity[variable] = {
                'low': self._calculate_variable_impact(base_case, variable, -0.2),
                'base': self._calculate_variable_impact(base_case, variable, 0),
                'high': self._calculate_variable_impact(base_case, variable, 0.2)
            }
        
        return sensitivity
    
    def _calculate_variable_impact(self, base_case: Dict, variable: str, change: float) -> float:
        """Calculate impact of variable change on valuation"""
        # Simplified impact calculation
        impacts = {
            'growth_rate': 2.5,  # 2.5x multiplier on valuation
            'gross_margin': 1.8,  # 1.8x multiplier
            'customer_acquisition_cost': -1.2  # Negative impact
        }
        
        base_value = 10000000  # Base valuation
        impact_multiplier = impacts.get(variable, 1.0)
        
        return base_value * (1 + change * impact_multiplier)
    
    def _calculate_risk_adjusted_returns(self, scenarios: List[Dict]) -> Dict:
        """Calculate risk-adjusted returns"""
        expected_value = 0
        best_case = None
        worst_case = None
        
        for scenario in scenarios:
            probability = scenario['probability']
            npv = scenario['npv']
            
            expected_value += probability * npv
            
            if best_case is None or npv > best_case['npv']:
                best_case = scenario
            
            if worst_case is None or npv < worst_case['npv']:
                worst_case = scenario
        
        # Calculate standard deviation (simplified)
        variance = sum([
            scenario['probability'] * math.pow(scenario['npv'] - expected_value, 2)
            for scenario in scenarios
        ])
        std_dev = math.sqrt(variance)
        
        return {
            'expected_value': expected_value,
            'best_case': best_case['name'] if best_case else 'None',
            'best_case_npv': best_case['npv'] if best_case else 0,
            'worst_case': worst_case['name'] if worst_case else 'None',
            'worst_case_npv': worst_case['npv'] if worst_case else 0,
            'standard_deviation': std_dev,
            'sharpe_ratio': (expected_value / std_dev) if std_dev > 0 else 0
        }
    
    def _generate_recommendation(self, scenarios: List[Dict], risk_adjusted: Dict) -> Dict:
        """Generate recommendation based on analysis"""
        recommendation = {
            'recommended_scenario': '',
            'rationale': [],
            'key_actions': [],
            'risk_mitigation': []
        }
        
        # Find optimal scenario
        best_risk_adjusted = max(scenarios, key=lambda s: s['npv'] * s['probability'])
        recommendation['recommended_scenario'] = best_risk_adjusted['name']
        
        # Generate rationale
        if best_risk_adjusted['npv'] > 0:
            recommendation['rationale'].append(f"Positive NPV of ${best_risk_adjusted['npv']:,.0f}")
        
        if best_risk_adjusted['irr'] > 0.15:
            recommendation['rationale'].append(f"Strong IRR of {best_risk_adjusted['irr']:.1%}")
        
        if best_risk_adjusted['break_even_month'] > 0 and best_risk_adjusted['break_even_month'] < 24:
            recommendation['rationale'].append(f"Quick path to profitability ({best_risk_adjusted['break_even_month']} months)")
        
        # Key actions
        recommendation['key_actions'] = [
            'Secure funding for growth initiatives',
            'Build scalable operational infrastructure',
            'Invest in customer acquisition channels',
            'Strengthen unit economics',
            'Establish financial controls'
        ]
        
        # Risk mitigation
        if risk_adjusted['standard_deviation'] > risk_adjusted['expected_value'] * 0.5:
            recommendation['risk_mitigation'].append('High variability - consider hedging strategies')
        
        recommendation['risk_mitigation'].extend([
            'Maintain 12+ months runway',
            'Diversify revenue streams',
            'Build contingency plans for downside scenarios'
        ])
        
        return recommendation

def analyze_financial_scenarios(base_case: Dict, scenarios: List[Dict]) -> str:
    """Main function to analyze financial scenarios"""
    analyzer = FinancialScenarioAnalyzer()
    results = analyzer.analyze_scenarios(base_case, scenarios)
    
    # Format output
    output = [
        "=== Financial Scenario Analysis ===",
        "",
        "Base Case Summary:",
        f"  Revenue: ${results['base_case_summary']['revenue']:,.0f}",
        f"  Gross Margin: {results['base_case_summary']['gross_margin']:.1f}%",
        f"  EBITDA: ${results['base_case_summary']['ebitda']:,.0f}",
        f"  Runway: {results['base_case_summary']['runway_months']:.1f} months",
        "",
        "Scenario Analysis:"
    ]
    
    for scenario in results['scenario_analysis']:
        output.append(f"\n{scenario['name']} (Probability: {scenario['probability']:.0%})")
        output.append(f"  NPV: ${scenario['npv']:,.0f}")
        output.append(f"  IRR: {scenario['irr']:.1%}")
        output.append(f"  Break-even: {scenario['break_even_month']} months")
        output.append(f"  Return Multiple: {scenario['total_return']:.1f}x")
        
        # Show Year 3 projection
        if scenario['projections']:
            year3 = scenario['projections'][-1]
            output.append(f"  Year 3 Revenue: ${year3['revenue']:,.0f}")
            output.append(f"  Year 3 EBITDA Margin: {year3['ebitda_margin']:.1f}%")
    
    output.extend([
        "",
        "Risk-Adjusted Analysis:",
        f"  Expected Value: ${results['risk_adjusted_view']['expected_value']:,.0f}",
        f"  Best Case: {results['risk_adjusted_view']['best_case']} (${results['risk_adjusted_view']['best_case_npv']:,.0f})",
        f"  Worst Case: {results['risk_adjusted_view']['worst_case']} (${results['risk_adjusted_view']['worst_case_npv']:,.0f})",
        f"  Risk (Std Dev): ${results['risk_adjusted_view']['standard_deviation']:,.0f}",
        f"  Sharpe Ratio: {results['risk_adjusted_view']['sharpe_ratio']:.2f}",
        "",
        f"RECOMMENDATION: {results['recommendation']['recommended_scenario']}",
        "",
        "Rationale:"
    ])
    
    for reason in results['recommendation']['rationale']:
        output.append(f"  • {reason}")
    
    output.extend([
        "",
        "Key Actions:"
    ])
    
    for action in results['recommendation']['key_actions'][:3]:
        output.append(f"  • {action}")
    
    return '\n'.join(output)

if __name__ == "__main__":
    # Example usage
    example_base_case = {
        'revenue': 5000000,
        'cogs': 1500000,
        'operating_expenses': 3000000,
        'cash': 2000000,
        'burn_rate': 200000,
        'valuation': 20000000,
        'initial_investment': 5000000
    }
    
    example_scenarios = [
        {
            'name': 'Aggressive Growth',
            'probability': 0.3,
            'growth_model': 'exponential',
            'growth_rate': 0.5,
            'changes': {
                'operating_expenses': {'multiply': 1.3}
            },
            'assumptions': ['Market expansion successful', 'Product-market fit achieved'],
            'cogs_ratio': 0.25,
            'opex_growth': 0.3,
            'capex_ratio': 0.08,
            'discount_rate': 0.12
        },
        {
            'name': 'Moderate Growth',
            'probability': 0.5,
            'growth_model': 'exponential',
            'growth_rate': 0.3,
            'changes': {},
            'assumptions': ['Steady market growth', 'Competition remains stable'],
            'cogs_ratio': 0.3,
            'opex_growth': 0.15,
            'capex_ratio': 0.05,
            'discount_rate': 0.10
        },
        {
            'name': 'Conservative',
            'probability': 0.2,
            'growth_model': 'linear',
            'growth_rate': 0.15,
            'changes': {
                'operating_expenses': {'multiply': 0.9}
            },
            'assumptions': ['Market headwinds', 'Focus on profitability'],
            'cogs_ratio': 0.35,
            'opex_growth': 0.05,
            'capex_ratio': 0.03,
            'discount_rate': 0.08
        }
    ]
    
    print(analyze_financial_scenarios(example_base_case, example_scenarios))
