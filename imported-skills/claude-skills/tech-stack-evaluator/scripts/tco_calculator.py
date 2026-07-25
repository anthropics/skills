"""
Total Cost of Ownership (TCO) Calculator.

Calculates comprehensive TCO including licensing, hosting, developer productivity,
scaling costs, and hidden costs over multi-year projections.
"""

from typing import Dict, List, Any, Optional
import json


class TCOCalculator:
    """Calculate Total Cost of Ownership for technology stacks."""

    def __init__(self, tco_data: Dict[str, Any]):
        """
        Initialize TCO calculator with cost parameters.

        Args:
            tco_data: Dictionary containing cost parameters and projections
        """
        self.technology = tco_data.get('technology', 'Unknown')
        self.team_size = tco_data.get('team_size', 5)
        self.timeline_years = tco_data.get('timeline_years', 5)
        self.initial_costs = tco_data.get('initial_costs', {})
        self.operational_costs = tco_data.get('operational_costs', {})
        self.scaling_params = tco_data.get('scaling_params', {})
        self.productivity_factors = tco_data.get('productivity_factors', {})

    def calculate_initial_costs(self) -> Dict[str, float]:
        """
        Calculate one-time initial costs.

        Returns:
            Dictionary of initial cost components
        """
        costs = {
            'licensing': self.initial_costs.get('licensing', 0.0),
            'training': self._calculate_training_costs(),
            'migration': self.initial_costs.get('migration', 0.0),
            'setup': self.initial_costs.get('setup', 0.0),
            'tooling': self.initial_costs.get('tooling', 0.0)
        }

        costs['total_initial'] = sum(costs.values())
        return costs

    def _calculate_training_costs(self) -> float:
        """
        Calculate training costs based on team size and learning curve.

        Returns:
            Total training cost
        """
        # Default training assumptions
        hours_per_developer = self.initial_costs.get('training_hours_per_dev', 40)
        avg_hourly_rate = self.initial_costs.get('developer_hourly_rate', 100)
        training_materials = self.initial_costs.get('training_materials', 500)

        total_hours = self.team_size * hours_per_developer
        total_cost = (total_hours * avg_hourly_rate) + training_materials

        return total_cost

    def calculate_operational_costs(self) -> Dict[str, List[float]]:
        """
        Calculate ongoing operational costs per year.

        Returns:
            Dictionary with yearly cost projections
        """
        yearly_costs = {
            'licensing': [],
            'hosting': [],
            'support': [],
            'maintenance': [],
            'total_yearly': []
        }

        for year in range(1, self.timeline_years + 1):
            # Licensing costs (may include annual fees)
            license_cost = self.operational_costs.get('annual_licensing', 0.0)
            yearly_costs['licensing'].append(license_cost)

            # Hosting costs (scale with growth)
            hosting_cost = self._calculate_hosting_cost(year)
            yearly_costs['hosting'].append(hosting_cost)

            # Support costs
            support_cost = self.operational_costs.get('annual_support', 0.0)
            yearly_costs['support'].append(support_cost)

            # Maintenance costs (developer time)
            maintenance_cost = self._calculate_maintenance_cost(year)
            yearly_costs['maintenance'].append(maintenance_cost)

            # Total for year
            year_total = (
                license_cost + hosting_cost + support_cost + maintenance_cost
            )
            yearly_costs['total_yearly'].append(year_total)

        return yearly_costs

    def _calculate_hosting_cost(self, year: int) -> float:
        """
        Calculate hosting costs with growth projection.

        Args:
            year: Year number (1-indexed)

        Returns:
            Hosting cost for the year
        """
        base_cost = self.operational_costs.get('monthly_hosting', 1000.0) * 12
        growth_rate = self.scaling_params.get('annual_growth_rate', 0.20)  # 20% default

        # Apply compound growth
        year_cost = base_cost * ((1 + growth_rate) ** (year - 1))

        return year_cost

    def _calculate_maintenance_cost(self, year: int) -> float:
        """
        Calculate maintenance costs (developer time).

        Args:
            year: Year number (1-indexed)

        Returns:
            Maintenance cost for the year
        """
        hours_per_dev_per_month = self.operational_costs.get('maintenance_hours_per_dev_monthly', 20)
        avg_hourly_rate = self.initial_costs.get('developer_hourly_rate', 100)

        monthly_cost = self.team_size * hours_per_dev_per_month * avg_hourly_rate
        yearly_cost = monthly_cost * 12

        return yearly_cost

    def calculate_scaling_costs(self) -> Dict[str, Any]:
        """
        Calculate scaling-related costs and metrics.

        Returns:
            Dictionary with scaling cost analysis
        """
        # Project user growth
        initial_users = self.scaling_params.get('initial_users', 1000)
        annual_growth_rate = self.scaling_params.get('annual_growth_rate', 0.20)

        user_projections = []
        for year in range(1, self.timeline_years + 1):
            users = initial_users * ((1 + annual_growth_rate) ** year)
            user_projections.append(int(users))

        # Calculate cost per user
        operational = self.calculate_operational_costs()
        cost_per_user = []

        for year_idx, year_cost in enumerate(operational['total_yearly']):
            users = user_projections[year_idx]
            cost_per_user.append(year_cost / users if users > 0 else 0)

        # Infrastructure scaling costs
        infra_scaling = self._calculate_infrastructure_scaling()

        return {
            'user_projections': user_projections,
            'cost_per_user': cost_per_user,
            'infrastructure_scaling': infra_scaling,
            'scaling_efficiency': self._calculate_scaling_efficiency(cost_per_user)
        }

    def _calculate_infrastructure_scaling(self) -> Dict[str, List[float]]:
        """
        Calculate infrastructure scaling costs.

        Returns:
            Infrastructure cost projections
        """
        base_servers = self.scaling_params.get('initial_servers', 5)
        cost_per_server_monthly = self.scaling_params.get('cost_per_server_monthly', 200)
        growth_rate = self.scaling_params.get('annual_growth_rate', 0.20)

        server_costs = []
        for year in range(1, self.timeline_years + 1):
            servers_needed = base_servers * ((1 + growth_rate) ** year)
            yearly_cost = servers_needed * cost_per_server_monthly * 12
            server_costs.append(yearly_cost)

        return {
            'yearly_infrastructure_costs': server_costs
        }

    def _calculate_scaling_efficiency(self, cost_per_user: List[float]) -> str:
        """
        Assess scaling efficiency based on cost per user trend.

        Args:
            cost_per_user: List of yearly cost per user

        Returns:
            Efficiency assessment
        """
        if len(cost_per_user) < 2:
            return "Insufficient data"

        # Compare first year to last year
        initial = cost_per_user[0]
        final = cost_per_user[-1]

        if final < initial * 0.8:
            return "Excellent - economies of scale achieved"
        elif final < initial:
            return "Good - improving efficiency over time"
        elif final < initial * 1.2:
            return "Moderate - costs growing with users"
        else:
            return "Poor - costs growing faster than users"

    def calculate_productivity_impact(self) -> Dict[str, Any]:
        """
        Calculate developer productivity impact.

        Returns:
            Productivity analysis
        """
        # Productivity multiplier (1.0 = baseline)
        productivity_multiplier = self.productivity_factors.get('productivity_multiplier', 1.0)

        # Time to market impact (in days)
        ttm_reduction = self.productivity_factors.get('time_to_market_reduction_days', 0)

        # Calculate value of faster development
        avg_feature_time_days = self.productivity_factors.get('avg_feature_time_days', 30)
        features_per_year = 365 / avg_feature_time_days
        faster_features_per_year = 365 / max(1, avg_feature_time_days - ttm_reduction)

        additional_features = faster_features_per_year - features_per_year
        feature_value = self.productivity_factors.get('avg_feature_value', 10000)

        yearly_productivity_value = additional_features * feature_value

        return {
            'productivity_multiplier': productivity_multiplier,
            'time_to_market_reduction_days': ttm_reduction,
            'additional_features_per_year': additional_features,
            'yearly_productivity_value': yearly_productivity_value,
            'five_year_productivity_value': yearly_productivity_value * self.timeline_years
        }

    def calculate_hidden_costs(self) -> Dict[str, float]:
        """
        Identify and calculate hidden costs.

        Returns:
            Dictionary of hidden cost components
        """
        costs = {
            'technical_debt': self._estimate_technical_debt(),
            'vendor_lock_in_risk': self._estimate_vendor_lock_in_cost(),
            'security_incidents': self._estimate_security_costs(),
            'downtime_risk': self._estimate_downtime_costs(),
            'developer_turnover': self._estimate_turnover_costs()
        }

        costs['total_hidden_costs'] = sum(costs.values())
        return costs

    def _estimate_technical_debt(self) -> float:
        """
        Estimate technical debt accumulation costs.

        Returns:
            Estimated technical debt cost
        """
        # Percentage of development time spent on debt
        debt_percentage = self.productivity_factors.get('technical_debt_percentage', 0.15)
        yearly_dev_cost = self._calculate_maintenance_cost(1)  # Year 1 baseline

        # Technical debt accumulates over time
        total_debt_cost = 0
        for year in range(1, self.timeline_years + 1):
            year_debt = yearly_dev_cost * debt_percentage * year  # Increases each year
            total_debt_cost += year_debt

        return total_debt_cost

    def _estimate_vendor_lock_in_cost(self) -> float:
        """
        Estimate cost of vendor lock-in.

        Returns:
            Estimated lock-in cost
        """
        lock_in_risk = self.productivity_factors.get('vendor_lock_in_risk', 'low')

        # Migration cost if switching vendors
        migration_cost = self.initial_costs.get('migration', 10000)

        risk_multipliers = {
            'low': 0.1,
            'medium': 0.3,
            'high': 0.6
        }

        multiplier = risk_multipliers.get(lock_in_risk, 0.2)
        return migration_cost * multiplier

    def _estimate_security_costs(self) -> float:
        """
        Estimate potential security incident costs.

        Returns:
            Estimated security cost
        """
        incidents_per_year = self.productivity_factors.get('security_incidents_per_year', 0.5)
        avg_incident_cost = self.productivity_factors.get('avg_security_incident_cost', 50000)

        total_cost = incidents_per_year * avg_incident_cost * self.timeline_years
        return total_cost

    def _estimate_downtime_costs(self) -> float:
        """
        Estimate downtime costs.

        Returns:
            Estimated downtime cost
        """
        hours_downtime_per_year = self.productivity_factors.get('downtime_hours_per_year', 2)
        cost_per_hour = self.productivity_factors.get('downtime_cost_per_hour', 5000)

        total_cost = hours_downtime_per_year * cost_per_hour * self.timeline_years
        return total_cost

    def _estimate_turnover_costs(self) -> float:
        """
        Estimate costs from developer turnover.

        Returns:
            Estimated turnover cost
        """
        turnover_rate = self.productivity_factors.get('annual_turnover_rate', 0.15)
        cost_per_hire = self.productivity_factors.get('cost_per_new_hire', 30000)

        hires_per_year = self.team_size * turnover_rate
        total_cost = hires_per_year * cost_per_hire * self.timeline_years

        return total_cost

    def calculate_total_tco(self) -> Dict[str, Any]:
        """
        Calculate complete TCO over the timeline.

        Returns:
            Comprehensive TCO analysis
        """
        initial = self.calculate_initial_costs()
        operational = self.calculate_operational_costs()
        scaling = self.calculate_scaling_costs()
        productivity = self.calculate_productivity_impact()
        hidden = self.calculate_hidden_costs()

        # Calculate total costs
        total_operational = sum(operational['total_yearly'])
        total_cost = initial['total_initial'] + total_operational + hidden['total_hidden_costs']

        # Adjust for productivity gains
        net_cost = total_cost - productivity['five_year_productivity_value']

        return {
            'technology': self.technology,
            'timeline_years': self.timeline_years,
            'initial_costs': initial,
            'operational_costs': operational,
            'scaling_analysis': scaling,
            'productivity_impact': productivity,
            'hidden_costs': hidden,
            'total_tco': total_cost,
            'net_tco_after_productivity': net_cost,
            'average_yearly_cost': total_cost / self.timeline_years
        }

    def generate_tco_summary(self) -> Dict[str, Any]:
        """
        Generate executive summary of TCO.

        Returns:
            TCO summary for reporting
        """
        tco = self.calculate_total_tco()

        return {
            'technology': self.technology,
            'total_tco': f"${tco['total_tco']:,.2f}",
            'net_tco': f"${tco['net_tco_after_productivity']:,.2f}",
            'average_yearly': f"${tco['average_yearly_cost']:,.2f}",
            'initial_investment': f"${tco['initial_costs']['total_initial']:,.2f}",
            'key_cost_drivers': self._identify_cost_drivers(tco),
            'cost_optimization_opportunities': self._identify_optimizations(tco)
        }

    def _identify_cost_drivers(self, tco: Dict[str, Any]) -> List[str]:
        """
        Identify top cost drivers.

        Args:
            tco: Complete TCO analysis

        Returns:
            List of top cost drivers
        """
        drivers = []

        # Check operational costs
        operational = tco['operational_costs']
        total_hosting = sum(operational['hosting'])
        total_maintenance = sum(operational['maintenance'])

        if total_hosting > total_maintenance:
            drivers.append(f"Infrastructure/hosting ({total_hosting:,.0f})")
        else:
            drivers.append(f"Developer maintenance time ({total_maintenance:,.0f})")

        # Check hidden costs
        hidden = tco['hidden_costs']
        if hidden['technical_debt'] > 10000:
            drivers.append(f"Technical debt ({hidden['technical_debt']:,.0f})")

        return drivers[:3]  # Top 3

    def _identify_optimizations(self, tco: Dict[str, Any]) -> List[str]:
        """
        Identify cost optimization opportunities.

        Args:
            tco: Complete TCO analysis

        Returns:
            List of optimization suggestions
        """
        optimizations = []

        # Check scaling efficiency
        scaling = tco['scaling_analysis']
        if scaling['scaling_efficiency'].startswith('Poor'):
            optimizations.append("Improve scaling efficiency - costs growing too fast")

        # Check hidden costs
        hidden = tco['hidden_costs']
        if hidden['technical_debt'] > 20000:
            optimizations.append("Address technical debt accumulation")

        if hidden['downtime_risk'] > 10000:
            optimizations.append("Invest in reliability to reduce downtime costs")

        return optimizations
