"""
Security and Compliance Assessor.

Analyzes security vulnerabilities, compliance readiness (GDPR, SOC2, HIPAA),
and overall security posture of technology stacks.
"""

from typing import Dict, List, Any, Optional
from datetime import datetime, timedelta


class SecurityAssessor:
    """Assess security and compliance readiness of technology stacks."""

    # Compliance standards mapping
    COMPLIANCE_STANDARDS = {
        'GDPR': ['data_privacy', 'consent_management', 'data_portability', 'right_to_deletion', 'audit_logging'],
        'SOC2': ['access_controls', 'encryption_at_rest', 'encryption_in_transit', 'audit_logging', 'backup_recovery'],
        'HIPAA': ['phi_protection', 'encryption_at_rest', 'encryption_in_transit', 'access_controls', 'audit_logging'],
        'PCI_DSS': ['payment_data_encryption', 'access_controls', 'network_security', 'vulnerability_management']
    }

    def __init__(self, security_data: Dict[str, Any]):
        """
        Initialize security assessor with security data.

        Args:
            security_data: Dictionary containing vulnerability and compliance data
        """
        self.technology = security_data.get('technology', 'Unknown')
        self.vulnerabilities = security_data.get('vulnerabilities', {})
        self.security_features = security_data.get('security_features', {})
        self.compliance_requirements = security_data.get('compliance_requirements', [])

    def calculate_security_score(self) -> Dict[str, Any]:
        """
        Calculate overall security score (0-100).

        Returns:
            Dictionary with security score components
        """
        # Component scores
        vuln_score = self._score_vulnerabilities()
        patch_score = self._score_patch_responsiveness()
        features_score = self._score_security_features()
        track_record_score = self._score_track_record()

        # Weighted average
        weights = {
            'vulnerability_score': 0.30,
            'patch_responsiveness': 0.25,
            'security_features': 0.30,
            'track_record': 0.15
        }

        overall = (
            vuln_score * weights['vulnerability_score'] +
            patch_score * weights['patch_responsiveness'] +
            features_score * weights['security_features'] +
            track_record_score * weights['track_record']
        )

        return {
            'overall_security_score': overall,
            'vulnerability_score': vuln_score,
            'patch_responsiveness': patch_score,
            'security_features_score': features_score,
            'track_record_score': track_record_score,
            'security_grade': self._calculate_grade(overall)
        }

    def _score_vulnerabilities(self) -> float:
        """
        Score based on vulnerability count and severity.

        Returns:
            Vulnerability score (0-100, higher is better)
        """
        # Get vulnerability counts by severity (last 12 months)
        critical = self.vulnerabilities.get('critical_last_12m', 0)
        high = self.vulnerabilities.get('high_last_12m', 0)
        medium = self.vulnerabilities.get('medium_last_12m', 0)
        low = self.vulnerabilities.get('low_last_12m', 0)

        # Calculate weighted vulnerability count
        weighted_vulns = (critical * 4) + (high * 2) + (medium * 1) + (low * 0.5)

        # Score based on weighted count (fewer is better)
        if weighted_vulns == 0:
            score = 100
        elif weighted_vulns <= 5:
            score = 90
        elif weighted_vulns <= 10:
            score = 80
        elif weighted_vulns <= 20:
            score = 70
        elif weighted_vulns <= 30:
            score = 60
        elif weighted_vulns <= 50:
            score = 50
        else:
            score = max(0, 50 - (weighted_vulns - 50) / 2)

        # Penalty for critical vulnerabilities
        if critical > 0:
            score = max(0, score - (critical * 10))

        return max(0.0, min(100.0, score))

    def _score_patch_responsiveness(self) -> float:
        """
        Score based on patch response time.

        Returns:
            Patch responsiveness score (0-100)
        """
        # Average days to patch critical vulnerabilities
        critical_patch_days = self.vulnerabilities.get('avg_critical_patch_days', 30)
        high_patch_days = self.vulnerabilities.get('avg_high_patch_days', 60)

        # Score critical patch time (most important)
        if critical_patch_days <= 7:
            critical_score = 50
        elif critical_patch_days <= 14:
            critical_score = 40
        elif critical_patch_days <= 30:
            critical_score = 30
        elif critical_patch_days <= 60:
            critical_score = 20
        else:
            critical_score = 10

        # Score high severity patch time
        if high_patch_days <= 14:
            high_score = 30
        elif high_patch_days <= 30:
            high_score = 25
        elif high_patch_days <= 60:
            high_score = 20
        elif high_patch_days <= 90:
            high_score = 15
        else:
            high_score = 10

        # Has active security team
        has_security_team = self.vulnerabilities.get('has_security_team', False)
        team_score = 20 if has_security_team else 0

        total_score = critical_score + high_score + team_score

        return min(100.0, total_score)

    def _score_security_features(self) -> float:
        """
        Score based on built-in security features.

        Returns:
            Security features score (0-100)
        """
        score = 0.0

        # Essential features (10 points each)
        essential_features = [
            'encryption_at_rest',
            'encryption_in_transit',
            'authentication',
            'authorization',
            'input_validation'
        ]

        for feature in essential_features:
            if self.security_features.get(feature, False):
                score += 10

        # Advanced features (5 points each)
        advanced_features = [
            'rate_limiting',
            'csrf_protection',
            'xss_protection',
            'sql_injection_protection',
            'audit_logging',
            'mfa_support',
            'rbac',
            'secrets_management',
            'security_headers',
            'cors_configuration'
        ]

        for feature in advanced_features:
            if self.security_features.get(feature, False):
                score += 5

        return min(100.0, score)

    def _score_track_record(self) -> float:
        """
        Score based on historical security track record.

        Returns:
            Track record score (0-100)
        """
        score = 50.0  # Start at neutral

        # Years since major security incident
        years_since_major = self.vulnerabilities.get('years_since_major_incident', 5)
        if years_since_major >= 3:
            score += 30
        elif years_since_major >= 1:
            score += 15
        else:
            score -= 10

        # Security certifications
        has_certifications = self.vulnerabilities.get('has_security_certifications', False)
        if has_certifications:
            score += 20

        # Bug bounty program
        has_bug_bounty = self.vulnerabilities.get('has_bug_bounty_program', False)
        if has_bug_bounty:
            score += 10

        # Security audits
        security_audits = self.vulnerabilities.get('security_audits_per_year', 0)
        score += min(20, security_audits * 10)

        return min(100.0, max(0.0, score))

    def _calculate_grade(self, score: float) -> str:
        """
        Convert score to letter grade.

        Args:
            score: Security score (0-100)

        Returns:
            Letter grade
        """
        if score >= 90:
            return "A"
        elif score >= 80:
            return "B"
        elif score >= 70:
            return "C"
        elif score >= 60:
            return "D"
        else:
            return "F"

    def assess_compliance(self, standards: List[str] = None) -> Dict[str, Dict[str, Any]]:
        """
        Assess compliance readiness for specified standards.

        Args:
            standards: List of compliance standards to assess (defaults to all required)

        Returns:
            Dictionary of compliance assessments by standard
        """
        if standards is None:
            standards = self.compliance_requirements

        results = {}

        for standard in standards:
            if standard not in self.COMPLIANCE_STANDARDS:
                results[standard] = {
                    'readiness': 'Unknown',
                    'score': 0,
                    'status': 'Unknown standard'
                }
                continue

            readiness = self._assess_standard_readiness(standard)
            results[standard] = readiness

        return results

    def _assess_standard_readiness(self, standard: str) -> Dict[str, Any]:
        """
        Assess readiness for a specific compliance standard.

        Args:
            standard: Compliance standard name

        Returns:
            Readiness assessment
        """
        required_features = self.COMPLIANCE_STANDARDS[standard]
        met_count = 0
        total_count = len(required_features)
        missing_features = []

        for feature in required_features:
            if self.security_features.get(feature, False):
                met_count += 1
            else:
                missing_features.append(feature)

        # Calculate readiness percentage
        readiness_pct = (met_count / total_count * 100) if total_count > 0 else 0

        # Determine readiness level
        if readiness_pct >= 90:
            readiness_level = "Ready"
            status = "Compliant - meets all requirements"
        elif readiness_pct >= 70:
            readiness_level = "Mostly Ready"
            status = "Minor gaps - additional configuration needed"
        elif readiness_pct >= 50:
            readiness_level = "Partial"
            status = "Significant work required"
        else:
            readiness_level = "Not Ready"
            status = "Major gaps - extensive implementation needed"

        return {
            'readiness_level': readiness_level,
            'readiness_percentage': readiness_pct,
            'status': status,
            'features_met': met_count,
            'features_required': total_count,
            'missing_features': missing_features,
            'recommendation': self._generate_compliance_recommendation(readiness_level, missing_features)
        }

    def _generate_compliance_recommendation(self, readiness_level: str, missing_features: List[str]) -> str:
        """
        Generate compliance recommendation.

        Args:
            readiness_level: Current readiness level
            missing_features: List of missing features

        Returns:
            Recommendation string
        """
        if readiness_level == "Ready":
            return "Proceed with compliance audit and certification"
        elif readiness_level == "Mostly Ready":
            return f"Implement missing features: {', '.join(missing_features[:3])}"
        elif readiness_level == "Partial":
            return f"Significant implementation needed. Start with: {', '.join(missing_features[:3])}"
        else:
            return "Not recommended without major security enhancements"

    def identify_vulnerabilities(self) -> Dict[str, Any]:
        """
        Identify and categorize vulnerabilities.

        Returns:
            Categorized vulnerability report
        """
        # Current vulnerabilities
        current = {
            'critical': self.vulnerabilities.get('critical_last_12m', 0),
            'high': self.vulnerabilities.get('high_last_12m', 0),
            'medium': self.vulnerabilities.get('medium_last_12m', 0),
            'low': self.vulnerabilities.get('low_last_12m', 0)
        }

        # Historical vulnerabilities (last 3 years)
        historical = {
            'critical': self.vulnerabilities.get('critical_last_3y', 0),
            'high': self.vulnerabilities.get('high_last_3y', 0),
            'medium': self.vulnerabilities.get('medium_last_3y', 0),
            'low': self.vulnerabilities.get('low_last_3y', 0)
        }

        # Common vulnerability types
        common_types = self.vulnerabilities.get('common_vulnerability_types', [
            'SQL Injection',
            'XSS',
            'CSRF',
            'Authentication Issues'
        ])

        return {
            'current_vulnerabilities': current,
            'total_current': sum(current.values()),
            'historical_vulnerabilities': historical,
            'total_historical': sum(historical.values()),
            'common_types': common_types,
            'severity_distribution': self._calculate_severity_distribution(current),
            'trend': self._analyze_vulnerability_trend(current, historical)
        }

    def _calculate_severity_distribution(self, vulnerabilities: Dict[str, int]) -> Dict[str, str]:
        """
        Calculate percentage distribution of vulnerability severities.

        Args:
            vulnerabilities: Vulnerability counts by severity

        Returns:
            Percentage distribution
        """
        total = sum(vulnerabilities.values())
        if total == 0:
            return {k: "0%" for k in vulnerabilities.keys()}

        return {
            severity: f"{(count / total * 100):.1f}%"
            for severity, count in vulnerabilities.items()
        }

    def _analyze_vulnerability_trend(self, current: Dict[str, int], historical: Dict[str, int]) -> str:
        """
        Analyze vulnerability trend.

        Args:
            current: Current vulnerabilities
            historical: Historical vulnerabilities

        Returns:
            Trend description
        """
        current_total = sum(current.values())
        historical_avg = sum(historical.values()) / 3  # 3-year average

        if current_total < historical_avg * 0.7:
            return "Improving - fewer vulnerabilities than historical average"
        elif current_total < historical_avg * 1.2:
            return "Stable - consistent with historical average"
        else:
            return "Concerning - more vulnerabilities than historical average"

    def generate_security_report(self) -> Dict[str, Any]:
        """
        Generate comprehensive security assessment report.

        Returns:
            Complete security analysis
        """
        security_score = self.calculate_security_score()
        compliance = self.assess_compliance()
        vulnerabilities = self.identify_vulnerabilities()

        # Generate recommendations
        recommendations = self._generate_security_recommendations(
            security_score,
            compliance,
            vulnerabilities
        )

        return {
            'technology': self.technology,
            'security_score': security_score,
            'compliance_assessment': compliance,
            'vulnerability_analysis': vulnerabilities,
            'recommendations': recommendations,
            'overall_risk_level': self._determine_risk_level(security_score['overall_security_score'])
        }

    def _generate_security_recommendations(
        self,
        security_score: Dict[str, Any],
        compliance: Dict[str, Dict[str, Any]],
        vulnerabilities: Dict[str, Any]
    ) -> List[str]:
        """
        Generate security recommendations.

        Args:
            security_score: Security score data
            compliance: Compliance assessment
            vulnerabilities: Vulnerability analysis

        Returns:
            List of recommendations
        """
        recommendations = []

        # Security score recommendations
        if security_score['overall_security_score'] < 70:
            recommendations.append("Improve overall security posture - score below acceptable threshold")

        # Vulnerability recommendations
        current_critical = vulnerabilities['current_vulnerabilities']['critical']
        if current_critical > 0:
            recommendations.append(f"Address {current_critical} critical vulnerabilities immediately")

        # Patch responsiveness
        if security_score['patch_responsiveness'] < 60:
            recommendations.append("Improve vulnerability patch response time")

        # Security features
        if security_score['security_features_score'] < 70:
            recommendations.append("Implement additional security features (MFA, audit logging, RBAC)")

        # Compliance recommendations
        for standard, assessment in compliance.items():
            if assessment['readiness_level'] == "Not Ready":
                recommendations.append(f"{standard}: {assessment['recommendation']}")

        if not recommendations:
            recommendations.append("Security posture is strong - continue monitoring and maintenance")

        return recommendations

    def _determine_risk_level(self, security_score: float) -> str:
        """
        Determine overall risk level.

        Args:
            security_score: Overall security score

        Returns:
            Risk level description
        """
        if security_score >= 85:
            return "Low Risk - Strong security posture"
        elif security_score >= 70:
            return "Medium Risk - Acceptable with monitoring"
        elif security_score >= 55:
            return "High Risk - Security improvements needed"
        else:
            return "Critical Risk - Not recommended for production use"
