#!/usr/bin/env python3
"""
Regulatory Pathway Analyzer - Determines optimal regulatory pathway for medical devices.

Analyzes device characteristics and recommends the most efficient regulatory pathway
across multiple markets (FDA, EU MDR, UK UKCA, Health Canada, TGA, PMDA).

Supports:
- FDA: 510(k), De Novo, PMA, Breakthrough Device
- EU MDR: Class I, IIa, IIb, III, AIMDD
- UK: UKCA marking
- Health Canada: Class I-IV
- TGA: Class I, IIa, IIb, III
- Japan PMDA: Class I-IV

Usage:
    python regulatory_pathway_analyzer.py --device-class II --predicate yes --market all
    python regulatory_pathway_analyzer.py --interactive
    python regulatory_pathway_analyzer.py --data device_profile.json --output json
"""

import argparse
import json
import sys
from dataclasses import dataclass, field, asdict
from typing import List, Dict, Optional, Tuple
from enum import Enum


class RiskClass(Enum):
    CLASS_I = "I"
    CLASS_IIA = "IIa"
    CLASS_IIB = "IIb"
    CLASS_III = "III"
    CLASS_IV = "IV"


class MarketRegion(Enum):
    US_FDA = "US-FDA"
    EU_MDR = "EU-MDR"
    UK_UKCA = "UK-UKCA"
    HEALTH_CANADA = "Health-Canada"
    AUSTRALIA_TGA = "Australia-TGA"
    JAPAN_PMDA = "Japan-PMDA"


@dataclass
class DeviceProfile:
    """Medical device profile for pathway analysis."""
    device_name: str
    intended_use: str
    device_class: str  # I, IIa, IIb, III
    novel_technology: bool = False
    predicate_available: bool = True
    implantable: bool = False
    life_sustaining: bool = False
    software_component: bool = False
    ai_ml_component: bool = False
    sterile: bool = False
    measuring_function: bool = False
    target_markets: List[str] = field(default_factory=lambda: ["US-FDA", "EU-MDR"])


@dataclass
class PathwayOption:
    """A regulatory pathway option."""
    pathway_name: str
    market: str
    estimated_timeline_months: Tuple[int, int]
    estimated_cost_usd: Tuple[int, int]
    key_requirements: List[str]
    advantages: List[str]
    risks: List[str]
    recommendation_level: str  # "Recommended", "Alternative", "Not Recommended"


@dataclass
class PathwayAnalysis:
    """Complete pathway analysis result."""
    device: DeviceProfile
    recommended_pathways: List[PathwayOption]
    optimal_sequence: List[str]  # Recommended submission order
    total_timeline_months: Tuple[int, int]
    total_estimated_cost: Tuple[int, int]
    critical_success_factors: List[str]
    warnings: List[str]


class RegulatoryPathwayAnalyzer:
    """Analyzes and recommends regulatory pathways for medical devices."""

    # FDA pathway decision matrix
    FDA_PATHWAYS = {
        "I": {
            "pathway": "510(k) Exempt / Registration & Listing",
            "timeline": (1, 3),
            "cost": (5000, 15000),
            "requirements": ["Establishment registration", "Device listing", "GMP compliance (if non-exempt)"]
        },
        "II": {
            "pathway": "510(k)",
            "timeline": (6, 12),
            "cost": (50000, 250000),
            "requirements": ["Predicate device identification", "Substantial equivalence demonstration", "Performance testing", "Biocompatibility (if applicable)", "Software documentation (if applicable)"]
        },
        "II-novel": {
            "pathway": "De Novo",
            "timeline": (12, 18),
            "cost": (150000, 400000),
            "requirements": ["Risk-based classification request", "Special controls development", "Performance testing", "Clinical data (potentially)"]
        },
        "III": {
            "pathway": "PMA",
            "timeline": (18, 36),
            "cost": (500000, 2000000),
            "requirements": ["Clinical investigations", "Manufacturing information", "Performance testing", "Risk-benefit analysis", "Post-approval studies"]
        },
        "III-breakthrough": {
            "pathway": "Breakthrough Device Program + PMA",
            "timeline": (12, 24),
            "cost": (500000, 2000000),
            "requirements": ["Breakthrough designation request", "More flexible clinical evidence", "Iterative FDA engagement", "Post-market data collection"]
        }
    }

    # EU MDR pathway decision matrix
    EU_MDR_PATHWAYS = {
        "I": {
            "pathway": "Self-declaration (Class I)",
            "timeline": (2, 4),
            "cost": (10000, 30000),
            "requirements": ["Technical documentation", "EU Declaration of Conformity", "UDI assignment", "EUDAMED registration", "Authorized Representative (if non-EU)"]
        },
        "IIa": {
            "pathway": "Notified Body assessment (Class IIa)",
            "timeline": (12, 18),
            "cost": (80000, 200000),
            "requirements": ["QMS certification (ISO 13485)", "Technical documentation", "Clinical evaluation", "Notified Body audit", "Post-market surveillance plan"]
        },
        "IIb": {
            "pathway": "Notified Body assessment (Class IIb)",
            "timeline": (15, 24),
            "cost": (150000, 400000),
            "requirements": ["Full QMS certification", "Comprehensive technical documentation", "Clinical evaluation (may need clinical investigation)", "Type examination or product verification", "Notified Body scrutiny"]
        },
        "III": {
            "pathway": "Notified Body assessment (Class III)",
            "timeline": (18, 30),
            "cost": (300000, 800000),
            "requirements": ["Full QMS certification", "Complete technical documentation", "Clinical investigation (typically required)", "Notified Body clinical evaluation review", "Scrutiny procedure (possible)", "PMCF plan"]
        }
    }

    def __init__(self):
        self.analysis_warnings = []

    def analyze_fda_pathway(self, device: DeviceProfile) -> PathwayOption:
        """Determine optimal FDA pathway."""
        device_class = device.device_class.upper().replace("IIA", "II").replace("IIB", "II")

        if device_class == "I":
            pathway_data = self.FDA_PATHWAYS["I"]
            return PathwayOption(
                pathway_name=pathway_data["pathway"],
                market="US-FDA",
                estimated_timeline_months=pathway_data["timeline"],
                estimated_cost_usd=pathway_data["cost"],
                key_requirements=pathway_data["requirements"],
                advantages=["Fastest path to market", "Minimal regulatory burden", "No premarket submission required (if exempt)"],
                risks=["Limited to exempt product codes", "Still requires GMP compliance"],
                recommendation_level="Recommended"
            )

        elif device_class == "III" or device.implantable or device.life_sustaining:
            if device.novel_technology:
                pathway_data = self.FDA_PATHWAYS["III-breakthrough"]
                rec_level = "Recommended" if device.novel_technology else "Alternative"
            else:
                pathway_data = self.FDA_PATHWAYS["III"]
                rec_level = "Recommended"
        else:  # Class II
            if device.predicate_available and not device.novel_technology:
                pathway_data = self.FDA_PATHWAYS["II"]
                rec_level = "Recommended"
            else:
                pathway_data = self.FDA_PATHWAYS["II-novel"]
                rec_level = "Recommended"

        return PathwayOption(
            pathway_name=pathway_data["pathway"],
            market="US-FDA",
            estimated_timeline_months=pathway_data["timeline"],
            estimated_cost_usd=pathway_data["cost"],
            key_requirements=pathway_data["requirements"],
            advantages=self._get_fda_advantages(pathway_data["pathway"], device),
            risks=self._get_fda_risks(pathway_data["pathway"], device),
            recommendation_level=rec_level
        )

    def analyze_eu_mdr_pathway(self, device: DeviceProfile) -> PathwayOption:
        """Determine optimal EU MDR pathway."""
        device_class = device.device_class.lower().replace("iia", "IIa").replace("iib", "IIb")

        if device_class in ["i", "1"]:
            pathway_data = self.EU_MDR_PATHWAYS["I"]
            class_key = "I"
        elif device_class in ["iia", "2a"]:
            pathway_data = self.EU_MDR_PATHWAYS["IIa"]
            class_key = "IIa"
        elif device_class in ["iib", "2b"]:
            pathway_data = self.EU_MDR_PATHWAYS["IIb"]
            class_key = "IIb"
        else:
            pathway_data = self.EU_MDR_PATHWAYS["III"]
            class_key = "III"

        # Adjust for implantables
        if device.implantable and class_key in ["IIa", "IIb"]:
            pathway_data = self.EU_MDR_PATHWAYS["III"]
            self.analysis_warnings.append(
                f"Implantable devices are typically upclassified to Class III under EU MDR"
            )

        return PathwayOption(
            pathway_name=pathway_data["pathway"],
            market="EU-MDR",
            estimated_timeline_months=pathway_data["timeline"],
            estimated_cost_usd=pathway_data["cost"],
            key_requirements=pathway_data["requirements"],
            advantages=self._get_eu_advantages(pathway_data["pathway"], device),
            risks=self._get_eu_risks(pathway_data["pathway"], device),
            recommendation_level="Recommended"
        )

    def _get_fda_advantages(self, pathway: str, device: DeviceProfile) -> List[str]:
        advantages = []
        if "510(k)" in pathway:
            advantages.extend([
                "Well-established pathway with clear guidance",
                "Predictable review timeline",
                "Lower clinical evidence requirements vs PMA"
            ])
            if device.predicate_available:
                advantages.append("Predicate device identified - streamlined review")
        elif "De Novo" in pathway:
            advantages.extend([
                "Creates new predicate for future 510(k) submissions",
                "Appropriate for novel low-moderate risk devices",
                "Can result in Class I or II classification"
            ])
        elif "PMA" in pathway:
            advantages.extend([
                "Strongest FDA approval - highest market credibility",
                "Difficult for competitors to challenge",
                "May qualify for breakthrough device benefits"
            ])
        elif "Breakthrough" in pathway:
            advantages.extend([
                "Priority review and interactive FDA engagement",
                "Flexible clinical evidence requirements",
                "Faster iterative development with FDA feedback"
            ])
        return advantages

    def _get_fda_risks(self, pathway: str, device: DeviceProfile) -> List[str]:
        risks = []
        if "510(k)" in pathway:
            risks.extend([
                "Predicate device may be challenged",
                "SE determination can be subjective"
            ])
            if device.software_component:
                risks.append("Software documentation requirements increasing (Cybersecurity, AI/ML)")
        elif "De Novo" in pathway:
            risks.extend([
                "Less predictable than 510(k)",
                "May require more clinical data than expected",
                "New special controls may be imposed"
            ])
        elif "PMA" in pathway:
            risks.extend([
                "Very expensive and time-consuming",
                "Clinical trial risks and delays",
                "Post-approval study requirements"
            ])
        if device.ai_ml_component:
            risks.append("AI/ML components face evolving regulatory requirements")
        return risks

    def _get_eu_advantages(self, pathway: str, device: DeviceProfile) -> List[str]:
        advantages = ["Access to entire EU/EEA market (27+ countries)"]
        if "Self-declaration" in pathway:
            advantages.extend([
                "No Notified Body involvement required",
                "Fastest path to EU market",
                "Lowest cost option"
            ])
        elif "IIa" in pathway:
            advantages.append("Moderate regulatory burden with broad market access")
        elif "IIb" in pathway or "III" in pathway:
            advantages.extend([
                "Strong market credibility with NB certification",
                "Recognized globally for regulatory quality"
            ])
        return advantages

    def _get_eu_risks(self, pathway: str, device: DeviceProfile) -> List[str]:
        risks = []
        if "Self-declaration" not in pathway:
            risks.extend([
                "Limited Notified Body capacity - long wait times",
                "Notified Body costs increasing under MDR"
            ])
        risks.append("MDR transition still creating uncertainty")
        if device.software_component:
            risks.append("EU AI Act may apply to AI/ML medical devices")
        return risks

    def determine_optimal_sequence(self, pathways: List[PathwayOption], device: DeviceProfile) -> List[str]:
        """Determine optimal submission sequence across markets."""
        # General principle: Start with fastest/cheapest, use data for subsequent submissions
        sequence = []

        # Sort by timeline (fastest first)
        sorted_pathways = sorted(pathways, key=lambda p: p.estimated_timeline_months[0])

        # FDA first if 510(k) - well recognized globally
        fda_pathway = next((p for p in pathways if p.market == "US-FDA"), None)
        eu_pathway = next((p for p in pathways if p.market == "EU-MDR"), None)

        if fda_pathway and "510(k)" in fda_pathway.pathway_name:
            sequence.append("1. US-FDA 510(k) first - clearance recognized globally, data reusable")
            if eu_pathway:
                sequence.append("2. EU-MDR - use FDA data in clinical evaluation")
        elif eu_pathway and "Self-declaration" in eu_pathway.pathway_name:
            sequence.append("1. EU-MDR (Class I self-declaration) - fastest market entry")
            if fda_pathway:
                sequence.append("2. US-FDA - use EU experience and data")
        else:
            for i, p in enumerate(sorted_pathways, 1):
                sequence.append(f"{i}. {p.market} ({p.pathway_name})")

        return sequence

    def analyze(self, device: DeviceProfile) -> PathwayAnalysis:
        """Perform complete pathway analysis."""
        self.analysis_warnings = []
        pathways = []

        for market in device.target_markets:
            if "FDA" in market or "US" in market:
                pathways.append(self.analyze_fda_pathway(device))
            elif "MDR" in market or "EU" in market:
                pathways.append(self.analyze_eu_mdr_pathway(device))
            # Additional markets can be added here

        sequence = self.determine_optimal_sequence(pathways, device)

        total_timeline_min = sum(p.estimated_timeline_months[0] for p in pathways)
        total_timeline_max = sum(p.estimated_timeline_months[1] for p in pathways)
        total_cost_min = sum(p.estimated_cost_usd[0] for p in pathways)
        total_cost_max = sum(p.estimated_cost_usd[1] for p in pathways)

        csf = [
            "Early engagement with regulators (Pre-Sub/Scientific Advice)",
            "Robust QMS (ISO 13485) in place before submissions",
            "Clinical evidence strategy aligned with target markets",
            "Cybersecurity and software documentation (if applicable)"
        ]

        if device.ai_ml_component:
            csf.append("AI/ML transparency and bias documentation")

        return PathwayAnalysis(
            device=device,
            recommended_pathways=pathways,
            optimal_sequence=sequence,
            total_timeline_months=(total_timeline_min, total_timeline_max),
            total_estimated_cost=(total_cost_min, total_cost_max),
            critical_success_factors=csf,
            warnings=self.analysis_warnings
        )


def format_analysis_text(analysis: PathwayAnalysis) -> str:
    """Format analysis as readable text report."""
    lines = [
        "=" * 70,
        "REGULATORY PATHWAY ANALYSIS REPORT",
        "=" * 70,
        f"Device: {analysis.device.device_name}",
        f"Intended Use: {analysis.device.intended_use}",
        f"Device Class: {analysis.device.device_class}",
        f"Target Markets: {', '.join(analysis.device.target_markets)}",
        "",
        "DEVICE CHARACTERISTICS",
        "-" * 40,
        f"  Novel Technology: {'Yes' if analysis.device.novel_technology else 'No'}",
        f"  Predicate Available: {'Yes' if analysis.device.predicate_available else 'No'}",
        f"  Implantable: {'Yes' if analysis.device.implantable else 'No'}",
        f"  Life-Sustaining: {'Yes' if analysis.device.life_sustaining else 'No'}",
        f"  Software/AI Component: {'Yes' if analysis.device.software_component or analysis.device.ai_ml_component else 'No'}",
        f"  Sterile: {'Yes' if analysis.device.sterile else 'No'}",
        "",
        "RECOMMENDED PATHWAYS",
        "-" * 40,
    ]

    for pathway in analysis.recommended_pathways:
        lines.extend([
            "",
            f"  [{pathway.market}] {pathway.pathway_name}",
            f"  Recommendation: {pathway.recommendation_level}",
            f"  Timeline: {pathway.estimated_timeline_months[0]}-{pathway.estimated_timeline_months[1]} months",
            f"  Estimated Cost: ${pathway.estimated_cost_usd[0]:,} - ${pathway.estimated_cost_usd[1]:,}",
            f"  Key Requirements:",
        ])
        for req in pathway.key_requirements:
            lines.append(f"    • {req}")
        lines.append(f"  Advantages:")
        for adv in pathway.advantages:
            lines.append(f"    + {adv}")
        lines.append(f"  Risks:")
        for risk in pathway.risks:
            lines.append(f"    ! {risk}")

    lines.extend([
        "",
        "OPTIMAL SUBMISSION SEQUENCE",
        "-" * 40,
    ])
    for step in analysis.optimal_sequence:
        lines.append(f"  {step}")

    lines.extend([
        "",
        "TOTAL ESTIMATES",
        "-" * 40,
        f"  Combined Timeline: {analysis.total_timeline_months[0]}-{analysis.total_timeline_months[1]} months",
        f"  Combined Cost: ${analysis.total_estimated_cost[0]:,} - ${analysis.total_estimated_cost[1]:,}",
        "",
        "CRITICAL SUCCESS FACTORS",
        "-" * 40,
    ])
    for i, factor in enumerate(analysis.critical_success_factors, 1):
        lines.append(f"  {i}. {factor}")

    if analysis.warnings:
        lines.extend([
            "",
            "WARNINGS",
            "-" * 40,
        ])
        for warning in analysis.warnings:
            lines.append(f"  ⚠ {warning}")

    lines.append("=" * 70)
    return "\n".join(lines)


def interactive_mode():
    """Interactive device profiling."""
    print("=" * 60)
    print("Regulatory Pathway Analyzer - Interactive Mode")
    print("=" * 60)

    device = DeviceProfile(
        device_name=input("\nDevice Name: ").strip(),
        intended_use=input("Intended Use: ").strip(),
        device_class=input("Device Class (I/IIa/IIb/III): ").strip(),
        novel_technology=input("Novel technology? (y/n): ").strip().lower() == 'y',
        predicate_available=input("Predicate device available? (y/n): ").strip().lower() == 'y',
        implantable=input("Implantable? (y/n): ").strip().lower() == 'y',
        life_sustaining=input("Life-sustaining? (y/n): ").strip().lower() == 'y',
        software_component=input("Software component? (y/n): ").strip().lower() == 'y',
        ai_ml_component=input("AI/ML component? (y/n): ").strip().lower() == 'y',
    )

    markets = input("Target markets (comma-separated, e.g., US-FDA,EU-MDR): ").strip()
    if markets:
        device.target_markets = [m.strip() for m in markets.split(",")]

    analyzer = RegulatoryPathwayAnalyzer()
    analysis = analyzer.analyze(device)
    print("\n" + format_analysis_text(analysis))


def main():
    parser = argparse.ArgumentParser(description="Regulatory Pathway Analyzer for Medical Devices")
    parser.add_argument("--device-name", type=str, help="Device name")
    parser.add_argument("--device-class", type=str, choices=["I", "IIa", "IIb", "III"], help="Device classification")
    parser.add_argument("--predicate", type=str, choices=["yes", "no"], help="Predicate device available")
    parser.add_argument("--novel", action="store_true", help="Novel technology")
    parser.add_argument("--implantable", action="store_true", help="Implantable device")
    parser.add_argument("--software", action="store_true", help="Software component")
    parser.add_argument("--ai-ml", action="store_true", help="AI/ML component")
    parser.add_argument("--market", type=str, default="all", help="Target market(s)")
    parser.add_argument("--data", type=str, help="JSON file with device profile")
    parser.add_argument("--output", choices=["text", "json"], default="text", help="Output format")
    parser.add_argument("--interactive", action="store_true", help="Interactive mode")

    args = parser.parse_args()

    if args.interactive:
        interactive_mode()
        return

    if args.data:
        with open(args.data) as f:
            data = json.load(f)
        device = DeviceProfile(**data)
    elif args.device_class:
        device = DeviceProfile(
            device_name=args.device_name or "Unnamed Device",
            intended_use="Medical device",
            device_class=args.device_class,
            novel_technology=args.novel,
            predicate_available=args.predicate == "yes" if args.predicate else True,
            implantable=args.implantable,
            software_component=args.software,
            ai_ml_component=args.ai_ml,
        )
        if args.market != "all":
            device.target_markets = [m.strip() for m in args.market.split(",")]
    else:
        # Demo mode
        device = DeviceProfile(
            device_name="SmartGlucose Monitor Pro",
            intended_use="Continuous glucose monitoring for diabetes management",
            device_class="II",
            novel_technology=False,
            predicate_available=True,
            software_component=True,
            ai_ml_component=True,
            target_markets=["US-FDA", "EU-MDR"]
        )

    analyzer = RegulatoryPathwayAnalyzer()
    analysis = analyzer.analyze(device)

    if args.output == "json":
        result = {
            "device": asdict(analysis.device),
            "pathways": [asdict(p) for p in analysis.recommended_pathways],
            "optimal_sequence": analysis.optimal_sequence,
            "total_timeline_months": list(analysis.total_timeline_months),
            "total_estimated_cost": list(analysis.total_estimated_cost),
            "critical_success_factors": analysis.critical_success_factors,
            "warnings": analysis.warnings
        }
        print(json.dumps(result, indent=2))
    else:
        print(format_analysis_text(analysis))


if __name__ == "__main__":
    main()
