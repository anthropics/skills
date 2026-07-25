#!/usr/bin/env python3
"""
Root Cause Analyzer - Structured root cause analysis for CAPA investigations.

Supports multiple analysis methodologies:
- 5-Why Analysis
- Fishbone (Ishikawa) Diagram
- Fault Tree Analysis
- Kepner-Tregoe Problem Analysis

Generates structured root cause reports and CAPA recommendations.

Usage:
    python root_cause_analyzer.py --method 5why --problem "High defect rate in assembly line"
    python root_cause_analyzer.py --interactive
    python root_cause_analyzer.py --data investigation.json --output json
"""

import argparse
import json
import sys
from dataclasses import dataclass, field, asdict
from typing import List, Dict, Optional
from enum import Enum
from datetime import datetime


class AnalysisMethod(Enum):
    FIVE_WHY = "5-Why"
    FISHBONE = "Fishbone"
    FAULT_TREE = "Fault Tree"
    KEPNER_TREGOE = "Kepner-Tregoe"


class RootCauseCategory(Enum):
    MAN = "Man (People)"
    MACHINE = "Machine (Equipment)"
    MATERIAL = "Material"
    METHOD = "Method (Process)"
    MEASUREMENT = "Measurement"
    ENVIRONMENT = "Environment"
    MANAGEMENT = "Management (Policy)"
    SOFTWARE = "Software/Data"


class SeverityLevel(Enum):
    LOW = "Low"
    MEDIUM = "Medium"
    HIGH = "High"
    CRITICAL = "Critical"


@dataclass
class WhyStep:
    """A single step in 5-Why analysis."""
    level: int
    question: str
    answer: str
    evidence: str = ""
    verified: bool = False


@dataclass
class FishboneCause:
    """A cause in fishbone analysis."""
    category: str
    cause: str
    sub_causes: List[str] = field(default_factory=list)
    is_root: bool = False
    evidence: str = ""


@dataclass
class FaultEvent:
    """An event in fault tree analysis."""
    event_id: str
    description: str
    is_basic: bool = True  # Basic events have no children
    gate_type: str = "OR"  # OR, AND
    children: List[str] = field(default_factory=list)
    probability: Optional[float] = None


@dataclass
class RootCauseFinding:
    """Identified root cause with evidence."""
    cause_id: str
    description: str
    category: str
    evidence: List[str] = field(default_factory=list)
    contributing_factors: List[str] = field(default_factory=list)
    systemic: bool = False  # Whether it's a systemic vs. local issue


@dataclass
class CAPARecommendation:
    """Corrective or preventive action recommendation."""
    action_id: str
    action_type: str  # "Corrective" or "Preventive"
    description: str
    addresses_cause: str  # cause_id
    priority: str
    estimated_effort: str
    responsible_role: str
    effectiveness_criteria: List[str] = field(default_factory=list)


@dataclass
class RootCauseAnalysis:
    """Complete root cause analysis result."""
    investigation_id: str
    problem_statement: str
    analysis_method: str
    root_causes: List[RootCauseFinding]
    recommendations: List[CAPARecommendation]
    analysis_details: Dict
    confidence_level: float
    investigator_notes: List[str] = field(default_factory=list)


class RootCauseAnalyzer:
    """Performs structured root cause analysis."""

    def __init__(self):
        self.analysis_steps = []
        self.findings = []

    def analyze_5why(self, problem: str, whys: List[Dict] = None) -> Dict:
        """Perform 5-Why analysis."""
        steps = []
        if whys:
            for i, w in enumerate(whys, 1):
                steps.append(WhyStep(
                    level=i,
                    question=w.get("question", f"Why did this occur? (Level {i})"),
                    answer=w.get("answer", ""),
                    evidence=w.get("evidence", ""),
                    verified=w.get("verified", False)
                ))

        # Analyze depth and quality
        depth = len(steps)
        has_root = any(
            s.answer and ("system" in s.answer.lower() or "policy" in s.answer.lower() or "process" in s.answer.lower())
            for s in steps
        )

        return {
            "method": "5-Why Analysis",
            "steps": [asdict(s) for s in steps],
            "depth": depth,
            "reached_systemic_cause": has_root,
            "quality_score": min(100, depth * 20 + (20 if has_root else 0))
        }

    def analyze_fishbone(self, problem: str, causes: List[Dict] = None) -> Dict:
        """Perform fishbone (Ishikawa) analysis."""
        categories = {}
        fishbone_causes = []

        if causes:
            for c in causes:
                cat = c.get("category", "Method")
                cause = c.get("cause", "")
                sub = c.get("sub_causes", [])

                if cat not in categories:
                    categories[cat] = []
                categories[cat].append({
                    "cause": cause,
                    "sub_causes": sub,
                    "is_root": c.get("is_root", False),
                    "evidence": c.get("evidence", "")
                })
                fishbone_causes.append(FishboneCause(
                    category=cat,
                    cause=cause,
                    sub_causes=sub,
                    is_root=c.get("is_root", False),
                    evidence=c.get("evidence", "")
                ))

        root_causes = [fc for fc in fishbone_causes if fc.is_root]

        return {
            "method": "Fishbone (Ishikawa) Analysis",
            "problem": problem,
            "categories": categories,
            "total_causes": len(fishbone_causes),
            "root_causes_identified": len(root_causes),
            "categories_covered": list(categories.keys()),
            "recommended_categories": [c.value for c in RootCauseCategory],
            "missing_categories": [c.value for c in RootCauseCategory if c.value.split(" (")[0] not in categories]
        }

    def analyze_fault_tree(self, top_event: str, events: List[Dict] = None) -> Dict:
        """Perform fault tree analysis."""
        fault_events = {}
        if events:
            for e in events:
                fault_events[e["event_id"]] = FaultEvent(
                    event_id=e["event_id"],
                    description=e.get("description", ""),
                    is_basic=e.get("is_basic", True),
                    gate_type=e.get("gate_type", "OR"),
                    children=e.get("children", []),
                    probability=e.get("probability")
                )

        # Find basic events (root causes)
        basic_events = {eid: ev for eid, ev in fault_events.items() if ev.is_basic}
        intermediate_events = {eid: ev for eid, ev in fault_events.items() if not ev.is_basic}

        return {
            "method": "Fault Tree Analysis",
            "top_event": top_event,
            "total_events": len(fault_events),
            "basic_events": len(basic_events),
            "intermediate_events": len(intermediate_events),
            "basic_event_details": [asdict(e) for e in basic_events.values()],
            "cut_sets": self._find_cut_sets(fault_events)
        }

    def _find_cut_sets(self, events: Dict[str, FaultEvent]) -> List[List[str]]:
        """Find minimal cut sets (combinations of basic events that cause top event)."""
        # Simplified cut set analysis
        cut_sets = []
        for eid, event in events.items():
            if not event.is_basic and event.gate_type == "AND":
                cut_sets.append(event.children)
        return cut_sets[:5]  # Return top 5

    def generate_recommendations(
        self,
        root_causes: List[RootCauseFinding],
        problem: str
    ) -> List[CAPARecommendation]:
        """Generate CAPA recommendations based on root causes."""
        recommendations = []

        for i, cause in enumerate(root_causes, 1):
            # Corrective action (fix the immediate cause)
            recommendations.append(CAPARecommendation(
                action_id=f"CA-{i:03d}",
                action_type="Corrective",
                description=f"Address immediate cause: {cause.description}",
                addresses_cause=cause.cause_id,
                priority=self._assess_priority(cause),
                estimated_effort=self._estimate_effort(cause),
                responsible_role=self._suggest_responsible(cause),
                effectiveness_criteria=[
                    f"Elimination of {cause.description} confirmed by audit",
                    "No recurrence within 90 days",
                    "Metrics return to acceptable range"
                ]
            ))

            # Preventive action (prevent recurrence in other areas)
            if cause.systemic:
                recommendations.append(CAPARecommendation(
                    action_id=f"PA-{i:03d}",
                    action_type="Preventive",
                    description=f"Systemic prevention: Update process/procedure to prevent similar issues",
                    addresses_cause=cause.cause_id,
                    priority="Medium",
                    estimated_effort="2-4 weeks",
                    responsible_role="Quality Manager",
                    effectiveness_criteria=[
                        "Updated procedure approved and implemented",
                        "Training completed for affected personnel",
                        "No similar issues in related processes within 6 months"
                    ]
                ))

        return recommendations

    def _assess_priority(self, cause: RootCauseFinding) -> str:
        if cause.systemic or "safety" in cause.description.lower():
            return "High"
        elif "quality" in cause.description.lower():
            return "Medium"
        return "Low"

    def _estimate_effort(self, cause: RootCauseFinding) -> str:
        if cause.systemic:
            return "4-8 weeks"
        elif len(cause.contributing_factors) > 3:
            return "2-4 weeks"
        return "1-2 weeks"

    def _suggest_responsible(self, cause: RootCauseFinding) -> str:
        category_roles = {
            "Man": "Training Manager",
            "Machine": "Engineering Manager",
            "Material": "Supply Chain Manager",
            "Method": "Process Owner",
            "Measurement": "Quality Engineer",
            "Environment": "Facilities Manager",
            "Management": "Department Head",
            "Software": "IT/Software Manager"
        }
        cat_key = cause.category.split(" (")[0] if "(" in cause.category else cause.category
        return category_roles.get(cat_key, "Quality Manager")

    def full_analysis(
        self,
        problem: str,
        method: str = "5-Why",
        analysis_data: Dict = None
    ) -> RootCauseAnalysis:
        """Perform complete root cause analysis."""
        investigation_id = f"RCA-{datetime.now().strftime('%Y%m%d-%H%M')}"
        analysis_details = {}
        root_causes = []

        if method == "5-Why" and analysis_data:
            analysis_details = self.analyze_5why(problem, analysis_data.get("whys", []))
            # Extract root cause from deepest why
            steps = analysis_details.get("steps", [])
            if steps:
                last_step = steps[-1]
                root_causes.append(RootCauseFinding(
                    cause_id="RC-001",
                    description=last_step.get("answer", "Unknown"),
                    category="Systemic",
                    evidence=[s.get("evidence", "") for s in steps if s.get("evidence")],
                    systemic=analysis_details.get("reached_systemic_cause", False)
                ))

        elif method == "Fishbone" and analysis_data:
            analysis_details = self.analyze_fishbone(problem, analysis_data.get("causes", []))
            for i, cat in enumerate(analysis_data.get("causes", [])):
                if cat.get("is_root"):
                    root_causes.append(RootCauseFinding(
                        cause_id=f"RC-{i+1:03d}",
                        description=cat.get("cause", ""),
                        category=cat.get("category", ""),
                        evidence=[cat.get("evidence", "")] if cat.get("evidence") else [],
                        sub_causes=cat.get("sub_causes", []),
                        systemic=True
                    ))

        recommendations = self.generate_recommendations(root_causes, problem)

        # Confidence based on evidence and method
        confidence = 0.7
        if root_causes and any(rc.evidence for rc in root_causes):
            confidence = 0.85
        if len(root_causes) > 1:
            confidence = min(0.95, confidence + 0.05)

        return RootCauseAnalysis(
            investigation_id=investigation_id,
            problem_statement=problem,
            analysis_method=method,
            root_causes=root_causes,
            recommendations=recommendations,
            analysis_details=analysis_details,
            confidence_level=confidence
        )


def format_rca_text(rca: RootCauseAnalysis) -> str:
    """Format RCA report as text."""
    lines = [
        "=" * 70,
        "ROOT CAUSE ANALYSIS REPORT",
        "=" * 70,
        f"Investigation ID: {rca.investigation_id}",
        f"Analysis Method: {rca.analysis_method}",
        f"Confidence Level: {rca.confidence_level:.0%}",
        "",
        "PROBLEM STATEMENT",
        "-" * 40,
        f"  {rca.problem_statement}",
        "",
        "ROOT CAUSES IDENTIFIED",
        "-" * 40,
    ]

    for rc in rca.root_causes:
        lines.extend([
            f"",
            f"  [{rc.cause_id}] {rc.description}",
            f"  Category: {rc.category}",
            f"  Systemic: {'Yes' if rc.systemic else 'No'}",
        ])
        if rc.evidence:
            lines.append(f"  Evidence:")
            for ev in rc.evidence:
                if ev:
                    lines.append(f"    • {ev}")
        if rc.contributing_factors:
            lines.append(f"  Contributing Factors:")
            for cf in rc.contributing_factors:
                lines.append(f"    - {cf}")

    lines.extend([
        "",
        "RECOMMENDED ACTIONS",
        "-" * 40,
    ])

    for rec in rca.recommendations:
        lines.extend([
            f"",
            f"  [{rec.action_id}] {rec.action_type}: {rec.description}",
            f"  Priority: {rec.priority} | Effort: {rec.estimated_effort}",
            f"  Responsible: {rec.responsible_role}",
            f"  Effectiveness Criteria:",
        ])
        for ec in rec.effectiveness_criteria:
            lines.append(f"    ✓ {ec}")

    if "steps" in rca.analysis_details:
        lines.extend([
            "",
            "5-WHY CHAIN",
            "-" * 40,
        ])
        for step in rca.analysis_details["steps"]:
            lines.extend([
                f"",
                f"  Why {step['level']}: {step['question']}",
                f"  → {step['answer']}",
            ])
            if step.get("evidence"):
                lines.append(f"  Evidence: {step['evidence']}")

    lines.append("=" * 70)
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description="Root Cause Analyzer for CAPA Investigations")
    parser.add_argument("--problem", type=str, help="Problem statement")
    parser.add_argument("--method", choices=["5why", "fishbone", "fault-tree", "kt"],
                       default="5why", help="Analysis method")
    parser.add_argument("--data", type=str, help="JSON file with analysis data")
    parser.add_argument("--output", choices=["text", "json"], default="text", help="Output format")
    parser.add_argument("--interactive", action="store_true", help="Interactive mode")

    args = parser.parse_args()

    analyzer = RootCauseAnalyzer()

    if args.data:
        with open(args.data) as f:
            data = json.load(f)
        problem = data.get("problem", "Unknown problem")
        method = data.get("method", "5-Why")
        rca = analyzer.full_analysis(problem, method, data)
    elif args.problem:
        method_map = {"5why": "5-Why", "fishbone": "Fishbone", "fault-tree": "Fault Tree", "kt": "Kepner-Tregoe"}
        rca = analyzer.full_analysis(args.problem, method_map.get(args.method, "5-Why"))
    else:
        # Demo
        demo_data = {
            "method": "5-Why",
            "whys": [
                {"question": "Why did the product fail inspection?", "answer": "Surface defect detected on 15% of units", "evidence": "QC inspection records"},
                {"question": "Why did surface defects occur?", "answer": "Injection molding temperature was outside spec", "evidence": "Process monitoring data"},
                {"question": "Why was temperature outside spec?", "answer": "Temperature controller calibration drift", "evidence": "Calibration log"},
                {"question": "Why did calibration drift go undetected?", "answer": "No automated alert for drift, manual checks missed it", "evidence": "SOP review"},
                {"question": "Why was there no automated alert?", "answer": "Process monitoring system lacks drift detection capability - systemic gap", "evidence": "System requirements review"}
            ]
        }
        rca = analyzer.full_analysis("High defect rate in injection molding process", "5-Why", demo_data)

    if args.output == "json":
        result = {
            "investigation_id": rca.investigation_id,
            "problem": rca.problem_statement,
            "method": rca.analysis_method,
            "root_causes": [asdict(rc) for rc in rca.root_causes],
            "recommendations": [asdict(rec) for rec in rca.recommendations],
            "analysis_details": rca.analysis_details,
            "confidence": rca.confidence_level
        }
        print(json.dumps(result, indent=2, default=str))
    else:
        print(format_rca_text(rca))


if __name__ == "__main__":
    main()
