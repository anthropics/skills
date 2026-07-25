#!/usr/bin/env python3
"""
PIR (Post-Incident Review) Generator

Generates comprehensive Post-Incident Review documents from incident data, timelines,
and actions taken. Applies multiple RCA frameworks including 5 Whys, Fishbone diagram,
and Timeline analysis.

This tool creates structured PIR documents with root cause analysis, lessons learned,
action items, and follow-up recommendations.

Usage:
    python pir_generator.py --incident incident.json --timeline timeline.json --output pir.md
    python pir_generator.py --incident incident.json --rca-method fishbone --action-items
    cat incident.json | python pir_generator.py --format markdown
"""

import argparse
import json
import sys
import re
from datetime import datetime, timezone, timedelta
from typing import Dict, List, Optional, Any, Tuple
from collections import defaultdict, Counter


class PIRGenerator:
    """
    Generates comprehensive Post-Incident Review documents with multiple
    RCA frameworks, lessons learned, and actionable follow-up items.
    """
    
    def __init__(self):
        """Initialize the PIR generator with templates and frameworks."""
        self.rca_frameworks = self._load_rca_frameworks()
        self.pir_templates = self._load_pir_templates()
        self.severity_guidelines = self._load_severity_guidelines()
        self.action_item_types = self._load_action_item_types()
        self.lessons_learned_categories = self._load_lessons_learned_categories()
    
    def _load_rca_frameworks(self) -> Dict[str, Dict]:
        """Load root cause analysis framework definitions."""
        return {
            "five_whys": {
                "name": "5 Whys Analysis",
                "description": "Iterative questioning technique to explore cause-and-effect relationships",
                "steps": [
                    "State the problem clearly",
                    "Ask why the problem occurred",
                    "For each answer, ask why again",
                    "Continue until root cause is identified",
                    "Verify the root cause addresses the original problem"
                ],
                "min_iterations": 3,
                "max_iterations": 7
            },
            "fishbone": {
                "name": "Fishbone (Ishikawa) Diagram",
                "description": "Systematic analysis across multiple categories of potential causes",
                "categories": [
                    {
                        "name": "People",
                        "description": "Human factors, training, communication, experience",
                        "examples": ["Training gaps", "Communication failures", "Skill deficits", "Staffing issues"]
                    },
                    {
                        "name": "Process",
                        "description": "Procedures, workflows, change management, review processes",
                        "examples": ["Missing procedures", "Inadequate reviews", "Change management gaps", "Documentation issues"]
                    },
                    {
                        "name": "Technology",
                        "description": "Systems, tools, architecture, automation",
                        "examples": ["Architecture limitations", "Tool deficiencies", "Automation gaps", "Infrastructure issues"]
                    },
                    {
                        "name": "Environment",
                        "description": "External factors, dependencies, infrastructure",
                        "examples": ["Third-party dependencies", "Network issues", "Hardware failures", "External service outages"]
                    }
                ]
            },
            "timeline": {
                "name": "Timeline Analysis",
                "description": "Chronological analysis of events to identify decision points and missed opportunities",
                "focus_areas": [
                    "Detection timing and effectiveness",
                    "Response time and escalation paths",
                    "Decision points and alternative paths",
                    "Communication effectiveness",
                    "Mitigation strategy effectiveness"
                ]
            },
            "bow_tie": {
                "name": "Bow Tie Analysis",
                "description": "Analysis of both preventive and protective measures around an incident",
                "components": [
                    "Hazards (what could go wrong)",
                    "Top events (what actually went wrong)",
                    "Threats (what caused it)",
                    "Consequences (what was the impact)",
                    "Barriers (what preventive/protective measures exist or could exist)"
                ]
            }
        }
    
    def _load_pir_templates(self) -> Dict[str, str]:
        """Load PIR document templates for different severity levels."""
        return {
            "comprehensive": """# Post-Incident Review: {incident_title}

## Executive Summary
{executive_summary}

## Incident Overview
- **Incident ID:** {incident_id}
- **Date & Time:** {incident_date}
- **Duration:** {duration}
- **Severity:** {severity}
- **Status:** {status}
- **Incident Commander:** {incident_commander}
- **Responders:** {responders}

### Customer Impact
{customer_impact}

### Business Impact  
{business_impact}

## Timeline
{timeline_section}

## Root Cause Analysis
{rca_section}

## What Went Well
{what_went_well}

## What Didn't Go Well
{what_went_wrong}

## Lessons Learned
{lessons_learned}

## Action Items
{action_items}

## Follow-up and Prevention
{prevention_measures}

## Appendix
{appendix_section}

---
*Generated on {generation_date} by PIR Generator*
""",
            "standard": """# Post-Incident Review: {incident_title}

## Summary
{executive_summary}

## Incident Details
- **Date:** {incident_date}
- **Duration:** {duration}  
- **Severity:** {severity}
- **Impact:** {customer_impact}

## Timeline
{timeline_section}

## Root Cause
{rca_section}

## Action Items
{action_items}

## Lessons Learned
{lessons_learned}

---
*Generated on {generation_date}*
""",
            "brief": """# Incident Review: {incident_title}

**Date:** {incident_date} | **Duration:** {duration} | **Severity:** {severity}

## What Happened
{executive_summary}

## Root Cause
{rca_section}

## Actions
{action_items}

---
*{generation_date}*
"""
        }
    
    def _load_severity_guidelines(self) -> Dict[str, Dict]:
        """Load severity-specific PIR guidelines."""
        return {
            "sev1": {
                "required_sections": ["executive_summary", "timeline", "rca", "action_items", "lessons_learned"],
                "required_attendees": ["incident_commander", "technical_leads", "engineering_manager", "product_manager"],
                "timeline_requirement": "Complete timeline with 15-minute intervals",
                "rca_methods": ["five_whys", "fishbone", "timeline"],
                "review_deadline_hours": 24,
                "follow_up_weeks": 4
            },
            "sev2": {
                "required_sections": ["summary", "timeline", "rca", "action_items"],
                "required_attendees": ["incident_commander", "technical_leads", "team_lead"],
                "timeline_requirement": "Key milestone timeline",
                "rca_methods": ["five_whys", "timeline"],
                "review_deadline_hours": 72,
                "follow_up_weeks": 2
            },
            "sev3": {
                "required_sections": ["summary", "rca", "action_items"],
                "required_attendees": ["technical_lead", "team_member"],
                "timeline_requirement": "Basic timeline",
                "rca_methods": ["five_whys"],
                "review_deadline_hours": 168,  # 1 week
                "follow_up_weeks": 1
            },
            "sev4": {
                "required_sections": ["summary", "action_items"],
                "required_attendees": ["assigned_engineer"],
                "timeline_requirement": "Optional",
                "rca_methods": ["brief_analysis"],
                "review_deadline_hours": 336,  # 2 weeks
                "follow_up_weeks": 0
            }
        }
    
    def _load_action_item_types(self) -> Dict[str, Dict]:
        """Load action item categorization and templates."""
        return {
            "immediate_fix": {
                "priority": "P0",
                "timeline": "24-48 hours",
                "description": "Critical bugs or security issues that need immediate attention",
                "template": "Fix {issue_description} to prevent recurrence of {incident_type}",
                "owners": ["engineer", "team_lead"]
            },
            "process_improvement": {
                "priority": "P1",
                "timeline": "1-2 weeks",
                "description": "Process gaps or communication issues identified",
                "template": "Improve {process_area} to address {gap_description}",
                "owners": ["team_lead", "process_owner"]
            },
            "monitoring_alerting": {
                "priority": "P1",
                "timeline": "1 week",
                "description": "Missing monitoring or alerting capabilities",
                "template": "Implement {monitoring_type} for {system_component}",
                "owners": ["sre", "engineer"]
            },
            "documentation": {
                "priority": "P2",
                "timeline": "2-3 weeks", 
                "description": "Documentation gaps or runbook updates",
                "template": "Update {documentation_type} to include {missing_information}",
                "owners": ["technical_writer", "engineer"]
            },
            "training": {
                "priority": "P2",
                "timeline": "1 month",
                "description": "Training needs or knowledge gaps",
                "template": "Provide {training_type} training on {topic}",
                "owners": ["training_coordinator", "subject_matter_expert"]
            },
            "architectural": {
                "priority": "P1-P3",
                "timeline": "1-3 months",
                "description": "System design or architecture improvements",
                "template": "Redesign {system_component} to improve {quality_attribute}",
                "owners": ["architect", "engineering_manager"]
            },
            "tooling": {
                "priority": "P2",
                "timeline": "2-4 weeks",
                "description": "Tool improvements or new tool requirements",
                "template": "Implement {tool_type} to support {use_case}",
                "owners": ["devops", "engineer"]
            }
        }
    
    def _load_lessons_learned_categories(self) -> Dict[str, List[str]]:
        """Load categories for organizing lessons learned."""
        return {
            "detection_and_monitoring": [
                "Monitoring gaps identified",
                "Alert fatigue issues",
                "Detection timing improvements",
                "Observability enhancements"
            ],
            "response_and_escalation": [
                "Response time improvements",
                "Escalation path optimization",
                "Communication effectiveness",
                "Resource allocation lessons"
            ],
            "technical_systems": [
                "Architecture resilience",
                "Failure mode analysis",
                "Performance bottlenecks",
                "Dependency management"
            ],
            "process_and_procedures": [
                "Runbook effectiveness",
                "Change management gaps",
                "Review process improvements",
                "Documentation quality"
            ],
            "team_and_culture": [
                "Training needs identified",
                "Cross-team collaboration",
                "Knowledge sharing gaps",
                "Decision-making processes"
            ]
        }
    
    def generate_pir(self, incident_data: Dict[str, Any], timeline_data: Optional[Dict] = None,
                    rca_method: str = "five_whys", template_type: str = "comprehensive") -> Dict[str, Any]:
        """
        Generate a comprehensive PIR document from incident data.
        
        Args:
            incident_data: Core incident information
            timeline_data: Optional timeline reconstruction data
            rca_method: RCA framework to use
            template_type: PIR template type (comprehensive, standard, brief)
            
        Returns:
            Dictionary containing PIR document and metadata
        """
        # Extract incident information
        incident_info = self._extract_incident_info(incident_data)
        
        # Generate root cause analysis
        rca_results = self._perform_rca(incident_data, timeline_data, rca_method)
        
        # Generate lessons learned
        lessons_learned = self._generate_lessons_learned(incident_data, timeline_data, rca_results)
        
        # Generate action items
        action_items = self._generate_action_items(incident_data, rca_results, lessons_learned)
        
        # Create timeline section
        timeline_section = self._create_timeline_section(timeline_data, incident_info["severity"])
        
        # Generate document sections
        sections = self._generate_document_sections(
            incident_info, rca_results, lessons_learned, action_items, timeline_section
        )
        
        # Build final document
        template = self.pir_templates[template_type]
        pir_document = template.format(**sections)
        
        # Generate metadata
        metadata = self._generate_metadata(incident_info, rca_results, action_items)
        
        return {
            "pir_document": pir_document,
            "metadata": metadata,
            "incident_info": incident_info,
            "rca_results": rca_results,
            "lessons_learned": lessons_learned,
            "action_items": action_items,
            "generation_timestamp": datetime.now(timezone.utc).isoformat()
        }
    
    def _extract_incident_info(self, incident_data: Dict) -> Dict[str, Any]:
        """Extract and normalize incident information."""
        return {
            "incident_id": incident_data.get("incident_id", "INC-" + datetime.now().strftime("%Y%m%d-%H%M")),
            "title": incident_data.get("title", incident_data.get("description", "Incident")[:50]),
            "description": incident_data.get("description", "No description provided"),
            "severity": incident_data.get("severity", "unknown").lower(),
            "start_time": self._parse_timestamp(incident_data.get("start_time", incident_data.get("timestamp", ""))),
            "end_time": self._parse_timestamp(incident_data.get("end_time", "")),
            "duration": self._calculate_duration(incident_data),
            "affected_services": incident_data.get("affected_services", []),
            "customer_impact": incident_data.get("customer_impact", "Unknown impact"),
            "business_impact": incident_data.get("business_impact", "Unknown business impact"),
            "incident_commander": incident_data.get("incident_commander", "TBD"),
            "responders": incident_data.get("responders", []),
            "status": incident_data.get("status", "resolved")
        }
    
    def _parse_timestamp(self, timestamp_str: str) -> Optional[datetime]:
        """Parse timestamp string to datetime object."""
        if not timestamp_str:
            return None
        
        formats = [
            "%Y-%m-%dT%H:%M:%S.%fZ",
            "%Y-%m-%dT%H:%M:%SZ",
            "%Y-%m-%d %H:%M:%S",
            "%m/%d/%Y %H:%M:%S"
        ]
        
        for fmt in formats:
            try:
                dt = datetime.strptime(timestamp_str, fmt)
                if dt.tzinfo is None:
                    dt = dt.replace(tzinfo=timezone.utc)
                return dt
            except ValueError:
                continue
        
        return None
    
    def _calculate_duration(self, incident_data: Dict) -> str:
        """Calculate incident duration in human-readable format."""
        start_time = self._parse_timestamp(incident_data.get("start_time", ""))
        end_time = self._parse_timestamp(incident_data.get("end_time", ""))
        
        if start_time and end_time:
            duration = end_time - start_time
            total_minutes = int(duration.total_seconds() / 60)
            
            if total_minutes < 60:
                return f"{total_minutes} minutes"
            elif total_minutes < 1440:  # Less than 24 hours
                hours = total_minutes // 60
                minutes = total_minutes % 60
                return f"{hours}h {minutes}m"
            else:
                days = total_minutes // 1440
                hours = (total_minutes % 1440) // 60
                return f"{days}d {hours}h"
        
        return incident_data.get("duration", "Unknown duration")
    
    def _perform_rca(self, incident_data: Dict, timeline_data: Optional[Dict], method: str) -> Dict[str, Any]:
        """Perform root cause analysis using specified method."""
        if method == "five_whys":
            return self._five_whys_analysis(incident_data, timeline_data)
        elif method == "fishbone":
            return self._fishbone_analysis(incident_data, timeline_data)
        elif method == "timeline":
            return self._timeline_analysis(incident_data, timeline_data)
        elif method == "bow_tie":
            return self._bow_tie_analysis(incident_data, timeline_data)
        else:
            return self._five_whys_analysis(incident_data, timeline_data)  # Default
    
    def _five_whys_analysis(self, incident_data: Dict, timeline_data: Optional[Dict]) -> Dict[str, Any]:
        """Perform 5 Whys root cause analysis."""
        problem_statement = incident_data.get("description", "Incident occurred")
        
        # Generate why questions based on incident data
        whys = []
        current_issue = problem_statement
        
        # Generate systematic why questions
        why_patterns = [
            f"Why did {current_issue}?",
            "Why wasn't this detected earlier?",
            "Why didn't existing safeguards prevent this?",
            "Why wasn't there a backup mechanism?",
            "Why wasn't this scenario anticipated?"
        ]
        
        # Try to infer answers from incident data
        potential_answers = self._infer_why_answers(incident_data, timeline_data)
        
        for i, why_question in enumerate(why_patterns):
            answer = potential_answers[i] if i < len(potential_answers) else "Further investigation needed"
            whys.append({
                "question": why_question,
                "answer": answer,
                "evidence": self._find_supporting_evidence(answer, incident_data, timeline_data)
            })
        
        # Identify root causes from the analysis
        root_causes = self._extract_root_causes(whys)
        
        return {
            "method": "five_whys",
            "problem_statement": problem_statement,
            "why_analysis": whys,
            "root_causes": root_causes,
            "confidence": self._calculate_rca_confidence(whys, incident_data)
        }
    
    def _fishbone_analysis(self, incident_data: Dict, timeline_data: Optional[Dict]) -> Dict[str, Any]:
        """Perform Fishbone (Ishikawa) diagram analysis."""
        problem_statement = incident_data.get("description", "Incident occurred")
        
        # Analyze each category
        categories = {}
        for category_info in self.rca_frameworks["fishbone"]["categories"]:
            category_name = category_info["name"]
            contributing_factors = self._identify_category_factors(
                category_name, incident_data, timeline_data
            )
            categories[category_name] = {
                "description": category_info["description"],
                "factors": contributing_factors,
                "examples": category_info["examples"]
            }
        
        # Identify primary contributing factors
        primary_factors = self._identify_primary_factors(categories)
        
        # Generate root cause hypothesis
        root_causes = self._synthesize_fishbone_root_causes(categories, primary_factors)
        
        return {
            "method": "fishbone",
            "problem_statement": problem_statement,
            "categories": categories,
            "primary_factors": primary_factors,
            "root_causes": root_causes,
            "confidence": self._calculate_rca_confidence(categories, incident_data)
        }
    
    def _timeline_analysis(self, incident_data: Dict, timeline_data: Optional[Dict]) -> Dict[str, Any]:
        """Perform timeline-based root cause analysis."""
        if not timeline_data:
            return {"method": "timeline", "error": "No timeline data provided"}
        
        # Extract key decision points
        decision_points = self._extract_decision_points(timeline_data)
        
        # Identify missed opportunities
        missed_opportunities = self._identify_missed_opportunities(timeline_data)
        
        # Analyze response effectiveness
        response_analysis = self._analyze_response_effectiveness(timeline_data)
        
        # Generate timeline-based root causes
        root_causes = self._extract_timeline_root_causes(
            decision_points, missed_opportunities, response_analysis
        )
        
        return {
            "method": "timeline",
            "decision_points": decision_points,
            "missed_opportunities": missed_opportunities,
            "response_analysis": response_analysis,
            "root_causes": root_causes,
            "confidence": self._calculate_rca_confidence(timeline_data, incident_data)
        }
    
    def _bow_tie_analysis(self, incident_data: Dict, timeline_data: Optional[Dict]) -> Dict[str, Any]:
        """Perform Bow Tie analysis."""
        # Identify the top event (what went wrong)
        top_event = incident_data.get("description", "Service failure")
        
        # Identify threats (what caused it)
        threats = self._identify_threats(incident_data, timeline_data)
        
        # Identify consequences (impact)
        consequences = self._identify_consequences(incident_data)
        
        # Identify existing barriers
        existing_barriers = self._identify_existing_barriers(incident_data, timeline_data)
        
        # Recommend additional barriers
        recommended_barriers = self._recommend_additional_barriers(threats, consequences)
        
        return {
            "method": "bow_tie",
            "top_event": top_event,
            "threats": threats,
            "consequences": consequences,
            "existing_barriers": existing_barriers,
            "recommended_barriers": recommended_barriers,
            "confidence": self._calculate_rca_confidence(threats, incident_data)
        }
    
    def _infer_why_answers(self, incident_data: Dict, timeline_data: Optional[Dict]) -> List[str]:
        """Infer potential answers to why questions from available data."""
        answers = []
        
        # Look for clues in incident description
        description = incident_data.get("description", "").lower()
        
        # Common patterns and their inferred answers
        if "database" in description and ("timeout" in description or "slow" in description):
            answers.append("Database connection pool was exhausted")
            answers.append("Connection pool configuration was insufficient for peak load")
            answers.append("Load testing didn't include realistic database scenarios")
        elif "deployment" in description or "release" in description:
            answers.append("New deployment introduced a regression")
            answers.append("Code review process missed the issue")
            answers.append("Testing environment didn't match production")
        elif "network" in description or "connectivity" in description:
            answers.append("Network infrastructure had unexpected load")
            answers.append("Network monitoring wasn't comprehensive enough")
            answers.append("Redundancy mechanisms failed simultaneously")
        else:
            # Generic answers based on common root causes
            answers.extend([
                "System couldn't handle the load/request volume",
                "Monitoring didn't detect the issue early enough",
                "Error handling mechanisms were insufficient",
                "Dependencies failed without proper circuit breakers",
                "System lacked sufficient redundancy/resilience"
            ])
        
        return answers[:5]  # Return up to 5 answers
    
    def _find_supporting_evidence(self, answer: str, incident_data: Dict, timeline_data: Optional[Dict]) -> List[str]:
        """Find supporting evidence for RCA answers."""
        evidence = []
        
        # Look for supporting information in incident data
        if timeline_data and "timeline" in timeline_data:
            events = timeline_data["timeline"].get("events", [])
            for event in events:
                event_message = event.get("message", "").lower()
                if any(keyword in event_message for keyword in answer.lower().split()):
                    evidence.append(f"Timeline event: {event['message']}")
        
        # Check incident metadata for supporting info
        metadata = incident_data.get("metadata", {})
        for key, value in metadata.items():
            if isinstance(value, str) and any(keyword in value.lower() for keyword in answer.lower().split()):
                evidence.append(f"Incident metadata: {key} = {value}")
        
        return evidence[:3]  # Return top 3 pieces of evidence
    
    def _extract_root_causes(self, whys: List[Dict]) -> List[Dict]:
        """Extract root causes from 5 Whys analysis."""
        root_causes = []
        
        # The deepest "why" answers are typically closest to root causes
        if len(whys) >= 3:
            for i, why in enumerate(whys[-2:]):  # Look at last 2 whys
                if "further investigation needed" not in why["answer"].lower():
                    root_causes.append({
                        "cause": why["answer"],
                        "category": self._categorize_root_cause(why["answer"]),
                        "evidence": why["evidence"],
                        "confidence": "high" if len(why["evidence"]) > 1 else "medium"
                    })
        
        return root_causes
    
    def _categorize_root_cause(self, cause: str) -> str:
        """Categorize a root cause into standard categories."""
        cause_lower = cause.lower()
        
        if any(keyword in cause_lower for keyword in ["process", "procedure", "review", "change management"]):
            return "Process"
        elif any(keyword in cause_lower for keyword in ["training", "knowledge", "skill", "experience"]):
            return "People"
        elif any(keyword in cause_lower for keyword in ["system", "architecture", "code", "configuration"]):
            return "Technology"
        elif any(keyword in cause_lower for keyword in ["network", "infrastructure", "dependency", "third-party"]):
            return "Environment"
        else:
            return "Unknown"
    
    def _identify_category_factors(self, category: str, incident_data: Dict, timeline_data: Optional[Dict]) -> List[Dict]:
        """Identify contributing factors for a Fishbone category."""
        factors = []
        description = incident_data.get("description", "").lower()
        
        if category == "People":
            if "misconfigured" in description or "human error" in description:
                factors.append({"factor": "Configuration error", "likelihood": "high"})
            if timeline_data and self._has_delayed_response(timeline_data):
                factors.append({"factor": "Delayed incident response", "likelihood": "medium"})
            
        elif category == "Process":
            if "deployment" in description:
                factors.append({"factor": "Insufficient deployment validation", "likelihood": "high"})
            if "code review" in incident_data.get("context", "").lower():
                factors.append({"factor": "Code review process gaps", "likelihood": "medium"})
            
        elif category == "Technology":
            if "database" in description:
                factors.append({"factor": "Database performance limitations", "likelihood": "high"})
            if "timeout" in description or "latency" in description:
                factors.append({"factor": "System performance bottlenecks", "likelihood": "high"})
            
        elif category == "Environment":
            if "network" in description:
                factors.append({"factor": "Network infrastructure issues", "likelihood": "medium"})
            if "third-party" in description or "external" in description:
                factors.append({"factor": "External service dependencies", "likelihood": "medium"})
        
        return factors
    
    def _identify_primary_factors(self, categories: Dict) -> List[Dict]:
        """Identify primary contributing factors across all categories."""
        primary_factors = []
        
        for category_name, category_data in categories.items():
            high_likelihood_factors = [
                f for f in category_data["factors"] 
                if f.get("likelihood") == "high"
            ]
            primary_factors.extend([
                {**factor, "category": category_name} 
                for factor in high_likelihood_factors
            ])
        
        return primary_factors
    
    def _synthesize_fishbone_root_causes(self, categories: Dict, primary_factors: List[Dict]) -> List[Dict]:
        """Synthesize root causes from Fishbone analysis."""
        root_causes = []
        
        # Group primary factors by category
        category_factors = defaultdict(list)
        for factor in primary_factors:
            category_factors[factor["category"]].append(factor)
        
        # Create root causes from categories with multiple factors
        for category, factors in category_factors.items():
            if len(factors) > 1:
                root_causes.append({
                    "cause": f"Multiple {category.lower()} issues contributed to the incident",
                    "category": category,
                    "contributing_factors": [f["factor"] for f in factors],
                    "confidence": "high"
                })
            elif len(factors) == 1:
                root_causes.append({
                    "cause": factors[0]["factor"],
                    "category": category,
                    "confidence": "medium"
                })
        
        return root_causes
    
    def _has_delayed_response(self, timeline_data: Dict) -> bool:
        """Check if timeline shows delayed response patterns."""
        if not timeline_data or "gap_analysis" not in timeline_data:
            return False
        
        gaps = timeline_data["gap_analysis"].get("gaps", [])
        return any(gap.get("type") == "phase_transition" for gap in gaps)
    
    def _extract_decision_points(self, timeline_data: Dict) -> List[Dict]:
        """Extract key decision points from timeline."""
        decision_points = []
        
        if "timeline" in timeline_data and "phases" in timeline_data["timeline"]:
            phases = timeline_data["timeline"]["phases"]
            
            for i, phase in enumerate(phases):
                if phase["name"] in ["escalation", "mitigation"]:
                    decision_points.append({
                        "timestamp": phase["start_time"],
                        "decision": f"Initiated {phase['name']} phase",
                        "phase": phase["name"],
                        "duration": phase["duration_minutes"]
                    })
        
        return decision_points
    
    def _identify_missed_opportunities(self, timeline_data: Dict) -> List[Dict]:
        """Identify missed opportunities from gap analysis."""
        missed_opportunities = []
        
        if "gap_analysis" in timeline_data:
            gaps = timeline_data["gap_analysis"].get("gaps", [])
            
            for gap in gaps:
                if gap.get("severity") == "critical":
                    missed_opportunities.append({
                        "opportunity": f"Earlier {gap['type'].replace('_', ' ')}",
                        "gap_minutes": gap["gap_minutes"],
                        "potential_impact": "Could have reduced incident duration"
                    })
        
        return missed_opportunities
    
    def _analyze_response_effectiveness(self, timeline_data: Dict) -> Dict[str, Any]:
        """Analyze the effectiveness of incident response."""
        effectiveness = {
            "overall_rating": "unknown",
            "strengths": [],
            "weaknesses": [],
            "metrics": {}
        }
        
        if "metrics" in timeline_data:
            metrics = timeline_data["metrics"]
            duration_metrics = metrics.get("duration_metrics", {})
            
            # Analyze response times
            time_to_mitigation = duration_metrics.get("time_to_mitigation_minutes", 0)
            time_to_resolution = duration_metrics.get("time_to_resolution_minutes", 0)
            
            if time_to_mitigation <= 30:
                effectiveness["strengths"].append("Quick mitigation response")
            else:
                effectiveness["weaknesses"].append("Slow mitigation response")
            
            if time_to_resolution <= 120:
                effectiveness["strengths"].append("Fast resolution")
            else:
                effectiveness["weaknesses"].append("Extended resolution time")
            
            effectiveness["metrics"] = {
                "time_to_mitigation": time_to_mitigation,
                "time_to_resolution": time_to_resolution
            }
        
        # Overall rating based on strengths vs weaknesses
        if len(effectiveness["strengths"]) > len(effectiveness["weaknesses"]):
            effectiveness["overall_rating"] = "effective"
        elif len(effectiveness["weaknesses"]) > len(effectiveness["strengths"]):
            effectiveness["overall_rating"] = "needs_improvement"
        else:
            effectiveness["overall_rating"] = "mixed"
        
        return effectiveness
    
    def _extract_timeline_root_causes(self, decision_points: List, missed_opportunities: List, 
                                    response_analysis: Dict) -> List[Dict]:
        """Extract root causes from timeline analysis."""
        root_causes = []
        
        # Root causes from missed opportunities
        for opportunity in missed_opportunities:
            if opportunity["gap_minutes"] > 60:  # Significant gaps
                root_causes.append({
                    "cause": f"Delayed response: {opportunity['opportunity']}",
                    "category": "Process",
                    "evidence": f"{opportunity['gap_minutes']} minute gap identified",
                    "confidence": "high"
                })
        
        # Root causes from response effectiveness
        for weakness in response_analysis.get("weaknesses", []):
            root_causes.append({
                "cause": weakness,
                "category": "Process",
                "evidence": "Timeline analysis",
                "confidence": "medium"
            })
        
        return root_causes
    
    def _identify_threats(self, incident_data: Dict, timeline_data: Optional[Dict]) -> List[Dict]:
        """Identify threats for Bow Tie analysis."""
        threats = []
        description = incident_data.get("description", "").lower()
        
        if "deployment" in description:
            threats.append({"threat": "Defective code deployment", "likelihood": "medium"})
        if "load" in description or "traffic" in description:
            threats.append({"threat": "Unexpected load increase", "likelihood": "high"})
        if "database" in description:
            threats.append({"threat": "Database performance degradation", "likelihood": "medium"})
        
        return threats
    
    def _identify_consequences(self, incident_data: Dict) -> List[Dict]:
        """Identify consequences for Bow Tie analysis."""
        consequences = []
        
        customer_impact = incident_data.get("customer_impact", "").lower()
        business_impact = incident_data.get("business_impact", "").lower()
        
        if "all users" in customer_impact or "complete outage" in customer_impact:
            consequences.append({"consequence": "Complete service unavailability", "severity": "critical"})
        
        if "revenue" in business_impact:
            consequences.append({"consequence": "Revenue loss", "severity": "high"})
        
        return consequences
    
    def _identify_existing_barriers(self, incident_data: Dict, timeline_data: Optional[Dict]) -> List[Dict]:
        """Identify existing preventive/protective barriers."""
        barriers = []
        
        # Look for evidence of existing controls
        if timeline_data and "timeline" in timeline_data:
            events = timeline_data["timeline"].get("events", [])
            
            for event in events:
                message = event.get("message", "").lower()
                if "alert" in message or "monitoring" in message:
                    barriers.append({
                        "barrier": "Monitoring and alerting system",
                        "type": "detective",
                        "effectiveness": "partial"
                    })
                elif "rollback" in message:
                    barriers.append({
                        "barrier": "Rollback capability", 
                        "type": "corrective",
                        "effectiveness": "effective"
                    })
        
        return barriers
    
    def _recommend_additional_barriers(self, threats: List[Dict], consequences: List[Dict]) -> List[Dict]:
        """Recommend additional barriers based on threats and consequences."""
        recommendations = []
        
        for threat in threats:
            if "deployment" in threat["threat"].lower():
                recommendations.append({
                    "barrier": "Enhanced pre-deployment testing",
                    "type": "preventive",
                    "justification": "Prevent defective deployments reaching production"
                })
            elif "load" in threat["threat"].lower():
                recommendations.append({
                    "barrier": "Auto-scaling and load shedding",
                    "type": "preventive",
                    "justification": "Handle unexpected load increases automatically"
                })
        
        return recommendations
    
    def _calculate_rca_confidence(self, analysis_data: Any, incident_data: Dict) -> str:
        """Calculate confidence level for RCA results."""
        # Simple heuristic based on available data
        confidence_score = 0
        
        # More detailed incident data increases confidence
        if incident_data.get("description") and len(incident_data["description"]) > 50:
            confidence_score += 1
        
        if incident_data.get("timeline") or incident_data.get("events"):
            confidence_score += 2
        
        if incident_data.get("logs") or incident_data.get("monitoring_data"):
            confidence_score += 2
        
        # Analysis data completeness
        if isinstance(analysis_data, list) and len(analysis_data) > 3:
            confidence_score += 1
        elif isinstance(analysis_data, dict) and len(analysis_data) > 5:
            confidence_score += 1
        
        if confidence_score >= 4:
            return "high"
        elif confidence_score >= 2:
            return "medium"
        else:
            return "low"
    
    def _generate_lessons_learned(self, incident_data: Dict, timeline_data: Optional[Dict], 
                                rca_results: Dict) -> Dict[str, List[str]]:
        """Generate categorized lessons learned."""
        lessons = defaultdict(list)
        
        # Lessons from RCA
        root_causes = rca_results.get("root_causes", [])
        for root_cause in root_causes:
            category = root_cause.get("category", "technical_systems").lower()
            category_key = self._map_to_lessons_category(category)
            
            lesson = f"Identified: {root_cause['cause']}"
            lessons[category_key].append(lesson)
        
        # Lessons from timeline analysis
        if timeline_data and "gap_analysis" in timeline_data:
            gaps = timeline_data["gap_analysis"].get("gaps", [])
            for gap in gaps:
                if gap.get("severity") == "critical":
                    lessons["response_and_escalation"].append(
                        f"Response time gap: {gap['type'].replace('_', ' ')} took {gap['gap_minutes']} minutes"
                    )
        
        # Generic lessons based on incident characteristics
        severity = incident_data.get("severity", "").lower()
        if severity in ["sev1", "critical"]:
            lessons["detection_and_monitoring"].append(
                "Critical incidents require immediate detection and alerting"
            )
        
        return dict(lessons)
    
    def _map_to_lessons_category(self, category: str) -> str:
        """Map RCA category to lessons learned category."""
        mapping = {
            "people": "team_and_culture",
            "process": "process_and_procedures", 
            "technology": "technical_systems",
            "environment": "technical_systems",
            "unknown": "process_and_procedures"
        }
        return mapping.get(category, "technical_systems")
    
    def _generate_action_items(self, incident_data: Dict, rca_results: Dict, 
                             lessons_learned: Dict) -> List[Dict]:
        """Generate actionable follow-up items."""
        action_items = []
        
        # Actions from root causes
        root_causes = rca_results.get("root_causes", [])
        for root_cause in root_causes:
            action_type = self._determine_action_type(root_cause)
            action_template = self.action_item_types[action_type]
            
            action_items.append({
                "title": f"Address: {root_cause['cause'][:50]}...",
                "description": root_cause["cause"],
                "type": action_type,
                "priority": action_template["priority"],
                "timeline": action_template["timeline"],
                "owner": "TBD",
                "success_criteria": f"Prevent recurrence of {root_cause['cause'][:30]}...",
                "related_root_cause": root_cause
            })
        
        # Actions from lessons learned
        for category, lessons in lessons_learned.items():
            if len(lessons) > 1:  # Multiple lessons in same category indicate systematic issue
                action_items.append({
                    "title": f"Improve {category.replace('_', ' ')}",
                    "description": f"Address multiple issues identified in {category}",
                    "type": "process_improvement",
                    "priority": "P1",
                    "timeline": "2-3 weeks",
                    "owner": "TBD",
                    "success_criteria": f"Comprehensive review and improvement of {category}"
                })
        
        # Standard actions based on severity
        severity = incident_data.get("severity", "").lower()
        if severity in ["sev1", "critical"]:
            action_items.append({
                "title": "Conduct comprehensive post-incident review",
                "description": "Schedule PIR meeting with all stakeholders",
                "type": "process_improvement",
                "priority": "P0",
                "timeline": "24-48 hours",
                "owner": incident_data.get("incident_commander", "TBD"),
                "success_criteria": "PIR completed and documented"
            })
        
        return action_items
    
    def _determine_action_type(self, root_cause: Dict) -> str:
        """Determine action item type based on root cause."""
        cause_text = root_cause.get("cause", "").lower()
        category = root_cause.get("category", "").lower()
        
        if any(keyword in cause_text for keyword in ["bug", "error", "failure", "crash"]):
            return "immediate_fix"
        elif any(keyword in cause_text for keyword in ["monitor", "alert", "detect"]):
            return "monitoring_alerting"
        elif any(keyword in cause_text for keyword in ["process", "procedure", "review"]):
            return "process_improvement"
        elif any(keyword in cause_text for keyword in ["document", "runbook", "knowledge"]):
            return "documentation"
        elif any(keyword in cause_text for keyword in ["training", "skill", "knowledge"]):
            return "training"
        elif any(keyword in cause_text for keyword in ["architecture", "design", "system"]):
            return "architectural"
        else:
            return "process_improvement"  # Default
    
    def _create_timeline_section(self, timeline_data: Optional[Dict], severity: str) -> str:
        """Create timeline section for PIR document."""
        if not timeline_data:
            return "No detailed timeline available."
        
        timeline_content = []
        
        if "timeline" in timeline_data and "phases" in timeline_data["timeline"]:
            timeline_content.append("### Phase Timeline")
            timeline_content.append("")
            
            phases = timeline_data["timeline"]["phases"]
            for phase in phases:
                timeline_content.append(f"**{phase['name'].title()} Phase**")
                timeline_content.append(f"- Start: {phase['start_time']}")
                timeline_content.append(f"- Duration: {phase['duration_minutes']} minutes")
                timeline_content.append(f"- Events: {phase['event_count']}")
                timeline_content.append("")
        
        if "metrics" in timeline_data:
            metrics = timeline_data["metrics"]
            duration_metrics = metrics.get("duration_metrics", {})
            
            timeline_content.append("### Key Metrics")
            timeline_content.append("")
            timeline_content.append(f"- Total Duration: {duration_metrics.get('total_duration_minutes', 'N/A')} minutes")
            timeline_content.append(f"- Time to Mitigation: {duration_metrics.get('time_to_mitigation_minutes', 'N/A')} minutes")
            timeline_content.append(f"- Time to Resolution: {duration_metrics.get('time_to_resolution_minutes', 'N/A')} minutes")
            timeline_content.append("")
        
        return "\n".join(timeline_content)
    
    def _generate_document_sections(self, incident_info: Dict, rca_results: Dict, 
                                  lessons_learned: Dict, action_items: List[Dict], 
                                  timeline_section: str) -> Dict[str, str]:
        """Generate all document sections for PIR template."""
        sections = {}
        
        # Basic information
        sections["incident_title"] = incident_info["title"]
        sections["incident_id"] = incident_info["incident_id"]
        sections["incident_date"] = incident_info["start_time"].strftime("%Y-%m-%d %H:%M:%S UTC") if incident_info["start_time"] else "Unknown"
        sections["duration"] = incident_info["duration"]
        sections["severity"] = incident_info["severity"].upper()
        sections["status"] = incident_info["status"].title()
        sections["incident_commander"] = incident_info["incident_commander"]
        sections["responders"] = ", ".join(incident_info["responders"]) if incident_info["responders"] else "TBD"
        sections["generation_date"] = datetime.now().strftime("%Y-%m-%d")
        
        # Impact sections
        sections["customer_impact"] = incident_info["customer_impact"]
        sections["business_impact"] = incident_info["business_impact"]
        
        # Executive summary
        sections["executive_summary"] = self._create_executive_summary(incident_info, rca_results)
        
        # Timeline
        sections["timeline_section"] = timeline_section
        
        # RCA section
        sections["rca_section"] = self._create_rca_section(rca_results)
        
        # What went well/wrong
        sections["what_went_well"] = self._create_what_went_well_section(incident_info, rca_results)
        sections["what_went_wrong"] = self._create_what_went_wrong_section(rca_results, lessons_learned)
        
        # Lessons learned
        sections["lessons_learned"] = self._create_lessons_learned_section(lessons_learned)
        
        # Action items
        sections["action_items"] = self._create_action_items_section(action_items)
        
        # Prevention and appendix
        sections["prevention_measures"] = self._create_prevention_section(rca_results, action_items)
        sections["appendix_section"] = self._create_appendix_section(incident_info)
        
        return sections
    
    def _create_executive_summary(self, incident_info: Dict, rca_results: Dict) -> str:
        """Create executive summary section."""
        summary_parts = []
        
        # Incident description
        summary_parts.append(f"On {incident_info['start_time'].strftime('%B %d, %Y') if incident_info['start_time'] else 'an unknown date'}, we experienced a {incident_info['severity']} incident affecting {incident_info.get('affected_services', ['our services'])}.")
        
        # Duration and impact
        summary_parts.append(f"The incident lasted {incident_info['duration']} and had the following impact: {incident_info['customer_impact']}")
        
        # Root cause summary
        root_causes = rca_results.get("root_causes", [])
        if root_causes:
            primary_cause = root_causes[0]["cause"]
            summary_parts.append(f"Root cause analysis identified the primary issue as: {primary_cause}")
        
        # Resolution
        summary_parts.append(f"The incident has been {incident_info['status']} and we have identified specific actions to prevent recurrence.")
        
        return " ".join(summary_parts)
    
    def _create_rca_section(self, rca_results: Dict) -> str:
        """Create RCA section content."""
        rca_content = []
        
        method = rca_results.get("method", "unknown")
        rca_content.append(f"### Analysis Method: {self.rca_frameworks.get(method, {}).get('name', method)}")
        rca_content.append("")
        
        if method == "five_whys" and "why_analysis" in rca_results:
            rca_content.append("#### Why Analysis")
            rca_content.append("")
            
            for i, why in enumerate(rca_results["why_analysis"], 1):
                rca_content.append(f"**Why {i}:** {why['question']}")
                rca_content.append(f"**Answer:** {why['answer']}")
                if why["evidence"]:
                    rca_content.append(f"**Evidence:** {', '.join(why['evidence'])}")
                rca_content.append("")
        
        elif method == "fishbone" and "categories" in rca_results:
            rca_content.append("#### Contributing Factor Analysis")
            rca_content.append("")
            
            for category, data in rca_results["categories"].items():
                if data["factors"]:
                    rca_content.append(f"**{category}:**")
                    for factor in data["factors"]:
                        rca_content.append(f"- {factor['factor']} (likelihood: {factor.get('likelihood', 'unknown')})")
                    rca_content.append("")
        
        # Root causes summary
        root_causes = rca_results.get("root_causes", [])
        if root_causes:
            rca_content.append("#### Identified Root Causes")
            rca_content.append("")
            
            for i, cause in enumerate(root_causes, 1):
                rca_content.append(f"{i}. **{cause['cause']}**")
                rca_content.append(f"   - Category: {cause.get('category', 'Unknown')}")
                rca_content.append(f"   - Confidence: {cause.get('confidence', 'Unknown')}")
                if cause.get("evidence"):
                    rca_content.append(f"   - Evidence: {cause['evidence']}")
                rca_content.append("")
        
        return "\n".join(rca_content)
    
    def _create_what_went_well_section(self, incident_info: Dict, rca_results: Dict) -> str:
        """Create what went well section."""
        positives = []
        
        # Generic positive aspects
        if incident_info["status"] == "resolved":
            positives.append("The incident was successfully resolved")
        
        if incident_info["incident_commander"] != "TBD":
            positives.append("Incident command was established")
        
        if len(incident_info.get("responders", [])) > 1:
            positives.append("Multiple team members collaborated on resolution")
        
        # Analysis-specific positives
        if rca_results.get("confidence") == "high":
            positives.append("Root cause analysis provided clear insights")
        
        if not positives:
            positives.append("Incident response process was followed")
        
        return "\n".join([f"- {positive}" for positive in positives])
    
    def _create_what_went_wrong_section(self, rca_results: Dict, lessons_learned: Dict) -> str:
        """Create what went wrong section."""
        issues = []
        
        # Issues from RCA
        root_causes = rca_results.get("root_causes", [])
        for cause in root_causes[:3]:  # Show top 3
            issues.append(cause["cause"])
        
        # Issues from lessons learned
        for category, lessons in lessons_learned.items():
            if lessons:
                issues.append(f"{category.replace('_', ' ').title()}: {lessons[0]}")
        
        if not issues:
            issues.append("Analysis in progress")
        
        return "\n".join([f"- {issue}" for issue in issues])
    
    def _create_lessons_learned_section(self, lessons_learned: Dict) -> str:
        """Create lessons learned section."""
        content = []
        
        for category, lessons in lessons_learned.items():
            if lessons:
                content.append(f"### {category.replace('_', ' ').title()}")
                content.append("")
                
                for lesson in lessons:
                    content.append(f"- {lesson}")
                
                content.append("")
        
        if not content:
            content.append("Lessons learned to be documented following detailed analysis.")
        
        return "\n".join(content)
    
    def _create_action_items_section(self, action_items: List[Dict]) -> str:
        """Create action items section."""
        if not action_items:
            return "Action items to be defined."
        
        content = []
        
        # Group by priority
        priority_groups = defaultdict(list)
        for item in action_items:
            priority_groups[item.get("priority", "P3")].append(item)
        
        for priority in ["P0", "P1", "P2", "P3"]:
            items = priority_groups.get(priority, [])
            if items:
                content.append(f"### {priority} - {self._get_priority_description(priority)}")
                content.append("")
                
                for item in items:
                    content.append(f"**{item['title']}**")
                    content.append(f"- Owner: {item.get('owner', 'TBD')}")
                    content.append(f"- Timeline: {item.get('timeline', 'TBD')}")
                    content.append(f"- Success Criteria: {item.get('success_criteria', 'TBD')}")
                    content.append("")
        
        return "\n".join(content)
    
    def _get_priority_description(self, priority: str) -> str:
        """Get human-readable priority description."""
        descriptions = {
            "P0": "Critical - Immediate Action Required",
            "P1": "High Priority - Complete Within 1-2 Weeks", 
            "P2": "Medium Priority - Complete Within 1 Month",
            "P3": "Low Priority - Complete When Capacity Allows"
        }
        return descriptions.get(priority, "Unknown Priority")
    
    def _create_prevention_section(self, rca_results: Dict, action_items: List[Dict]) -> str:
        """Create prevention and follow-up section."""
        content = []
        
        content.append("### Prevention Measures")
        content.append("")
        content.append("Based on the root cause analysis, the following preventive measures have been identified:")
        content.append("")
        
        # Extract prevention-focused action items
        prevention_items = [item for item in action_items if "prevent" in item.get("description", "").lower()]
        
        if prevention_items:
            for item in prevention_items:
                content.append(f"- {item['title']}: {item.get('description', '')}")
        else:
            content.append("- Implement comprehensive testing for similar scenarios")
            content.append("- Improve monitoring and alerting coverage")  
            content.append("- Enhance error handling and resilience patterns")
        
        content.append("")
        content.append("### Follow-up Schedule")
        content.append("")
        content.append("- 1 week: Review action item progress")
        content.append("- 1 month: Evaluate effectiveness of implemented changes")
        content.append("- 3 months: Conduct follow-up assessment and update preventive measures")
        
        return "\n".join(content)
    
    def _create_appendix_section(self, incident_info: Dict) -> str:
        """Create appendix section."""
        content = []
        
        content.append("### Additional Information")
        content.append("")
        content.append(f"- Incident ID: {incident_info['incident_id']}")
        content.append(f"- Severity Classification: {incident_info['severity']}")
        
        if incident_info.get("affected_services"):
            content.append(f"- Affected Services: {', '.join(incident_info['affected_services'])}")
        
        content.append("")
        content.append("### References")
        content.append("")
        content.append("- Incident tracking ticket: [Link TBD]")
        content.append("- Monitoring dashboards: [Link TBD]")
        content.append("- Communication thread: [Link TBD]")
        
        return "\n".join(content)
    
    def _generate_metadata(self, incident_info: Dict, rca_results: Dict, action_items: List[Dict]) -> Dict[str, Any]:
        """Generate PIR metadata for tracking and analysis."""
        return {
            "pir_id": f"PIR-{incident_info['incident_id']}",
            "incident_severity": incident_info["severity"],
            "rca_method": rca_results.get("method", "unknown"),
            "rca_confidence": rca_results.get("confidence", "unknown"),
            "total_action_items": len(action_items),
            "critical_action_items": len([item for item in action_items if item.get("priority") == "P0"]),
            "estimated_prevention_timeline": self._estimate_prevention_timeline(action_items),
            "categories_affected": list(set(item.get("type", "unknown") for item in action_items)),
            "review_completeness": self._assess_review_completeness(incident_info, rca_results, action_items)
        }
    
    def _estimate_prevention_timeline(self, action_items: List[Dict]) -> str:
        """Estimate timeline for implementing all prevention measures."""
        if not action_items:
            return "unknown"
        
        # Find the longest timeline among action items
        max_weeks = 0
        for item in action_items:
            timeline = item.get("timeline", "")
            if "week" in timeline:
                try:
                    weeks = int(re.findall(r'\d+', timeline)[0])
                    max_weeks = max(max_weeks, weeks)
                except (IndexError, ValueError):
                    pass
            elif "month" in timeline:
                try:
                    months = int(re.findall(r'\d+', timeline)[0])
                    max_weeks = max(max_weeks, months * 4)
                except (IndexError, ValueError):
                    pass
        
        if max_weeks == 0:
            return "1-2 weeks"
        elif max_weeks <= 4:
            return f"{max_weeks} weeks"
        else:
            return f"{max_weeks // 4} months"
    
    def _assess_review_completeness(self, incident_info: Dict, rca_results: Dict, action_items: List[Dict]) -> float:
        """Assess completeness of the PIR (0-1 score)."""
        score = 0.0
        
        # Basic information completeness
        if incident_info.get("description"):
            score += 0.1
        if incident_info.get("start_time"):
            score += 0.1
        if incident_info.get("customer_impact"):
            score += 0.1
        
        # RCA completeness
        if rca_results.get("root_causes"):
            score += 0.2
        if rca_results.get("confidence") in ["medium", "high"]:
            score += 0.1
        
        # Action items completeness
        if action_items:
            score += 0.2
        if any(item.get("owner") and item["owner"] != "TBD" for item in action_items):
            score += 0.1
        
        # Additional factors
        if incident_info.get("incident_commander") != "TBD":
            score += 0.1
        if len(action_items) >= 3:  # Multiple action items show thorough analysis
            score += 0.1
        
        return min(score, 1.0)


def format_json_output(result: Dict) -> str:
    """Format result as pretty JSON."""
    return json.dumps(result, indent=2, ensure_ascii=False)


def format_markdown_output(result: Dict) -> str:
    """Format result as Markdown PIR document."""
    return result.get("pir_document", "Error: No PIR document generated")


def format_text_output(result: Dict) -> str:
    """Format result as human-readable summary."""
    if "error" in result:
        return f"Error: {result['error']}"
    
    metadata = result.get("metadata", {})
    incident_info = result.get("incident_info", {})
    rca_results = result.get("rca_results", {})
    action_items = result.get("action_items", [])
    
    output = []
    output.append("=" * 60)
    output.append("POST-INCIDENT REVIEW SUMMARY")  
    output.append("=" * 60)
    output.append("")
    
    # Basic info
    output.append("INCIDENT INFORMATION:")
    output.append(f"  PIR ID: {metadata.get('pir_id', 'Unknown')}")
    output.append(f"  Severity: {incident_info.get('severity', 'Unknown').upper()}")
    output.append(f"  Duration: {incident_info.get('duration', 'Unknown')}")
    output.append(f"  Status: {incident_info.get('status', 'Unknown').title()}")
    output.append("")
    
    # RCA summary
    output.append("ROOT CAUSE ANALYSIS:")
    output.append(f"  Method: {rca_results.get('method', 'Unknown')}")
    output.append(f"  Confidence: {rca_results.get('confidence', 'Unknown').title()}")
    
    root_causes = rca_results.get("root_causes", [])
    if root_causes:
        output.append(f"  Root Causes Identified: {len(root_causes)}")
        for i, cause in enumerate(root_causes[:3], 1):
            output.append(f"    {i}. {cause.get('cause', 'Unknown')[:60]}...")
    output.append("")
    
    # Action items summary
    output.append("ACTION ITEMS:")
    output.append(f"  Total Actions: {len(action_items)}")
    output.append(f"  Critical (P0): {metadata.get('critical_action_items', 0)}")
    output.append(f"  Prevention Timeline: {metadata.get('estimated_prevention_timeline', 'Unknown')}")
    
    if action_items:
        output.append("  Top Actions:")
        for item in action_items[:3]:
            output.append(f"    - {item.get('title', 'Unknown')[:50]}...")
    output.append("")
    
    # Completeness
    completeness = metadata.get("review_completeness", 0) * 100
    output.append(f"REVIEW COMPLETENESS: {completeness:.0f}%")
    output.append("")
    
    output.append("=" * 60)
    
    return "\n".join(output)


def main():
    """Main function with argument parsing and execution."""
    parser = argparse.ArgumentParser(
        description="Generate Post-Incident Review documents with RCA and action items",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python pir_generator.py --incident incident.json --output pir.md
  python pir_generator.py --incident incident.json --rca-method fishbone
  cat incident.json | python pir_generator.py --format markdown
  
Incident JSON format:
  {
    "incident_id": "INC-2024-001",
    "title": "Database performance degradation",
    "description": "Users experiencing slow response times",
    "severity": "sev2",
    "start_time": "2024-01-01T12:00:00Z",
    "end_time": "2024-01-01T14:30:00Z",
    "customer_impact": "50% of users affected by slow page loads",
    "business_impact": "Moderate user experience degradation",
    "incident_commander": "Alice Smith",
    "responders": ["Bob Jones", "Carol Johnson"]
  }
        """
    )
    
    parser.add_argument(
        "--incident", "-i",
        help="Incident data file (JSON) or '-' for stdin"
    )
    
    parser.add_argument(
        "--timeline", "-t",
        help="Timeline reconstruction file (JSON)"
    )
    
    parser.add_argument(
        "--output", "-o",
        help="Output file path (default: stdout)"
    )
    
    parser.add_argument(
        "--format", "-f",
        choices=["json", "markdown", "text"],
        default="markdown",
        help="Output format (default: markdown)"
    )
    
    parser.add_argument(
        "--rca-method",
        choices=["five_whys", "fishbone", "timeline", "bow_tie"],
        default="five_whys",
        help="Root cause analysis method (default: five_whys)"
    )
    
    parser.add_argument(
        "--template-type",
        choices=["comprehensive", "standard", "brief"],
        default="comprehensive",
        help="PIR template type (default: comprehensive)"
    )
    
    parser.add_argument(
        "--action-items",
        action="store_true",
        help="Generate detailed action items"
    )
    
    args = parser.parse_args()
    
    generator = PIRGenerator()
    
    try:
        # Read incident data
        if args.incident == "-" or (not args.incident and not sys.stdin.isatty()):
            # Read from stdin
            input_text = sys.stdin.read().strip()
            if not input_text:
                parser.error("No incident data provided")
            incident_data = json.loads(input_text)
        elif args.incident:
            # Read from file
            with open(args.incident, 'r') as f:
                incident_data = json.load(f)
        else:
            parser.error("No incident data specified. Use --incident or pipe data to stdin.")
        
        # Read timeline data if provided
        timeline_data = None
        if args.timeline:
            with open(args.timeline, 'r') as f:
                timeline_data = json.load(f)
        
        # Validate incident data
        if not isinstance(incident_data, dict):
            parser.error("Incident data must be a JSON object")
        
        if not incident_data.get("description") and not incident_data.get("title"):
            parser.error("Incident data must contain 'description' or 'title'")
        
        # Generate PIR
        result = generator.generate_pir(
            incident_data=incident_data,
            timeline_data=timeline_data,
            rca_method=args.rca_method,
            template_type=args.template_type
        )
        
        # Format output
        if args.format == "json":
            output = format_json_output(result)
        elif args.format == "markdown":
            output = format_markdown_output(result)
        else:
            output = format_text_output(result)
        
        # Write output
        if args.output:
            with open(args.output, 'w') as f:
                f.write(output)
                f.write('\n')
        else:
            print(output)
    
    except FileNotFoundError as e:
        print(f"Error: File not found - {e}", file=sys.stderr)
        sys.exit(1)
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON - {e}", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()