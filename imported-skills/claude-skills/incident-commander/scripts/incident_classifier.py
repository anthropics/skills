#!/usr/bin/env python3
"""
Incident Classifier

Analyzes incident descriptions and outputs severity levels, recommended response teams,
initial actions, and communication templates.

This tool uses pattern matching and keyword analysis to classify incidents according to
SEV1-4 criteria and provide structured response guidance.

Usage:
    python incident_classifier.py --input incident.json
    echo "Database is down" | python incident_classifier.py --format text
    python incident_classifier.py --interactive
"""

import argparse
import json
import sys
import re
from datetime import datetime, timezone
from typing import Dict, List, Tuple, Optional, Any


class IncidentClassifier:
    """
    Classifies incidents based on description, impact metrics, and business context.
    Provides severity assessment, team recommendations, and response templates.
    """
    
    def __init__(self):
        """Initialize the classifier with rules and templates."""
        self.severity_rules = self._load_severity_rules()
        self.team_mappings = self._load_team_mappings()
        self.communication_templates = self._load_communication_templates()
        self.action_templates = self._load_action_templates()
    
    def _load_severity_rules(self) -> Dict[str, Dict]:
        """Load severity classification rules and keywords."""
        return {
            "sev1": {
                "keywords": [
                    "down", "outage", "offline", "unavailable", "crashed", "failed",
                    "critical", "emergency", "dead", "broken", "timeout", "500 error",
                    "data loss", "corrupted", "breach", "security incident",
                    "revenue impact", "customer facing", "all users", "complete failure"
                ],
                "impact_indicators": [
                    "100%", "all users", "entire service", "complete",
                    "revenue loss", "sla violation", "customer churn",
                    "security breach", "data corruption", "regulatory"
                ],
                "duration_threshold": 0,  # Immediate classification
                "response_time": 300,  # 5 minutes
                "description": "Complete service failure affecting all users or critical business functions"
            },
            "sev2": {
                "keywords": [
                    "degraded", "slow", "performance", "errors", "partial",
                    "intermittent", "high latency", "timeouts", "some users",
                    "feature broken", "api errors", "database slow"
                ],
                "impact_indicators": [
                    "50%", "25-75%", "many users", "significant",
                    "performance degradation", "feature unavailable",
                    "support tickets", "user complaints"
                ],
                "duration_threshold": 300,  # 5 minutes
                "response_time": 900,  # 15 minutes
                "description": "Significant degradation affecting subset of users or non-critical functions"
            },
            "sev3": {
                "keywords": [
                    "minor", "cosmetic", "single feature", "workaround available",
                    "edge case", "rare issue", "non-critical", "internal tool",
                    "logging issue", "monitoring gap"
                ],
                "impact_indicators": [
                    "<25%", "few users", "limited impact",
                    "workaround exists", "internal only",
                    "development environment"
                ],
                "duration_threshold": 3600,  # 1 hour
                "response_time": 7200,  # 2 hours
                "description": "Limited impact with workarounds available"
            },
            "sev4": {
                "keywords": [
                    "cosmetic", "documentation", "typo", "minor bug",
                    "enhancement", "nice to have", "low priority",
                    "test environment", "dev tools"
                ],
                "impact_indicators": [
                    "no impact", "cosmetic only", "documentation",
                    "development", "testing", "non-production"
                ],
                "duration_threshold": 86400,  # 24 hours
                "response_time": 172800,  # 2 days
                "description": "Minimal impact, cosmetic issues, or planned maintenance"
            }
        }
    
    def _load_team_mappings(self) -> Dict[str, List[str]]:
        """Load team assignment rules based on service/component keywords."""
        return {
            "database": ["Database Team", "SRE", "Backend Engineering"],
            "frontend": ["Frontend Team", "UX Engineering", "Product Engineering"],
            "api": ["API Team", "Backend Engineering", "Platform Team"],
            "infrastructure": ["SRE", "DevOps", "Platform Team"],
            "security": ["Security Team", "SRE", "Compliance Team"],
            "network": ["Network Engineering", "SRE", "Infrastructure Team"],
            "authentication": ["Identity Team", "Security Team", "Backend Engineering"],
            "payment": ["Payments Team", "Finance Engineering", "Compliance Team"],
            "mobile": ["Mobile Team", "API Team", "QA Engineering"],
            "monitoring": ["SRE", "Platform Team", "DevOps"],
            "deployment": ["DevOps", "Release Engineering", "SRE"],
            "data": ["Data Engineering", "Analytics Team", "Backend Engineering"]
        }
    
    def _load_communication_templates(self) -> Dict[str, Dict]:
        """Load communication templates for each severity level."""
        return {
            "sev1": {
                "subject": "🚨 [SEV1] {service} - {brief_description}",
                "body": """CRITICAL INCIDENT ALERT

Incident Details:
- Start Time: {timestamp}
- Severity: SEV1 - Critical Outage
- Service: {service}
- Impact: {impact_description}
- Current Status: Investigating

Customer Impact:
{customer_impact}

Response Team:
- Incident Commander: TBD (assigning now)
- Primary Responder: {primary_responder}
- SMEs Required: {subject_matter_experts}

Immediate Actions Taken:
{initial_actions}

War Room: {war_room_link}
Status Page: Will be updated within 15 minutes
Next Update: {next_update_time}

This is a customer-impacting incident requiring immediate attention.

{incident_commander_contact}"""
            },
            "sev2": {
                "subject": "⚠️ [SEV2] {service} - {brief_description}",
                "body": """MAJOR INCIDENT NOTIFICATION

Incident Details:
- Start Time: {timestamp}
- Severity: SEV2 - Major Impact
- Service: {service}
- Impact: {impact_description}
- Current Status: Investigating

User Impact:
{customer_impact}

Response Team:
- Primary Responder: {primary_responder}
- Supporting Team: {supporting_teams}
- Incident Commander: {incident_commander}

Initial Assessment:
{initial_assessment}

Next Steps:
{next_steps}

Updates will be provided every 30 minutes.
Status page: {status_page_link}

{contact_information}"""
            },
            "sev3": {
                "subject": "ℹ️ [SEV3] {service} - {brief_description}",
                "body": """MINOR INCIDENT NOTIFICATION

Incident Details:
- Start Time: {timestamp}
- Severity: SEV3 - Minor Impact
- Service: {service}
- Impact: {impact_description}
- Status: {current_status}

Details:
{incident_details}

Assigned Team: {assigned_team}
Estimated Resolution: {eta}

Workaround: {workaround}

This incident has limited customer impact and is being addressed during normal business hours.

{team_contact}"""
            },
            "sev4": {
                "subject": "[SEV4] {service} - {brief_description}",
                "body": """LOW PRIORITY ISSUE

Issue Details:
- Reported: {timestamp}
- Severity: SEV4 - Low Impact
- Component: {service}
- Description: {description}

This issue will be addressed in the normal development cycle.

Assigned to: {assigned_team}
Target Resolution: {target_date}

{standard_contact}"""
            }
        }
    
    def _load_action_templates(self) -> Dict[str, List[Dict]]:
        """Load initial action templates for each severity level."""
        return {
            "sev1": [
                {
                    "action": "Establish incident command",
                    "priority": 1,
                    "timeout_minutes": 5,
                    "description": "Page incident commander and establish war room"
                },
                {
                    "action": "Create incident ticket",
                    "priority": 1,
                    "timeout_minutes": 2,
                    "description": "Create tracking ticket with all known details"
                },
                {
                    "action": "Update status page",
                    "priority": 2,
                    "timeout_minutes": 15,
                    "description": "Post initial status page update acknowledging incident"
                },
                {
                    "action": "Notify executives",
                    "priority": 2,
                    "timeout_minutes": 15,
                    "description": "Alert executive team of customer-impacting outage"
                },
                {
                    "action": "Engage subject matter experts",
                    "priority": 3,
                    "timeout_minutes": 10,
                    "description": "Page relevant SMEs based on affected systems"
                },
                {
                    "action": "Begin technical investigation",
                    "priority": 3,
                    "timeout_minutes": 5,
                    "description": "Start technical diagnosis and mitigation efforts"
                }
            ],
            "sev2": [
                {
                    "action": "Assign incident commander",
                    "priority": 1,
                    "timeout_minutes": 30,
                    "description": "Assign IC and establish coordination channel"
                },
                {
                    "action": "Create incident tracking",
                    "priority": 1,
                    "timeout_minutes": 5,
                    "description": "Create incident ticket with details and timeline"
                },
                {
                    "action": "Assess customer impact",
                    "priority": 2,
                    "timeout_minutes": 15,
                    "description": "Determine scope and severity of user impact"
                },
                {
                    "action": "Engage response team",
                    "priority": 2,
                    "timeout_minutes": 30,
                    "description": "Page appropriate technical responders"
                },
                {
                    "action": "Begin investigation",
                    "priority": 3,
                    "timeout_minutes": 15,
                    "description": "Start technical analysis and debugging"
                },
                {
                    "action": "Plan status communication",
                    "priority": 3,
                    "timeout_minutes": 30,
                    "description": "Determine if status page update is needed"
                }
            ],
            "sev3": [
                {
                    "action": "Assign to appropriate team",
                    "priority": 1,
                    "timeout_minutes": 120,
                    "description": "Route to team with relevant expertise"
                },
                {
                    "action": "Create tracking ticket",
                    "priority": 1,
                    "timeout_minutes": 30,
                    "description": "Document issue in standard ticketing system"
                },
                {
                    "action": "Assess scope and impact",
                    "priority": 2,
                    "timeout_minutes": 60,
                    "description": "Understand full scope of the issue"
                },
                {
                    "action": "Identify workarounds",
                    "priority": 2,
                    "timeout_minutes": 60,
                    "description": "Find temporary solutions if possible"
                },
                {
                    "action": "Plan resolution approach",
                    "priority": 3,
                    "timeout_minutes": 120,
                    "description": "Develop plan for permanent fix"
                }
            ],
            "sev4": [
                {
                    "action": "Create backlog item",
                    "priority": 1,
                    "timeout_minutes": 1440,  # 24 hours
                    "description": "Add to team backlog for future sprint planning"
                },
                {
                    "action": "Triage and prioritize",
                    "priority": 2,
                    "timeout_minutes": 2880,  # 2 days
                    "description": "Review and prioritize against other work"
                },
                {
                    "action": "Assign owner",
                    "priority": 3,
                    "timeout_minutes": 4320,  # 3 days
                    "description": "Assign to appropriate developer when capacity allows"
                }
            ]
        }
    
    def classify_incident(self, incident_data: Dict[str, Any]) -> Dict[str, Any]:
        """
        Main classification method that analyzes incident data and returns
        comprehensive response recommendations.
        
        Args:
            incident_data: Dictionary containing incident information
            
        Returns:
            Dictionary with classification results and recommendations
        """
        # Extract key information from incident data
        description = incident_data.get('description', '').lower()
        affected_users = incident_data.get('affected_users', '0%')
        business_impact = incident_data.get('business_impact', 'unknown')
        service = incident_data.get('service', 'unknown service')
        duration = incident_data.get('duration_minutes', 0)
        
        # Classify severity
        severity = self._classify_severity(description, affected_users, business_impact, duration)
        
        # Determine response teams
        response_teams = self._determine_teams(description, service)
        
        # Generate initial actions
        initial_actions = self._generate_initial_actions(severity, incident_data)
        
        # Create communication template
        communication = self._generate_communication(severity, incident_data)
        
        # Calculate response timeline
        timeline = self._generate_timeline(severity)
        
        # Determine escalation path
        escalation = self._determine_escalation(severity, business_impact)
        
        return {
            "classification": {
                "severity": severity.upper(),
                "confidence": self._calculate_confidence(description, affected_users, business_impact),
                "reasoning": self._explain_classification(severity, description, affected_users),
                "timestamp": datetime.now(timezone.utc).isoformat()
            },
            "response": {
                "primary_team": response_teams[0] if response_teams else "General Engineering",
                "supporting_teams": response_teams[1:] if len(response_teams) > 1 else [],
                "all_teams": response_teams,
                "response_time_minutes": self.severity_rules[severity]["response_time"] // 60
            },
            "initial_actions": initial_actions,
            "communication": communication,
            "timeline": timeline,
            "escalation": escalation,
            "incident_data": {
                "service": service,
                "description": incident_data.get('description', ''),
                "affected_users": affected_users,
                "business_impact": business_impact,
                "duration_minutes": duration
            }
        }
    
    def _classify_severity(self, description: str, affected_users: str, 
                          business_impact: str, duration: int) -> str:
        """Classify incident severity based on multiple factors."""
        scores = {"sev1": 0, "sev2": 0, "sev3": 0, "sev4": 0}
        
        # Keyword analysis
        for severity, rules in self.severity_rules.items():
            for keyword in rules["keywords"]:
                if keyword in description:
                    scores[severity] += 2
            
            for indicator in rules["impact_indicators"]:
                if indicator.lower() in description or indicator.lower() in affected_users.lower():
                    scores[severity] += 3
        
        # Business impact weighting
        if business_impact.lower() in ['critical', 'high', 'severe']:
            scores["sev1"] += 5
            scores["sev2"] += 3
        elif business_impact.lower() in ['medium', 'moderate']:
            scores["sev2"] += 3
            scores["sev3"] += 2
        elif business_impact.lower() in ['low', 'minimal']:
            scores["sev3"] += 2
            scores["sev4"] += 3
        
        # User impact analysis
        if '%' in affected_users:
            try:
                percentage = float(re.findall(r'\d+', affected_users)[0])
                if percentage >= 75:
                    scores["sev1"] += 4
                elif percentage >= 25:
                    scores["sev2"] += 4
                elif percentage >= 5:
                    scores["sev3"] += 3
                else:
                    scores["sev4"] += 2
            except (IndexError, ValueError):
                pass
        
        # Duration consideration
        if duration > 0:
            if duration >= 3600:  # 1 hour
                scores["sev1"] += 2
                scores["sev2"] += 1
            elif duration >= 1800:  # 30 minutes
                scores["sev2"] += 2
                scores["sev3"] += 1
        
        # Return highest scoring severity
        return max(scores, key=scores.get)
    
    def _determine_teams(self, description: str, service: str) -> List[str]:
        """Determine which teams should respond based on affected systems."""
        teams = set()
        text_to_analyze = f"{description} {service}".lower()
        
        for component, team_list in self.team_mappings.items():
            if component in text_to_analyze:
                teams.update(team_list)
        
        # Default teams if no specific match
        if not teams:
            teams = {"General Engineering", "SRE"}
        
        return list(teams)
    
    def _generate_initial_actions(self, severity: str, incident_data: Dict) -> List[Dict]:
        """Generate prioritized initial actions based on severity."""
        base_actions = self.action_templates[severity].copy()
        
        # Customize actions based on incident details
        for action in base_actions:
            if severity in ["sev1", "sev2"]:
                action["urgency"] = "immediate" if severity == "sev1" else "high"
            else:
                action["urgency"] = "normal" if severity == "sev3" else "low"
        
        return base_actions
    
    def _generate_communication(self, severity: str, incident_data: Dict) -> Dict:
        """Generate communication template filled with incident data."""
        template = self.communication_templates[severity]
        
        # Fill template with incident data
        now = datetime.now(timezone.utc)
        service = incident_data.get('service', 'Unknown Service')
        description = incident_data.get('description', 'Incident detected')
        
        communication = {
            "subject": template["subject"].format(
                service=service,
                brief_description=description[:50] + "..." if len(description) > 50 else description
            ),
            "body": template["body"],
            "urgency": severity,
            "recipients": self._determine_recipients(severity),
            "channels": self._determine_channels(severity),
            "frequency_minutes": self._get_update_frequency(severity)
        }
        
        return communication
    
    def _generate_timeline(self, severity: str) -> Dict:
        """Generate expected response timeline."""
        rules = self.severity_rules[severity]
        now = datetime.now(timezone.utc)
        
        milestones = []
        if severity == "sev1":
            milestones = [
                {"milestone": "Incident Commander assigned", "minutes": 5},
                {"milestone": "War room established", "minutes": 10},
                {"milestone": "Initial status page update", "minutes": 15},
                {"milestone": "Executive notification", "minutes": 15},
                {"milestone": "First customer update", "minutes": 30}
            ]
        elif severity == "sev2":
            milestones = [
                {"milestone": "Response team assembled", "minutes": 15},
                {"milestone": "Initial assessment complete", "minutes": 30},
                {"milestone": "Stakeholder notification", "minutes": 60},
                {"milestone": "Status page update (if needed)", "minutes": 60}
            ]
        elif severity == "sev3":
            milestones = [
                {"milestone": "Team assignment", "minutes": 120},
                {"milestone": "Initial triage complete", "minutes": 240},
                {"milestone": "Resolution plan created", "minutes": 480}
            ]
        else:  # sev4
            milestones = [
                {"milestone": "Backlog creation", "minutes": 1440},
                {"milestone": "Priority assessment", "minutes": 2880}
            ]
        
        return {
            "response_time_minutes": rules["response_time"] // 60,
            "milestones": milestones,
            "update_frequency_minutes": self._get_update_frequency(severity)
        }
    
    def _determine_escalation(self, severity: str, business_impact: str) -> Dict:
        """Determine escalation requirements and triggers."""
        escalation_rules = {
            "sev1": {
                "immediate": ["Incident Commander", "Engineering Manager"],
                "15_minutes": ["VP Engineering", "Customer Success"],
                "30_minutes": ["CTO"],
                "60_minutes": ["CEO", "All C-Suite"],
                "triggers": ["Extended outage", "Revenue impact", "Media attention"]
            },
            "sev2": {
                "immediate": ["Team Lead", "On-call Engineer"],
                "30_minutes": ["Engineering Manager"],
                "120_minutes": ["VP Engineering"],
                "triggers": ["No progress", "Expanding scope", "Customer escalation"]
            },
            "sev3": {
                "immediate": ["Assigned Engineer"],
                "240_minutes": ["Team Lead"],
                "triggers": ["Issue complexity", "Multiple teams needed"]
            },
            "sev4": {
                "immediate": ["Product Owner"],
                "triggers": ["Customer request", "Stakeholder priority"]
            }
        }
        
        return escalation_rules.get(severity, escalation_rules["sev4"])
    
    def _determine_recipients(self, severity: str) -> List[str]:
        """Determine who should receive notifications."""
        recipients = {
            "sev1": ["on-call", "engineering-leadership", "executives", "customer-success"],
            "sev2": ["on-call", "engineering-leadership", "product-team"],
            "sev3": ["assigned-team", "team-lead"],
            "sev4": ["assigned-engineer"]
        }
        return recipients.get(severity, recipients["sev4"])
    
    def _determine_channels(self, severity: str) -> List[str]:
        """Determine communication channels to use."""
        channels = {
            "sev1": ["pager", "phone", "slack", "email", "status-page"],
            "sev2": ["pager", "slack", "email"],
            "sev3": ["slack", "email"],
            "sev4": ["ticket-system"]
        }
        return channels.get(severity, channels["sev4"])
    
    def _get_update_frequency(self, severity: str) -> int:
        """Get recommended update frequency in minutes."""
        frequencies = {"sev1": 15, "sev2": 30, "sev3": 240, "sev4": 0}
        return frequencies.get(severity, 0)
    
    def _calculate_confidence(self, description: str, affected_users: str, business_impact: str) -> float:
        """Calculate confidence score for the classification."""
        confidence = 0.5  # Base confidence
        
        # Higher confidence with more specific information
        if '%' in affected_users and any(char.isdigit() for char in affected_users):
            confidence += 0.2
        
        if business_impact.lower() in ['critical', 'high', 'medium', 'low']:
            confidence += 0.15
        
        if len(description.split()) > 5:  # Detailed description
            confidence += 0.15
        
        return min(confidence, 1.0)
    
    def _explain_classification(self, severity: str, description: str, affected_users: str) -> str:
        """Provide explanation for the classification decision."""
        rules = self.severity_rules[severity]
        
        matched_keywords = []
        for keyword in rules["keywords"]:
            if keyword in description.lower():
                matched_keywords.append(keyword)
        
        explanation = f"Classified as {severity.upper()} based on: "
        reasons = []
        
        if matched_keywords:
            reasons.append(f"keywords: {', '.join(matched_keywords[:3])}")
        
        if '%' in affected_users:
            reasons.append(f"user impact: {affected_users}")
        
        if not reasons:
            reasons.append("default classification based on available information")
        
        return explanation + "; ".join(reasons)


def format_json_output(result: Dict) -> str:
    """Format result as pretty JSON."""
    return json.dumps(result, indent=2, ensure_ascii=False)


def format_text_output(result: Dict) -> str:
    """Format result as human-readable text."""
    classification = result["classification"]
    response = result["response"]
    actions = result["initial_actions"]
    communication = result["communication"]
    
    output = []
    output.append("=" * 60)
    output.append("INCIDENT CLASSIFICATION REPORT")
    output.append("=" * 60)
    output.append("")
    
    # Classification section
    output.append("CLASSIFICATION:")
    output.append(f"  Severity: {classification['severity']}")
    output.append(f"  Confidence: {classification['confidence']:.1%}")
    output.append(f"  Reasoning: {classification['reasoning']}")
    output.append(f"  Timestamp: {classification['timestamp']}")
    output.append("")
    
    # Response section
    output.append("RECOMMENDED RESPONSE:")
    output.append(f"  Primary Team: {response['primary_team']}")
    if response['supporting_teams']:
        output.append(f"  Supporting Teams: {', '.join(response['supporting_teams'])}")
    output.append(f"  Response Time: {response['response_time_minutes']} minutes")
    output.append("")
    
    # Actions section
    output.append("INITIAL ACTIONS:")
    for i, action in enumerate(actions[:5], 1):  # Show first 5 actions
        output.append(f"  {i}. {action['action']} (Priority {action['priority']})")
        output.append(f"     Timeout: {action['timeout_minutes']} minutes")
        output.append(f"     {action['description']}")
        output.append("")
    
    # Communication section
    output.append("COMMUNICATION:")
    output.append(f"  Subject: {communication['subject']}")
    output.append(f"  Urgency: {communication['urgency'].upper()}")
    output.append(f"  Recipients: {', '.join(communication['recipients'])}")
    output.append(f"  Channels: {', '.join(communication['channels'])}")
    if communication['frequency_minutes'] > 0:
        output.append(f"  Update Frequency: Every {communication['frequency_minutes']} minutes")
    output.append("")
    
    output.append("=" * 60)
    
    return "\n".join(output)


def parse_input_text(text: str) -> Dict[str, Any]:
    """Parse free-form text input into structured incident data."""
    # Basic parsing - in a real system, this would be more sophisticated
    incident_data = {
        "description": text.strip(),
        "service": "unknown service",
        "affected_users": "unknown",
        "business_impact": "unknown"
    }
    
    # Try to extract service name
    service_patterns = [
        r'(?:service|api|database|server|application)\s+(\w+)',
        r'(\w+)(?:\s+(?:is|has|service|api|database))',
        r'(?:^|\s)(\w+)\s+(?:down|failed|broken)'
    ]
    
    for pattern in service_patterns:
        match = re.search(pattern, text.lower())
        if match:
            incident_data["service"] = match.group(1)
            break
    
    # Try to extract user impact
    impact_patterns = [
        r'(\d+%)\s+(?:of\s+)?(?:users?|customers?)',
        r'(?:all|every|100%)\s+(?:users?|customers?)',
        r'(?:some|many|several)\s+(?:users?|customers?)'
    ]
    
    for pattern in impact_patterns:
        match = re.search(pattern, text.lower())
        if match:
            incident_data["affected_users"] = match.group(1) if match.group(1) else match.group(0)
            break
    
    # Try to infer business impact
    if any(word in text.lower() for word in ['critical', 'urgent', 'emergency', 'down', 'outage']):
        incident_data["business_impact"] = "high"
    elif any(word in text.lower() for word in ['slow', 'degraded', 'performance']):
        incident_data["business_impact"] = "medium"
    elif any(word in text.lower() for word in ['minor', 'cosmetic', 'small']):
        incident_data["business_impact"] = "low"
    
    return incident_data


def interactive_mode():
    """Run in interactive mode, prompting user for input."""
    classifier = IncidentClassifier()
    
    print("🚨 Incident Classifier - Interactive Mode")
    print("=" * 50)
    print("Enter incident details (or 'quit' to exit):")
    print()
    
    while True:
        try:
            description = input("Incident description: ").strip()
            if description.lower() in ['quit', 'exit', 'q']:
                break
            
            if not description:
                print("Please provide an incident description.")
                continue
            
            service = input("Affected service (optional): ").strip() or "unknown"
            affected_users = input("Affected users (e.g., '50%', 'all users'): ").strip() or "unknown"
            business_impact = input("Business impact (high/medium/low): ").strip() or "unknown"
            
            incident_data = {
                "description": description,
                "service": service,
                "affected_users": affected_users,
                "business_impact": business_impact
            }
            
            result = classifier.classify_incident(incident_data)
            print("\n" + "=" * 50)
            print(format_text_output(result))
            print("=" * 50)
            print()
            
        except KeyboardInterrupt:
            print("\n\nExiting...")
            break
        except Exception as e:
            print(f"Error: {e}")


def main():
    """Main function with argument parsing and execution."""
    parser = argparse.ArgumentParser(
        description="Classify incidents and provide response recommendations",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python incident_classifier.py --input incident.json
  echo "Database is down" | python incident_classifier.py --format text
  python incident_classifier.py --interactive
  
Input JSON format:
  {
    "description": "Database connection timeouts",
    "service": "user-service",
    "affected_users": "80%",
    "business_impact": "high"
  }
        """
    )
    
    parser.add_argument(
        "--input", "-i",
        help="Input file path (JSON format) or '-' for stdin"
    )
    
    parser.add_argument(
        "--format", "-f",
        choices=["json", "text"],
        default="json",
        help="Output format (default: json)"
    )
    
    parser.add_argument(
        "--interactive",
        action="store_true",
        help="Run in interactive mode"
    )
    
    parser.add_argument(
        "--output", "-o",
        help="Output file path (default: stdout)"
    )
    
    args = parser.parse_args()
    
    # Interactive mode
    if args.interactive:
        interactive_mode()
        return
    
    classifier = IncidentClassifier()
    
    try:
        # Read input
        if args.input == "-" or (not args.input and not sys.stdin.isatty()):
            # Read from stdin
            input_text = sys.stdin.read().strip()
            if not input_text:
                parser.error("No input provided")
            
            # Try to parse as JSON first, then as text
            try:
                incident_data = json.loads(input_text)
            except json.JSONDecodeError:
                incident_data = parse_input_text(input_text)
                
        elif args.input:
            # Read from file
            with open(args.input, 'r') as f:
                incident_data = json.load(f)
        else:
            parser.error("No input specified. Use --input, --interactive, or pipe data to stdin.")
        
        # Validate required fields
        if not isinstance(incident_data, dict):
            parser.error("Input must be a JSON object")
        
        if "description" not in incident_data:
            parser.error("Input must contain 'description' field")
        
        # Classify incident
        result = classifier.classify_incident(incident_data)
        
        # Format output
        if args.format == "json":
            output = format_json_output(result)
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