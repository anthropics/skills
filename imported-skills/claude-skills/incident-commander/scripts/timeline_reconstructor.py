#!/usr/bin/env python3
"""
Timeline Reconstructor

Reconstructs incident timelines from timestamped events (logs, alerts, Slack messages).
Identifies incident phases, calculates durations, and performs gap analysis.

This tool processes chronological event data and creates a coherent narrative
of how an incident progressed from detection through resolution.

Usage:
    python timeline_reconstructor.py --input events.json --output timeline.md
    python timeline_reconstructor.py --input events.json --detect-phases --gap-analysis
    cat events.json | python timeline_reconstructor.py --format text
"""

import argparse
import json
import sys
import re
from datetime import datetime, timezone, timedelta
from typing import Dict, List, Optional, Any, Tuple
from collections import defaultdict, namedtuple


# Event data structure
Event = namedtuple('Event', ['timestamp', 'source', 'type', 'message', 'severity', 'actor', 'metadata'])

# Phase data structure
Phase = namedtuple('Phase', ['name', 'start_time', 'end_time', 'duration', 'events', 'description'])


class TimelineReconstructor:
    """
    Reconstructs incident timelines from disparate event sources.
    Identifies phases, calculates metrics, and performs gap analysis.
    """
    
    def __init__(self):
        """Initialize the reconstructor with phase detection rules and templates."""
        self.phase_patterns = self._load_phase_patterns()
        self.event_types = self._load_event_types()
        self.severity_mapping = self._load_severity_mapping()
        self.gap_thresholds = self._load_gap_thresholds()
    
    def _load_phase_patterns(self) -> Dict[str, Dict]:
        """Load patterns for identifying incident phases."""
        return {
            "detection": {
                "keywords": [
                    "alert", "alarm", "triggered", "fired", "detected", "noticed",
                    "monitoring", "threshold exceeded", "anomaly", "spike",
                    "error rate", "latency increase", "timeout", "failure"
                ],
                "event_types": ["alert", "monitoring", "notification"],
                "priority": 1,
                "description": "Initial detection of the incident through monitoring or observation"
            },
            "triage": {
                "keywords": [
                    "investigating", "triaging", "assessing", "evaluating",
                    "checking", "looking into", "analyzing", "reviewing",
                    "diagnosis", "troubleshooting", "examining"
                ],
                "event_types": ["investigation", "communication", "action"],
                "priority": 2,
                "description": "Assessment and initial investigation of the incident"
            },
            "escalation": {
                "keywords": [
                    "escalating", "paging", "calling in", "requesting help",
                    "engaging", "involving", "notifying", "alerting team",
                    "incident commander", "war room", "all hands"
                ],
                "event_types": ["escalation", "communication", "notification"],
                "priority": 3,
                "description": "Escalation to additional resources or higher severity response"
            },
            "mitigation": {
                "keywords": [
                    "fixing", "patching", "deploying", "rolling back", "restarting",
                    "scaling", "rerouting", "bypassing", "workaround",
                    "implementing fix", "applying solution", "remediation"
                ],
                "event_types": ["deployment", "action", "fix"],
                "priority": 4,
                "description": "Active mitigation efforts to resolve the incident"
            },
            "resolution": {
                "keywords": [
                    "resolved", "fixed", "restored", "recovered", "back online",
                    "working", "normal", "stable", "healthy", "operational",
                    "incident closed", "service restored"
                ],
                "event_types": ["resolution", "confirmation"],
                "priority": 5,
                "description": "Confirmation that the incident has been resolved"
            },
            "review": {
                "keywords": [
                    "post-mortem", "retrospective", "review", "lessons learned",
                    "pir", "post-incident", "analysis", "follow-up",
                    "action items", "improvements"
                ],
                "event_types": ["review", "documentation"],
                "priority": 6,
                "description": "Post-incident review and documentation activities"
            }
        }
    
    def _load_event_types(self) -> Dict[str, Dict]:
        """Load event type classification rules."""
        return {
            "alert": {
                "sources": ["monitoring", "nagios", "datadog", "newrelic", "prometheus"],
                "indicators": ["alert", "alarm", "threshold", "metric"],
                "severity_boost": 2
            },
            "log": {
                "sources": ["application", "server", "container", "system"],
                "indicators": ["error", "exception", "warn", "fail"],
                "severity_boost": 1
            },
            "communication": {
                "sources": ["slack", "teams", "email", "chat"],
                "indicators": ["message", "notification", "update"],
                "severity_boost": 0
            },
            "deployment": {
                "sources": ["ci/cd", "jenkins", "github", "gitlab", "deploy"],
                "indicators": ["deploy", "release", "build", "merge"],
                "severity_boost": 3
            },
            "action": {
                "sources": ["manual", "script", "automation", "operator"],
                "indicators": ["executed", "ran", "performed", "applied"],
                "severity_boost": 2
            },
            "escalation": {
                "sources": ["pagerduty", "opsgenie", "oncall", "escalation"],
                "indicators": ["paged", "escalated", "notified", "assigned"],
                "severity_boost": 3
            }
        }
    
    def _load_severity_mapping(self) -> Dict[str, int]:
        """Load severity level mappings."""
        return {
            "critical": 5, "crit": 5, "sev1": 5, "p1": 5,
            "high": 4, "major": 4, "sev2": 4, "p2": 4,
            "medium": 3, "moderate": 3, "sev3": 3, "p3": 3,
            "low": 2, "minor": 2, "sev4": 2, "p4": 2,
            "info": 1, "informational": 1, "debug": 1,
            "unknown": 0
        }
    
    def _load_gap_thresholds(self) -> Dict[str, int]:
        """Load gap analysis thresholds in minutes."""
        return {
            "detection_to_triage": 15,  # Should start investigating within 15 min
            "triage_to_mitigation": 30,  # Should start mitigation within 30 min
            "mitigation_to_resolution": 120,  # Should resolve within 2 hours
            "communication_gap": 30,  # Should communicate every 30 min
            "action_gap": 60,  # Should take actions every hour
            "phase_transition": 45  # Should transition phases within 45 min
        }
    
    def reconstruct_timeline(self, events_data: List[Dict]) -> Dict[str, Any]:
        """
        Main reconstruction method that processes events and builds timeline.
        
        Args:
            events_data: List of event dictionaries
            
        Returns:
            Dictionary with timeline analysis and metrics
        """
        # Parse and normalize events
        events = self._parse_events(events_data)
        if not events:
            return {"error": "No valid events found"}
        
        # Sort events chronologically
        events.sort(key=lambda e: e.timestamp)
        
        # Detect phases
        phases = self._detect_phases(events)
        
        # Calculate metrics
        metrics = self._calculate_metrics(events, phases)
        
        # Perform gap analysis
        gap_analysis = self._analyze_gaps(events, phases)
        
        # Generate timeline narrative
        narrative = self._generate_narrative(events, phases)
        
        # Create summary statistics
        summary = self._generate_summary(events, phases, metrics)
        
        return {
            "timeline": {
                "total_events": len(events),
                "time_range": {
                    "start": events[0].timestamp.isoformat(),
                    "end": events[-1].timestamp.isoformat(),
                    "duration_minutes": int((events[-1].timestamp - events[0].timestamp).total_seconds() / 60)
                },
                "phases": [self._phase_to_dict(phase) for phase in phases],
                "events": [self._event_to_dict(event) for event in events]
            },
            "metrics": metrics,
            "gap_analysis": gap_analysis,
            "narrative": narrative,
            "summary": summary,
            "reconstruction_timestamp": datetime.now(timezone.utc).isoformat()
        }
    
    def _parse_events(self, events_data: List[Dict]) -> List[Event]:
        """Parse raw event data into normalized Event objects."""
        events = []
        
        for event_dict in events_data:
            try:
                # Parse timestamp
                timestamp_str = event_dict.get("timestamp", event_dict.get("time", ""))
                if not timestamp_str:
                    continue
                
                timestamp = self._parse_timestamp(timestamp_str)
                if not timestamp:
                    continue
                
                # Extract other fields
                source = event_dict.get("source", "unknown")
                event_type = self._classify_event_type(event_dict)
                message = event_dict.get("message", event_dict.get("description", ""))
                severity = self._parse_severity(event_dict.get("severity", event_dict.get("level", "unknown")))
                actor = event_dict.get("actor", event_dict.get("user", "system"))
                
                # Extract metadata
                metadata = {k: v for k, v in event_dict.items() 
                           if k not in ["timestamp", "time", "source", "type", "message", "severity", "actor"]}
                
                event = Event(
                    timestamp=timestamp,
                    source=source,
                    type=event_type,
                    message=message,
                    severity=severity,
                    actor=actor,
                    metadata=metadata
                )
                
                events.append(event)
                
            except Exception as e:
                # Skip invalid events but log them
                continue
        
        return events
    
    def _parse_timestamp(self, timestamp_str: str) -> Optional[datetime]:
        """Parse various timestamp formats."""
        # Common timestamp formats
        formats = [
            "%Y-%m-%dT%H:%M:%S.%fZ",  # ISO with microseconds
            "%Y-%m-%dT%H:%M:%SZ",     # ISO without microseconds
            "%Y-%m-%d %H:%M:%S",      # Standard format
            "%m/%d/%Y %H:%M:%S",      # US format
            "%d/%m/%Y %H:%M:%S",      # EU format
            "%Y-%m-%d %H:%M:%S.%f",   # With microseconds
            "%Y%m%d_%H%M%S",          # Compact format
        ]
        
        for fmt in formats:
            try:
                dt = datetime.strptime(timestamp_str, fmt)
                # Ensure timezone awareness
                if dt.tzinfo is None:
                    dt = dt.replace(tzinfo=timezone.utc)
                return dt
            except ValueError:
                continue
        
        # Try parsing as Unix timestamp
        try:
            timestamp_float = float(timestamp_str)
            return datetime.fromtimestamp(timestamp_float, tz=timezone.utc)
        except ValueError:
            pass
        
        return None
    
    def _classify_event_type(self, event_dict: Dict) -> str:
        """Classify event type based on source and content."""
        source = event_dict.get("source", "").lower()
        message = event_dict.get("message", "").lower()
        event_type = event_dict.get("type", "").lower()
        
        # Check explicit type first
        if event_type in self.event_types:
            return event_type
        
        # Classify based on source and content
        for type_name, type_info in self.event_types.items():
            # Check source patterns
            if any(src in source for src in type_info["sources"]):
                return type_name
            
            # Check message indicators
            if any(indicator in message for indicator in type_info["indicators"]):
                return type_name
        
        return "unknown"
    
    def _parse_severity(self, severity_str: str) -> int:
        """Parse severity string to numeric value."""
        severity_clean = str(severity_str).lower().strip()
        return self.severity_mapping.get(severity_clean, 0)
    
    def _detect_phases(self, events: List[Event]) -> List[Phase]:
        """Detect incident phases based on event patterns."""
        phases = []
        current_phase = None
        phase_events = []
        
        for event in events:
            detected_phase = self._identify_phase(event)
            
            if detected_phase != current_phase:
                # End current phase if exists
                if current_phase and phase_events:
                    phase_obj = Phase(
                        name=current_phase,
                        start_time=phase_events[0].timestamp,
                        end_time=phase_events[-1].timestamp,
                        duration=(phase_events[-1].timestamp - phase_events[0].timestamp).total_seconds() / 60,
                        events=phase_events.copy(),
                        description=self.phase_patterns[current_phase]["description"]
                    )
                    phases.append(phase_obj)
                
                # Start new phase
                current_phase = detected_phase
                phase_events = [event]
            else:
                phase_events.append(event)
        
        # Add final phase
        if current_phase and phase_events:
            phase_obj = Phase(
                name=current_phase,
                start_time=phase_events[0].timestamp,
                end_time=phase_events[-1].timestamp,
                duration=(phase_events[-1].timestamp - phase_events[0].timestamp).total_seconds() / 60,
                events=phase_events,
                description=self.phase_patterns[current_phase]["description"]
            )
            phases.append(phase_obj)
        
        return self._merge_adjacent_phases(phases)
    
    def _identify_phase(self, event: Event) -> str:
        """Identify which phase an event belongs to."""
        message_lower = event.message.lower()
        
        # Score each phase based on keywords and event type
        phase_scores = {}
        
        for phase_name, pattern_info in self.phase_patterns.items():
            score = 0
            
            # Keyword matching
            for keyword in pattern_info["keywords"]:
                if keyword in message_lower:
                    score += 2
            
            # Event type matching
            if event.type in pattern_info["event_types"]:
                score += 3
            
            # Severity boost for certain phases
            if phase_name == "escalation" and event.severity >= 4:
                score += 2
            
            phase_scores[phase_name] = score
        
        # Return highest scoring phase, default to triage
        if phase_scores and max(phase_scores.values()) > 0:
            return max(phase_scores, key=phase_scores.get)
        
        return "triage"  # Default phase
    
    def _merge_adjacent_phases(self, phases: List[Phase]) -> List[Phase]:
        """Merge adjacent phases of the same type."""
        if not phases:
            return phases
        
        merged = []
        current_phase = phases[0]
        
        for next_phase in phases[1:]:
            if (next_phase.name == current_phase.name and 
                (next_phase.start_time - current_phase.end_time).total_seconds() < 300):  # 5 min gap
                # Merge phases
                merged_events = current_phase.events + next_phase.events
                current_phase = Phase(
                    name=current_phase.name,
                    start_time=current_phase.start_time,
                    end_time=next_phase.end_time,
                    duration=(next_phase.end_time - current_phase.start_time).total_seconds() / 60,
                    events=merged_events,
                    description=current_phase.description
                )
            else:
                merged.append(current_phase)
                current_phase = next_phase
        
        merged.append(current_phase)
        return merged
    
    def _calculate_metrics(self, events: List[Event], phases: List[Phase]) -> Dict[str, Any]:
        """Calculate timeline metrics and KPIs."""
        if not events or not phases:
            return {}
        
        start_time = events[0].timestamp
        end_time = events[-1].timestamp
        total_duration = (end_time - start_time).total_seconds() / 60
        
        # Phase timing metrics
        phase_durations = {phase.name: phase.duration for phase in phases}
        
        # Detection metrics
        detection_time = 0
        if phases and phases[0].name == "detection":
            detection_time = phases[0].duration
        
        # Time to mitigation
        mitigation_start = None
        for phase in phases:
            if phase.name == "mitigation":
                mitigation_start = (phase.start_time - start_time).total_seconds() / 60
                break
        
        # Time to resolution
        resolution_time = None
        for phase in phases:
            if phase.name == "resolution":
                resolution_time = (phase.start_time - start_time).total_seconds() / 60
                break
        
        # Communication frequency
        comm_events = [e for e in events if e.type == "communication"]
        comm_frequency = len(comm_events) / (total_duration / 60) if total_duration > 0 else 0
        
        # Action frequency
        action_events = [e for e in events if e.type == "action"]
        action_frequency = len(action_events) / (total_duration / 60) if total_duration > 0 else 0
        
        # Event source distribution
        source_counts = defaultdict(int)
        for event in events:
            source_counts[event.source] += 1
        
        return {
            "duration_metrics": {
                "total_duration_minutes": round(total_duration, 1),
                "detection_duration_minutes": round(detection_time, 1),
                "time_to_mitigation_minutes": round(mitigation_start or 0, 1),
                "time_to_resolution_minutes": round(resolution_time or 0, 1),
                "phase_durations": {k: round(v, 1) for k, v in phase_durations.items()}
            },
            "activity_metrics": {
                "total_events": len(events),
                "events_per_hour": round((len(events) / (total_duration / 60)) if total_duration > 0 else 0, 1),
                "communication_frequency": round(comm_frequency, 1),
                "action_frequency": round(action_frequency, 1),
                "unique_sources": len(source_counts),
                "unique_actors": len(set(e.actor for e in events))
            },
            "phase_metrics": {
                "total_phases": len(phases),
                "phase_sequence": [p.name for p in phases],
                "longest_phase": max(phases, key=lambda p: p.duration).name if phases else None,
                "shortest_phase": min(phases, key=lambda p: p.duration).name if phases else None
            },
            "source_distribution": dict(source_counts)
        }
    
    def _analyze_gaps(self, events: List[Event], phases: List[Phase]) -> Dict[str, Any]:
        """Perform gap analysis to identify potential issues."""
        gaps = []
        warnings = []
        
        # Check phase transition timing
        for i in range(len(phases) - 1):
            current_phase = phases[i]
            next_phase = phases[i + 1]
            
            transition_gap = (next_phase.start_time - current_phase.end_time).total_seconds() / 60
            threshold_key = f"{current_phase.name}_to_{next_phase.name}"
            threshold = self.gap_thresholds.get(threshold_key, self.gap_thresholds["phase_transition"])
            
            if transition_gap > threshold:
                gaps.append({
                    "type": "phase_transition",
                    "from_phase": current_phase.name,
                    "to_phase": next_phase.name,
                    "gap_minutes": round(transition_gap, 1),
                    "threshold_minutes": threshold,
                    "severity": "warning" if transition_gap < threshold * 2 else "critical"
                })
        
        # Check communication gaps
        comm_events = [e for e in events if e.type == "communication"]
        for i in range(len(comm_events) - 1):
            gap_minutes = (comm_events[i+1].timestamp - comm_events[i].timestamp).total_seconds() / 60
            if gap_minutes > self.gap_thresholds["communication_gap"]:
                gaps.append({
                    "type": "communication_gap",
                    "gap_minutes": round(gap_minutes, 1),
                    "threshold_minutes": self.gap_thresholds["communication_gap"],
                    "severity": "warning" if gap_minutes < self.gap_thresholds["communication_gap"] * 2 else "critical"
                })
        
        # Check for missing phases
        expected_phases = ["detection", "triage", "mitigation", "resolution"]
        actual_phases = [p.name for p in phases]
        missing_phases = [p for p in expected_phases if p not in actual_phases]
        
        for missing_phase in missing_phases:
            warnings.append({
                "type": "missing_phase",
                "phase": missing_phase,
                "message": f"Expected phase '{missing_phase}' not detected in timeline"
            })
        
        # Check for unusually long phases
        for phase in phases:
            if phase.duration > 180:  # 3 hours
                warnings.append({
                    "type": "long_phase",
                    "phase": phase.name,
                    "duration_minutes": round(phase.duration, 1),
                    "message": f"Phase '{phase.name}' lasted {phase.duration:.0f} minutes, which is unusually long"
                })
        
        return {
            "gaps": gaps,
            "warnings": warnings,
            "gap_summary": {
                "total_gaps": len(gaps),
                "critical_gaps": len([g for g in gaps if g.get("severity") == "critical"]),
                "warning_gaps": len([g for g in gaps if g.get("severity") == "warning"]),
                "missing_phases": len(missing_phases)
            }
        }
    
    def _generate_narrative(self, events: List[Event], phases: List[Phase]) -> Dict[str, Any]:
        """Generate human-readable incident narrative."""
        if not events or not phases:
            return {"error": "Insufficient data for narrative generation"}
        
        # Create phase-based narrative
        phase_narratives = []
        for phase in phases:
            key_events = self._extract_key_events(phase.events)
            narrative_text = self._create_phase_narrative(phase, key_events)
            
            phase_narratives.append({
                "phase": phase.name,
                "start_time": phase.start_time.isoformat(),
                "duration_minutes": round(phase.duration, 1),
                "narrative": narrative_text,
                "key_events": len(key_events),
                "total_events": len(phase.events)
            })
        
        # Create overall summary
        start_time = events[0].timestamp
        end_time = events[-1].timestamp
        total_duration = (end_time - start_time).total_seconds() / 60
        
        summary = f"""Incident Timeline Summary:
The incident began at {start_time.strftime('%Y-%m-%d %H:%M:%S UTC')} and concluded at {end_time.strftime('%Y-%m-%d %H:%M:%S UTC')}, lasting approximately {total_duration:.0f} minutes.

The incident progressed through {len(phases)} distinct phases: {', '.join(p.name for p in phases)}.

Key milestones:"""
        
        for phase in phases:
            summary += f"\n- {phase.name.title()}: {phase.start_time.strftime('%H:%M')} ({phase.duration:.0f} min)"
        
        return {
            "summary": summary,
            "phase_narratives": phase_narratives,
            "timeline_type": self._classify_timeline_pattern(phases),
            "complexity_score": self._calculate_complexity_score(events, phases)
        }
    
    def _extract_key_events(self, events: List[Event]) -> List[Event]:
        """Extract the most important events from a phase."""
        # Sort by severity and timestamp
        sorted_events = sorted(events, key=lambda e: (e.severity, e.timestamp), reverse=True)
        
        # Take top events, but ensure chronological representation
        key_events = []
        
        # Always include first and last events
        if events:
            key_events.append(events[0])
            if len(events) > 1:
                key_events.append(events[-1])
        
        # Add high-severity events
        high_severity_events = [e for e in events if e.severity >= 4]
        key_events.extend(high_severity_events[:3])
        
        # Remove duplicates while preserving order
        seen = set()
        unique_events = []
        for event in key_events:
            event_key = (event.timestamp, event.message)
            if event_key not in seen:
                seen.add(event_key)
                unique_events.append(event)
        
        return sorted(unique_events, key=lambda e: e.timestamp)
    
    def _create_phase_narrative(self, phase: Phase, key_events: List[Event]) -> str:
        """Create narrative text for a phase."""
        phase_templates = {
            "detection": "The incident was first detected when {first_event}. {additional_details}",
            "triage": "Initial investigation began with {first_event}. The team {investigation_actions}",
            "escalation": "The incident was escalated when {escalation_trigger}. {escalation_actions}",
            "mitigation": "Mitigation efforts started with {first_action}. {mitigation_steps}",
            "resolution": "The incident was resolved when {resolution_event}. {confirmation_steps}",
            "review": "Post-incident review activities included {review_activities}"
        }
        
        template = phase_templates.get(phase.name, "During the {phase_name} phase, {activities}")
        
        if not key_events:
            return f"The {phase.name} phase lasted {phase.duration:.0f} minutes with {len(phase.events)} events."
        
        first_event = key_events[0].message
        
        # Customize based on phase
        if phase.name == "detection":
            return template.format(
                first_event=first_event,
                additional_details=f"This phase lasted {phase.duration:.0f} minutes with {len(phase.events)} total events."
            )
        elif phase.name == "triage":
            actions = [e.message for e in key_events if "investigating" in e.message.lower() or "checking" in e.message.lower()]
            investigation_text = "performed various diagnostic activities" if not actions else f"focused on {actions[0]}"
            return template.format(
                first_event=first_event,
                investigation_actions=investigation_text
            )
        else:
            return f"During the {phase.name} phase ({phase.duration:.0f} minutes), key activities included: {first_event}"
    
    def _classify_timeline_pattern(self, phases: List[Phase]) -> str:
        """Classify the overall timeline pattern."""
        phase_names = [p.name for p in phases]
        
        if "escalation" in phase_names and phases[0].name == "detection":
            return "standard_escalation"
        elif len(phases) <= 3:
            return "simple_resolution"
        elif "review" in phase_names:
            return "comprehensive_response"
        else:
            return "complex_incident"
    
    def _calculate_complexity_score(self, events: List[Event], phases: List[Phase]) -> float:
        """Calculate incident complexity score (0-10)."""
        score = 0.0
        
        # Phase count contributes to complexity
        score += min(len(phases) * 1.5, 6.0)
        
        # Event count contributes to complexity
        score += min(len(events) / 20, 2.0)
        
        # Duration contributes to complexity
        if events:
            duration_hours = (events[-1].timestamp - events[0].timestamp).total_seconds() / 3600
            score += min(duration_hours / 2, 2.0)
        
        return min(score, 10.0)
    
    def _generate_summary(self, events: List[Event], phases: List[Phase], metrics: Dict) -> Dict[str, Any]:
        """Generate comprehensive incident summary."""
        if not events:
            return {}
        
        # Key statistics
        start_time = events[0].timestamp
        end_time = events[-1].timestamp
        duration_minutes = metrics.get("duration_metrics", {}).get("total_duration_minutes", 0)
        
        # Phase analysis
        phase_analysis = {}
        for phase in phases:
            phase_analysis[phase.name] = {
                "duration_minutes": round(phase.duration, 1),
                "event_count": len(phase.events),
                "start_time": phase.start_time.isoformat(),
                "end_time": phase.end_time.isoformat()
            }
        
        # Actor involvement
        actors = defaultdict(int)
        for event in events:
            actors[event.actor] += 1
        
        return {
            "incident_overview": {
                "start_time": start_time.isoformat(),
                "end_time": end_time.isoformat(),
                "total_duration_minutes": round(duration_minutes, 1),
                "total_events": len(events),
                "phases_detected": len(phases)
            },
            "phase_analysis": phase_analysis,
            "key_participants": dict(actors),
            "event_sources": dict(defaultdict(int, {e.source: 1 for e in events})),
            "complexity_indicators": {
                "unique_sources": len(set(e.source for e in events)),
                "unique_actors": len(set(e.actor for e in events)),
                "high_severity_events": len([e for e in events if e.severity >= 4]),
                "phase_transitions": len(phases) - 1 if phases else 0
            }
        }
    
    def _event_to_dict(self, event: Event) -> Dict:
        """Convert Event namedtuple to dictionary."""
        return {
            "timestamp": event.timestamp.isoformat(),
            "source": event.source,
            "type": event.type,
            "message": event.message,
            "severity": event.severity,
            "actor": event.actor,
            "metadata": event.metadata
        }
    
    def _phase_to_dict(self, phase: Phase) -> Dict:
        """Convert Phase namedtuple to dictionary."""
        return {
            "name": phase.name,
            "start_time": phase.start_time.isoformat(),
            "end_time": phase.end_time.isoformat(),
            "duration_minutes": round(phase.duration, 1),
            "event_count": len(phase.events),
            "description": phase.description
        }


def format_json_output(result: Dict) -> str:
    """Format result as pretty JSON."""
    return json.dumps(result, indent=2, ensure_ascii=False)


def format_text_output(result: Dict) -> str:
    """Format result as human-readable text."""
    if "error" in result:
        return f"Error: {result['error']}"
    
    timeline = result["timeline"]
    metrics = result["metrics"]
    narrative = result["narrative"]
    
    output = []
    output.append("=" * 80)
    output.append("INCIDENT TIMELINE RECONSTRUCTION")
    output.append("=" * 80)
    output.append("")
    
    # Overview
    time_range = timeline["time_range"]
    output.append("OVERVIEW:")
    output.append(f"  Time Range: {time_range['start']} to {time_range['end']}")
    output.append(f"  Total Duration: {time_range['duration_minutes']} minutes")
    output.append(f"  Total Events: {timeline['total_events']}")
    output.append(f"  Phases Detected: {len(timeline['phases'])}")
    output.append("")
    
    # Phase summary
    output.append("PHASES:")
    for phase in timeline["phases"]:
        output.append(f"  {phase['name'].upper()}:")
        output.append(f"    Start: {phase['start_time']}")
        output.append(f"    Duration: {phase['duration_minutes']} minutes")
        output.append(f"    Events: {phase['event_count']}")
        output.append(f"    Description: {phase['description']}")
        output.append("")
    
    # Key metrics
    if "duration_metrics" in metrics:
        duration_metrics = metrics["duration_metrics"]
        output.append("KEY METRICS:")
        output.append(f"  Time to Mitigation: {duration_metrics.get('time_to_mitigation_minutes', 'N/A')} minutes")
        output.append(f"  Time to Resolution: {duration_metrics.get('time_to_resolution_minutes', 'N/A')} minutes")
        
        if "activity_metrics" in metrics:
            activity = metrics["activity_metrics"]
            output.append(f"  Events per Hour: {activity.get('events_per_hour', 'N/A')}")
            output.append(f"  Unique Sources: {activity.get('unique_sources', 'N/A')}")
        output.append("")
    
    # Narrative
    if "summary" in narrative:
        output.append("INCIDENT NARRATIVE:")
        output.append(narrative["summary"])
        output.append("")
    
    # Gap analysis
    if "gap_analysis" in result and result["gap_analysis"]["gaps"]:
        output.append("GAP ANALYSIS:")
        for gap in result["gap_analysis"]["gaps"][:5]:  # Show first 5 gaps
            output.append(f"  {gap['type'].replace('_', ' ').title()}: {gap['gap_minutes']} min gap (threshold: {gap['threshold_minutes']} min)")
        output.append("")
    
    output.append("=" * 80)
    
    return "\n".join(output)


def format_markdown_output(result: Dict) -> str:
    """Format result as Markdown timeline."""
    if "error" in result:
        return f"# Error\n\n{result['error']}"
    
    timeline = result["timeline"]
    narrative = result.get("narrative", {})
    
    output = []
    output.append("# Incident Timeline")
    output.append("")
    
    # Overview
    time_range = timeline["time_range"]
    output.append("## Overview")
    output.append("")
    output.append(f"- **Duration:** {time_range['duration_minutes']} minutes")
    output.append(f"- **Start Time:** {time_range['start']}")
    output.append(f"- **End Time:** {time_range['end']}")
    output.append(f"- **Total Events:** {timeline['total_events']}")
    output.append("")
    
    # Narrative summary
    if "summary" in narrative:
        output.append("## Summary")
        output.append("")
        output.append(narrative["summary"])
        output.append("")
    
    # Phase timeline
    output.append("## Phase Timeline")
    output.append("")
    
    for phase in timeline["phases"]:
        output.append(f"### {phase['name'].title()} Phase")
        output.append("")
        output.append(f"**Duration:** {phase['duration_minutes']} minutes  ")
        output.append(f"**Start:** {phase['start_time']}  ")
        output.append(f"**Events:** {phase['event_count']}  ")
        output.append("")
        output.append(phase["description"])
        output.append("")
    
    # Detailed timeline
    output.append("## Detailed Event Timeline")
    output.append("")
    
    for event in timeline["events"]:
        timestamp = datetime.fromisoformat(event["timestamp"].replace('Z', '+00:00'))
        output.append(f"**{timestamp.strftime('%H:%M:%S')}** [{event['source']}] {event['message']}")
        output.append("")
    
    return "\n".join(output)


def main():
    """Main function with argument parsing and execution."""
    parser = argparse.ArgumentParser(
        description="Reconstruct incident timeline from timestamped events",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python timeline_reconstructor.py --input events.json --output timeline.md
  python timeline_reconstructor.py --input events.json --detect-phases --gap-analysis
  cat events.json | python timeline_reconstructor.py --format text
  
Input JSON format:
  [
    {
      "timestamp": "2024-01-01T12:00:00Z",
      "source": "monitoring",
      "type": "alert",
      "message": "High error rate detected",
      "severity": "critical",
      "actor": "system"
    }
  ]
        """
    )
    
    parser.add_argument(
        "--input", "-i",
        help="Input file path (JSON format) or '-' for stdin"
    )
    
    parser.add_argument(
        "--output", "-o",
        help="Output file path (default: stdout)"
    )
    
    parser.add_argument(
        "--format", "-f",
        choices=["json", "text", "markdown"],
        default="json",
        help="Output format (default: json)"
    )
    
    parser.add_argument(
        "--detect-phases",
        action="store_true",
        help="Enable advanced phase detection"
    )
    
    parser.add_argument(
        "--gap-analysis",
        action="store_true",
        help="Perform gap analysis on timeline"
    )
    
    parser.add_argument(
        "--min-events",
        type=int,
        default=1,
        help="Minimum number of events required (default: 1)"
    )
    
    args = parser.parse_args()
    
    reconstructor = TimelineReconstructor()
    
    try:
        # Read input
        if args.input == "-" or (not args.input and not sys.stdin.isatty()):
            # Read from stdin
            input_text = sys.stdin.read().strip()
            if not input_text:
                parser.error("No input provided")
            events_data = json.loads(input_text)
        elif args.input:
            # Read from file
            with open(args.input, 'r') as f:
                events_data = json.load(f)
        else:
            parser.error("No input specified. Use --input or pipe data to stdin.")
        
        # Validate input
        if not isinstance(events_data, list):
            parser.error("Input must be a JSON array of events")
        
        if len(events_data) < args.min_events:
            parser.error(f"Minimum {args.min_events} events required")
        
        # Reconstruct timeline
        result = reconstructor.reconstruct_timeline(events_data)
        
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