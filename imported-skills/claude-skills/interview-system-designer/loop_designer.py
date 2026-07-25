#!/usr/bin/env python3
"""
Interview Loop Designer

Generates calibrated interview loops tailored to specific roles, levels, and teams.
Creates complete interview loops with rounds, focus areas, time allocation, 
interviewer skill requirements, and scorecard templates.

Usage:
    python loop_designer.py --role "Senior Software Engineer" --level senior --team platform
    python loop_designer.py --role "Product Manager" --level mid --competencies leadership,strategy
    python loop_designer.py --input role_definition.json --output loops/
"""

import os
import sys
import json
import argparse
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Any, Tuple
from collections import defaultdict


class InterviewLoopDesigner:
    """Designs comprehensive interview loops based on role requirements."""
    
    def __init__(self):
        self.competency_frameworks = self._init_competency_frameworks()
        self.role_templates = self._init_role_templates()
        self.interviewer_skills = self._init_interviewer_skills()
        
    def _init_competency_frameworks(self) -> Dict[str, Dict]:
        """Initialize competency frameworks for different roles."""
        return {
            "software_engineer": {
                "junior": {
                    "required": ["coding_fundamentals", "debugging", "testing_basics", "version_control"],
                    "preferred": ["system_understanding", "code_review", "collaboration"],
                    "focus_areas": ["technical_execution", "learning_agility", "team_collaboration"]
                },
                "mid": {
                    "required": ["advanced_coding", "system_design_basics", "testing_strategy", "debugging_complex"],
                    "preferred": ["mentoring_basics", "technical_communication", "project_ownership"],
                    "focus_areas": ["technical_depth", "system_thinking", "ownership"]
                },
                "senior": {
                    "required": ["system_architecture", "technical_leadership", "mentoring", "cross_team_collab"],
                    "preferred": ["technology_evaluation", "process_improvement", "hiring_contribution"],
                    "focus_areas": ["technical_leadership", "system_architecture", "people_development"]
                },
                "staff": {
                    "required": ["architectural_vision", "organizational_impact", "technical_strategy", "team_building"],
                    "preferred": ["industry_influence", "innovation_leadership", "executive_communication"],
                    "focus_areas": ["organizational_impact", "technical_vision", "strategic_influence"]
                },
                "principal": {
                    "required": ["company_wide_impact", "technical_vision", "talent_development", "strategic_planning"],
                    "preferred": ["industry_leadership", "board_communication", "market_influence"],
                    "focus_areas": ["strategic_leadership", "organizational_transformation", "external_influence"]
                }
            },
            "product_manager": {
                "junior": {
                    "required": ["product_execution", "user_research", "data_analysis", "stakeholder_comm"],
                    "preferred": ["market_awareness", "technical_understanding", "project_management"],
                    "focus_areas": ["execution_excellence", "user_focus", "analytical_thinking"]
                },
                "mid": {
                    "required": ["product_strategy", "cross_functional_leadership", "metrics_design", "market_analysis"],
                    "preferred": ["team_building", "technical_collaboration", "competitive_analysis"],
                    "focus_areas": ["strategic_thinking", "leadership", "business_impact"]
                },
                "senior": {
                    "required": ["business_strategy", "team_leadership", "p&l_ownership", "market_positioning"],
                    "preferred": ["hiring_leadership", "board_communication", "partnership_development"],
                    "focus_areas": ["business_leadership", "market_strategy", "organizational_impact"]
                },
                "staff": {
                    "required": ["portfolio_management", "organizational_leadership", "strategic_planning", "market_creation"],
                    "preferred": ["executive_presence", "investor_relations", "acquisition_strategy"],
                    "focus_areas": ["strategic_leadership", "market_innovation", "organizational_transformation"]
                }
            },
            "designer": {
                "junior": {
                    "required": ["design_fundamentals", "user_research", "prototyping", "design_tools"],
                    "preferred": ["user_empathy", "visual_design", "collaboration"],
                    "focus_areas": ["design_execution", "user_research", "creative_problem_solving"]
                },
                "mid": {
                    "required": ["design_systems", "user_testing", "cross_functional_collab", "design_strategy"],
                    "preferred": ["mentoring", "process_improvement", "business_understanding"],
                    "focus_areas": ["design_leadership", "system_thinking", "business_impact"]
                },
                "senior": {
                    "required": ["design_leadership", "team_building", "strategic_design", "stakeholder_management"],
                    "preferred": ["design_culture", "hiring_leadership", "executive_communication"],
                    "focus_areas": ["design_strategy", "team_leadership", "organizational_impact"]
                }
            },
            "data_scientist": {
                "junior": {
                    "required": ["statistical_analysis", "python_r", "data_visualization", "sql"],
                    "preferred": ["machine_learning", "business_understanding", "communication"],
                    "focus_areas": ["analytical_skills", "technical_execution", "business_impact"]
                },
                "mid": {
                    "required": ["advanced_ml", "experiment_design", "data_engineering", "stakeholder_comm"],
                    "preferred": ["mentoring", "project_leadership", "product_collaboration"],
                    "focus_areas": ["advanced_analytics", "project_leadership", "cross_functional_impact"]
                },
                "senior": {
                    "required": ["data_strategy", "team_leadership", "ml_systems", "business_strategy"],
                    "preferred": ["hiring_leadership", "executive_communication", "technology_evaluation"],
                    "focus_areas": ["strategic_leadership", "technical_vision", "organizational_impact"]
                }
            },
            "devops_engineer": {
                "junior": {
                    "required": ["infrastructure_basics", "scripting", "monitoring", "troubleshooting"],
                    "preferred": ["automation", "cloud_platforms", "security_awareness"],
                    "focus_areas": ["operational_excellence", "automation_mindset", "problem_solving"]
                },
                "mid": {
                    "required": ["ci_cd_design", "infrastructure_as_code", "security_implementation", "performance_optimization"],
                    "preferred": ["team_collaboration", "incident_management", "capacity_planning"],
                    "focus_areas": ["system_reliability", "automation_leadership", "cross_team_collaboration"]
                },
                "senior": {
                    "required": ["platform_architecture", "team_leadership", "security_strategy", "organizational_impact"],
                    "preferred": ["hiring_contribution", "technology_evaluation", "executive_communication"],
                    "focus_areas": ["platform_leadership", "strategic_thinking", "organizational_transformation"]
                }
            },
            "engineering_manager": {
                "junior": {
                    "required": ["team_leadership", "technical_background", "people_management", "project_coordination"],
                    "preferred": ["hiring_experience", "performance_management", "technical_mentoring"],
                    "focus_areas": ["people_leadership", "team_building", "execution_excellence"]
                },
                "senior": {
                    "required": ["organizational_leadership", "strategic_planning", "talent_development", "cross_functional_leadership"],
                    "preferred": ["technical_vision", "culture_building", "executive_communication"],
                    "focus_areas": ["organizational_impact", "strategic_leadership", "talent_development"]
                },
                "staff": {
                    "required": ["multi_team_leadership", "organizational_strategy", "executive_presence", "cultural_transformation"],
                    "preferred": ["board_communication", "market_understanding", "acquisition_integration"],
                    "focus_areas": ["organizational_transformation", "strategic_leadership", "cultural_evolution"]
                }
            }
        }
    
    def _init_role_templates(self) -> Dict[str, Dict]:
        """Initialize role-specific interview templates."""
        return {
            "software_engineer": {
                "core_rounds": ["technical_phone_screen", "coding_deep_dive", "system_design", "behavioral"],
                "optional_rounds": ["technical_leadership", "domain_expertise", "culture_fit"],
                "total_duration_range": (180, 360),  # 3-6 hours
                "required_competencies": ["coding", "problem_solving", "communication"]
            },
            "product_manager": {
                "core_rounds": ["product_sense", "analytical_thinking", "execution_process", "behavioral"],
                "optional_rounds": ["strategic_thinking", "technical_collaboration", "leadership"],
                "total_duration_range": (180, 300),  # 3-5 hours
                "required_competencies": ["product_strategy", "analytical_thinking", "stakeholder_management"]
            },
            "designer": {
                "core_rounds": ["portfolio_review", "design_challenge", "collaboration_process", "behavioral"],
                "optional_rounds": ["design_system_thinking", "research_methodology", "leadership"],
                "total_duration_range": (180, 300),  # 3-5 hours
                "required_competencies": ["design_process", "user_empathy", "visual_communication"]
            },
            "data_scientist": {
                "core_rounds": ["technical_assessment", "case_study", "statistical_thinking", "behavioral"],
                "optional_rounds": ["ml_systems", "business_strategy", "technical_leadership"],
                "total_duration_range": (210, 330),  # 3.5-5.5 hours
                "required_competencies": ["statistical_analysis", "programming", "business_acumen"]
            },
            "devops_engineer": {
                "core_rounds": ["technical_assessment", "system_design", "troubleshooting", "behavioral"],
                "optional_rounds": ["security_assessment", "automation_design", "leadership"],
                "total_duration_range": (180, 300),  # 3-5 hours
                "required_competencies": ["infrastructure", "automation", "problem_solving"]
            },
            "engineering_manager": {
                "core_rounds": ["leadership_assessment", "technical_background", "people_management", "behavioral"],
                "optional_rounds": ["strategic_thinking", "hiring_assessment", "culture_building"],
                "total_duration_range": (240, 360),  # 4-6 hours
                "required_competencies": ["people_leadership", "technical_understanding", "strategic_thinking"]
            }
        }
    
    def _init_interviewer_skills(self) -> Dict[str, Dict]:
        """Initialize interviewer skill requirements for different round types."""
        return {
            "technical_phone_screen": {
                "required_skills": ["technical_assessment", "coding_evaluation"],
                "preferred_experience": ["same_domain", "senior_level"],
                "calibration_level": "standard"
            },
            "coding_deep_dive": {
                "required_skills": ["advanced_technical", "code_quality_assessment"],
                "preferred_experience": ["senior_engineer", "system_design"],
                "calibration_level": "high"
            },
            "system_design": {
                "required_skills": ["architecture_design", "scalability_assessment"],
                "preferred_experience": ["senior_architect", "large_scale_systems"],
                "calibration_level": "high"
            },
            "behavioral": {
                "required_skills": ["behavioral_interviewing", "competency_assessment"],
                "preferred_experience": ["hiring_manager", "people_leadership"],
                "calibration_level": "standard"
            },
            "technical_leadership": {
                "required_skills": ["leadership_assessment", "technical_mentoring"],
                "preferred_experience": ["engineering_manager", "tech_lead"],
                "calibration_level": "high"
            },
            "product_sense": {
                "required_skills": ["product_evaluation", "market_analysis"],
                "preferred_experience": ["product_manager", "product_leadership"],
                "calibration_level": "high"
            },
            "analytical_thinking": {
                "required_skills": ["data_analysis", "metrics_evaluation"],
                "preferred_experience": ["data_analyst", "product_manager"],
                "calibration_level": "standard"
            },
            "design_challenge": {
                "required_skills": ["design_evaluation", "user_experience"],
                "preferred_experience": ["senior_designer", "design_manager"],
                "calibration_level": "high"
            }
        }
    
    def generate_interview_loop(self, role: str, level: str, team: Optional[str] = None, 
                              competencies: Optional[List[str]] = None) -> Dict[str, Any]:
        """Generate a complete interview loop for the specified role and level."""
        
        # Normalize inputs
        role_key = role.lower().replace(" ", "_").replace("-", "_")
        level_key = level.lower()
        
        # Get role template and competency requirements
        if role_key not in self.competency_frameworks:
            role_key = self._find_closest_role(role_key)
        
        if level_key not in self.competency_frameworks[role_key]:
            level_key = self._find_closest_level(role_key, level_key)
        
        competency_req = self.competency_frameworks[role_key][level_key]
        role_template = self.role_templates.get(role_key, self.role_templates["software_engineer"])
        
        # Design the interview loop
        rounds = self._design_rounds(role_key, level_key, competency_req, role_template, competencies)
        schedule = self._create_schedule(rounds)
        scorecard = self._generate_scorecard(role_key, level_key, competency_req)
        interviewer_requirements = self._define_interviewer_requirements(rounds)
        
        return {
            "role": role,
            "level": level,
            "team": team,
            "generated_at": datetime.now().isoformat(),
            "total_duration_minutes": sum(round_info["duration_minutes"] for round_info in rounds.values()),
            "total_rounds": len(rounds),
            "rounds": rounds,
            "suggested_schedule": schedule,
            "scorecard_template": scorecard,
            "interviewer_requirements": interviewer_requirements,
            "competency_framework": competency_req,
            "calibration_notes": self._generate_calibration_notes(role_key, level_key)
        }
    
    def _find_closest_role(self, role_key: str) -> str:
        """Find the closest matching role template."""
        role_mappings = {
            "engineer": "software_engineer",
            "developer": "software_engineer",
            "swe": "software_engineer",
            "backend": "software_engineer",
            "frontend": "software_engineer",
            "fullstack": "software_engineer",
            "pm": "product_manager",
            "product": "product_manager",
            "ux": "designer",
            "ui": "designer",
            "graphic": "designer",
            "data": "data_scientist",
            "analyst": "data_scientist",
            "ml": "data_scientist",
            "ops": "devops_engineer",
            "sre": "devops_engineer",
            "infrastructure": "devops_engineer",
            "manager": "engineering_manager",
            "lead": "engineering_manager"
        }
        
        for key_part in role_key.split("_"):
            if key_part in role_mappings:
                return role_mappings[key_part]
        
        return "software_engineer"  # Default fallback
    
    def _find_closest_level(self, role_key: str, level_key: str) -> str:
        """Find the closest matching level for the role."""
        available_levels = list(self.competency_frameworks[role_key].keys())
        
        level_mappings = {
            "entry": "junior",
            "associate": "junior", 
            "jr": "junior",
            "mid": "mid",
            "middle": "mid",
            "sr": "senior",
            "senior": "senior",
            "staff": "staff",
            "principal": "principal",
            "lead": "senior",
            "manager": "senior"
        }
        
        mapped_level = level_mappings.get(level_key, level_key)
        
        if mapped_level in available_levels:
            return mapped_level
        elif "senior" in available_levels:
            return "senior"
        else:
            return available_levels[0]
    
    def _design_rounds(self, role_key: str, level_key: str, competency_req: Dict, 
                      role_template: Dict, custom_competencies: Optional[List[str]]) -> Dict[str, Dict]:
        """Design the specific interview rounds based on role and level."""
        rounds = {}
        
        # Determine which rounds to include
        core_rounds = role_template["core_rounds"].copy()
        optional_rounds = role_template["optional_rounds"].copy()
        
        # Add optional rounds based on level
        if level_key in ["senior", "staff", "principal"]:
            if "technical_leadership" in optional_rounds and role_key in ["software_engineer", "engineering_manager"]:
                core_rounds.append("technical_leadership")
            if "strategic_thinking" in optional_rounds and role_key in ["product_manager", "engineering_manager"]:
                core_rounds.append("strategic_thinking")
            if "design_system_thinking" in optional_rounds and role_key == "designer":
                core_rounds.append("design_system_thinking")
        
        if level_key in ["staff", "principal"]:
            if "domain_expertise" in optional_rounds:
                core_rounds.append("domain_expertise")
        
        # Define round details
        round_definitions = self._get_round_definitions()
        
        for i, round_type in enumerate(core_rounds, 1):
            if round_type in round_definitions:
                round_def = round_definitions[round_type].copy()
                round_def["order"] = i
                round_def["focus_areas"] = self._customize_focus_areas(round_type, competency_req, custom_competencies)
                rounds[f"round_{i}_{round_type}"] = round_def
        
        return rounds
    
    def _get_round_definitions(self) -> Dict[str, Dict]:
        """Get predefined round definitions with standard durations and formats."""
        return {
            "technical_phone_screen": {
                "name": "Technical Phone Screen",
                "duration_minutes": 45,
                "format": "virtual",
                "objectives": ["Assess coding fundamentals", "Evaluate problem-solving approach", "Screen for basic technical competency"],
                "question_types": ["coding_problems", "technical_concepts", "experience_questions"],
                "evaluation_criteria": ["technical_accuracy", "problem_solving_process", "communication_clarity"]
            },
            "coding_deep_dive": {
                "name": "Coding Deep Dive",
                "duration_minutes": 75,
                "format": "in_person_or_virtual",
                "objectives": ["Evaluate coding skills in depth", "Assess code quality and testing", "Review debugging approach"],
                "question_types": ["complex_coding_problems", "code_review", "testing_strategy"],
                "evaluation_criteria": ["code_quality", "testing_approach", "debugging_skills", "optimization_thinking"]
            },
            "system_design": {
                "name": "System Design",
                "duration_minutes": 75,
                "format": "collaborative_whiteboard",
                "objectives": ["Assess architectural thinking", "Evaluate scalability considerations", "Review trade-off analysis"],
                "question_types": ["system_architecture", "scalability_design", "trade_off_analysis"],
                "evaluation_criteria": ["architectural_thinking", "scalability_awareness", "trade_off_reasoning"]
            },
            "behavioral": {
                "name": "Behavioral Interview",
                "duration_minutes": 45,
                "format": "conversational",
                "objectives": ["Assess cultural fit", "Evaluate past experiences", "Review leadership examples"],
                "question_types": ["star_method_questions", "situational_scenarios", "values_alignment"],
                "evaluation_criteria": ["communication_skills", "leadership_examples", "cultural_alignment"]
            },
            "technical_leadership": {
                "name": "Technical Leadership",
                "duration_minutes": 60,
                "format": "discussion_based",
                "objectives": ["Evaluate mentoring capability", "Assess technical decision making", "Review cross-team collaboration"],
                "question_types": ["leadership_scenarios", "technical_decisions", "mentoring_examples"],
                "evaluation_criteria": ["leadership_potential", "technical_judgment", "influence_skills"]
            },
            "product_sense": {
                "name": "Product Sense",
                "duration_minutes": 75,
                "format": "case_study",
                "objectives": ["Assess product intuition", "Evaluate user empathy", "Review market understanding"],
                "question_types": ["product_scenarios", "feature_prioritization", "user_journey_analysis"],
                "evaluation_criteria": ["product_intuition", "user_empathy", "analytical_thinking"]
            },
            "analytical_thinking": {
                "name": "Analytical Thinking",
                "duration_minutes": 60,
                "format": "data_analysis",
                "objectives": ["Evaluate data interpretation", "Assess metric design", "Review experiment planning"],
                "question_types": ["data_interpretation", "metric_design", "experiment_analysis"],
                "evaluation_criteria": ["analytical_rigor", "metric_intuition", "experimental_thinking"]
            },
            "design_challenge": {
                "name": "Design Challenge",
                "duration_minutes": 90,
                "format": "hands_on_design",
                "objectives": ["Assess design process", "Evaluate user-centered thinking", "Review iteration approach"],
                "question_types": ["design_problems", "user_research", "design_critique"],
                "evaluation_criteria": ["design_process", "user_focus", "visual_communication"]
            },
            "portfolio_review": {
                "name": "Portfolio Review",
                "duration_minutes": 75,
                "format": "presentation_discussion",
                "objectives": ["Review past work", "Assess design thinking", "Evaluate impact measurement"],
                "question_types": ["portfolio_walkthrough", "design_decisions", "impact_stories"],
                "evaluation_criteria": ["design_quality", "process_thinking", "business_impact"]
            }
        }
    
    def _customize_focus_areas(self, round_type: str, competency_req: Dict, 
                              custom_competencies: Optional[List[str]]) -> List[str]:
        """Customize focus areas based on role competency requirements."""
        base_focus_areas = competency_req.get("focus_areas", [])
        
        round_focus_mapping = {
            "technical_phone_screen": ["coding_fundamentals", "problem_solving"],
            "coding_deep_dive": ["technical_execution", "code_quality"],
            "system_design": ["system_thinking", "architectural_reasoning"],
            "behavioral": ["cultural_fit", "communication", "teamwork"],
            "technical_leadership": ["leadership", "mentoring", "influence"],
            "product_sense": ["product_intuition", "user_empathy"],
            "analytical_thinking": ["data_analysis", "metric_design"],
            "design_challenge": ["design_process", "user_focus"]
        }
        
        focus_areas = round_focus_mapping.get(round_type, [])
        
        # Add custom competencies if specified
        if custom_competencies:
            focus_areas.extend([comp for comp in custom_competencies if comp not in focus_areas])
        
        # Add role-specific focus areas
        focus_areas.extend([area for area in base_focus_areas if area not in focus_areas])
        
        return focus_areas[:5]  # Limit to top 5 focus areas
    
    def _create_schedule(self, rounds: Dict[str, Dict]) -> Dict[str, Any]:
        """Create a suggested interview schedule."""
        sorted_rounds = sorted(rounds.items(), key=lambda x: x[1]["order"])
        
        # Calculate optimal scheduling
        total_duration = sum(round_info["duration_minutes"] for _, round_info in sorted_rounds)
        
        if total_duration <= 240:  # 4 hours or less - single day
            schedule_type = "single_day"
            day_structure = self._create_single_day_schedule(sorted_rounds)
        else:  # Multi-day schedule
            schedule_type = "multi_day"
            day_structure = self._create_multi_day_schedule(sorted_rounds)
        
        return {
            "type": schedule_type,
            "total_duration_minutes": total_duration,
            "recommended_breaks": self._calculate_breaks(total_duration),
            "day_structure": day_structure,
            "logistics_notes": self._generate_logistics_notes(sorted_rounds)
        }
    
    def _create_single_day_schedule(self, rounds: List[Tuple[str, Dict]]) -> Dict[str, Any]:
        """Create a single-day interview schedule."""
        start_time = datetime.strptime("09:00", "%H:%M")
        current_time = start_time
        
        schedule = []
        
        for round_name, round_info in rounds:
            # Add break if needed (after 90 minutes of interviews)
            if schedule and sum(item.get("duration_minutes", 0) for item in schedule if "break" not in item.get("type", "")) >= 90:
                schedule.append({
                    "type": "break",
                    "start_time": current_time.strftime("%H:%M"),
                    "duration_minutes": 15,
                    "end_time": (current_time + timedelta(minutes=15)).strftime("%H:%M")
                })
                current_time += timedelta(minutes=15)
            
            # Add the interview round
            end_time = current_time + timedelta(minutes=round_info["duration_minutes"])
            schedule.append({
                "type": "interview",
                "round_name": round_name,
                "title": round_info["name"],
                "start_time": current_time.strftime("%H:%M"),
                "end_time": end_time.strftime("%H:%M"),
                "duration_minutes": round_info["duration_minutes"],
                "format": round_info["format"]
            })
            current_time = end_time
        
        return {
            "day_1": {
                "date": "TBD",
                "start_time": start_time.strftime("%H:%M"),
                "end_time": current_time.strftime("%H:%M"),
                "rounds": schedule
            }
        }
    
    def _create_multi_day_schedule(self, rounds: List[Tuple[str, Dict]]) -> Dict[str, Any]:
        """Create a multi-day interview schedule."""
        # Split rounds across days (max 4 hours per day)
        max_daily_minutes = 240
        days = {}
        current_day = 1
        current_day_duration = 0
        current_day_rounds = []
        
        for round_name, round_info in rounds:
            duration = round_info["duration_minutes"] + 15  # Add buffer time
            
            if current_day_duration + duration > max_daily_minutes and current_day_rounds:
                # Finalize current day
                days[f"day_{current_day}"] = self._finalize_day_schedule(current_day_rounds)
                current_day += 1
                current_day_duration = 0
                current_day_rounds = []
            
            current_day_rounds.append((round_name, round_info))
            current_day_duration += duration
        
        # Finalize last day
        if current_day_rounds:
            days[f"day_{current_day}"] = self._finalize_day_schedule(current_day_rounds)
        
        return days
    
    def _finalize_day_schedule(self, day_rounds: List[Tuple[str, Dict]]) -> Dict[str, Any]:
        """Finalize the schedule for a specific day."""
        start_time = datetime.strptime("09:00", "%H:%M")
        current_time = start_time
        schedule = []
        
        for round_name, round_info in day_rounds:
            end_time = current_time + timedelta(minutes=round_info["duration_minutes"])
            schedule.append({
                "type": "interview",
                "round_name": round_name,
                "title": round_info["name"],
                "start_time": current_time.strftime("%H:%M"),
                "end_time": end_time.strftime("%H:%M"),
                "duration_minutes": round_info["duration_minutes"],
                "format": round_info["format"]
            })
            current_time = end_time + timedelta(minutes=15)  # 15-min buffer
        
        return {
            "date": "TBD",
            "start_time": start_time.strftime("%H:%M"),
            "end_time": (current_time - timedelta(minutes=15)).strftime("%H:%M"),
            "rounds": schedule
        }
    
    def _calculate_breaks(self, total_duration: int) -> List[Dict[str, Any]]:
        """Calculate recommended breaks based on total duration."""
        breaks = []
        
        if total_duration >= 120:  # 2+ hours
            breaks.append({"type": "short_break", "duration": 15, "after_minutes": 90})
        
        if total_duration >= 240:  # 4+ hours
            breaks.append({"type": "lunch_break", "duration": 60, "after_minutes": 180})
        
        if total_duration >= 360:  # 6+ hours
            breaks.append({"type": "short_break", "duration": 15, "after_minutes": 300})
        
        return breaks
    
    def _generate_scorecard(self, role_key: str, level_key: str, competency_req: Dict) -> Dict[str, Any]:
        """Generate a scorecard template for the interview loop."""
        scoring_dimensions = []
        
        # Add competency-based scoring dimensions
        for competency in competency_req["required"]:
            scoring_dimensions.append({
                "dimension": competency,
                "weight": "high",
                "scale": "1-4",
                "description": f"Assessment of {competency.replace('_', ' ')} competency"
            })
        
        for competency in competency_req.get("preferred", []):
            scoring_dimensions.append({
                "dimension": competency,
                "weight": "medium",
                "scale": "1-4", 
                "description": f"Assessment of {competency.replace('_', ' ')} competency"
            })
        
        # Add standard dimensions
        standard_dimensions = [
            {"dimension": "communication", "weight": "high", "scale": "1-4"},
            {"dimension": "cultural_fit", "weight": "medium", "scale": "1-4"},
            {"dimension": "learning_agility", "weight": "medium", "scale": "1-4"}
        ]
        
        scoring_dimensions.extend(standard_dimensions)
        
        return {
            "scoring_scale": {
                "4": "Exceeds Expectations - Demonstrates mastery beyond required level",
                "3": "Meets Expectations - Solid performance meeting all requirements", 
                "2": "Partially Meets - Shows potential but has development areas",
                "1": "Does Not Meet - Significant gaps in required competencies"
            },
            "dimensions": scoring_dimensions,
            "overall_recommendation": {
                "options": ["Strong Hire", "Hire", "No Hire", "Strong No Hire"],
                "criteria": "Based on weighted average and minimum thresholds"
            },
            "calibration_notes": {
                "required": True,
                "min_length": 100,
                "sections": ["strengths", "areas_for_development", "specific_examples"]
            }
        }
    
    def _define_interviewer_requirements(self, rounds: Dict[str, Dict]) -> Dict[str, Dict]:
        """Define interviewer skill requirements for each round."""
        requirements = {}
        
        for round_name, round_info in rounds.items():
            round_type = round_name.split("_", 2)[-1]  # Extract round type
            
            if round_type in self.interviewer_skills:
                skill_req = self.interviewer_skills[round_type].copy()
                skill_req["suggested_interviewers"] = self._suggest_interviewer_profiles(round_type)
                requirements[round_name] = skill_req
            else:
                # Default requirements
                requirements[round_name] = {
                    "required_skills": ["interviewing_basics", "evaluation_skills"],
                    "preferred_experience": ["relevant_domain"],
                    "calibration_level": "standard",
                    "suggested_interviewers": ["experienced_interviewer"]
                }
        
        return requirements
    
    def _suggest_interviewer_profiles(self, round_type: str) -> List[str]:
        """Suggest specific interviewer profiles for different round types."""
        profile_mapping = {
            "technical_phone_screen": ["senior_engineer", "tech_lead"],
            "coding_deep_dive": ["senior_engineer", "staff_engineer"],
            "system_design": ["senior_architect", "staff_engineer"],
            "behavioral": ["hiring_manager", "people_manager"],
            "technical_leadership": ["engineering_manager", "senior_staff"],
            "product_sense": ["senior_pm", "product_leader"],
            "analytical_thinking": ["senior_analyst", "data_scientist"],
            "design_challenge": ["senior_designer", "design_manager"]
        }
        
        return profile_mapping.get(round_type, ["experienced_interviewer"])
    
    def _generate_calibration_notes(self, role_key: str, level_key: str) -> Dict[str, Any]:
        """Generate calibration notes and best practices."""
        return {
            "hiring_bar_notes": f"Calibrated for {level_key} level {role_key.replace('_', ' ')} role",
            "common_pitfalls": [
                "Avoid comparing candidates to each other rather than to the role standard",
                "Don't let one strong/weak area overshadow overall assessment",
                "Ensure consistent application of evaluation criteria"
            ],
            "calibration_checkpoints": [
                "Review score distribution after every 5 candidates",
                "Conduct monthly interviewer calibration sessions",
                "Track correlation with 6-month performance reviews"
            ],
            "escalation_criteria": [
                "Any candidate receiving all 4s or all 1s",
                "Significant disagreement between interviewers (>1.5 point spread)",
                "Unusual circumstances or accommodations needed"
            ]
        }
    
    def _generate_logistics_notes(self, rounds: List[Tuple[str, Dict]]) -> List[str]:
        """Generate logistics and coordination notes."""
        notes = [
            "Coordinate interviewer availability before scheduling",
            "Ensure all interviewers have access to job description and competency requirements",
            "Prepare interview rooms/virtual links for all rounds",
            "Share candidate resume and application with all interviewers"
        ]
        
        # Add format-specific notes
        formats_used = {round_info["format"] for _, round_info in rounds}
        
        if "virtual" in formats_used:
            notes.append("Test video conferencing setup before virtual interviews")
            notes.append("Share virtual meeting links with candidate 24 hours in advance")
        
        if "collaborative_whiteboard" in formats_used:
            notes.append("Prepare whiteboard or collaborative online tool for design sessions")
        
        if "hands_on_design" in formats_used:
            notes.append("Provide design tools access or ensure candidate can screen share their preferred tools")
        
        return notes


def format_human_readable(loop_data: Dict[str, Any]) -> str:
    """Format the interview loop data in a human-readable format."""
    output = []
    
    # Header
    output.append(f"Interview Loop Design for {loop_data['role']} ({loop_data['level'].title()} Level)")
    output.append("=" * 60)
    
    if loop_data.get('team'):
        output.append(f"Team: {loop_data['team']}")
    
    output.append(f"Generated: {loop_data['generated_at']}")
    output.append(f"Total Duration: {loop_data['total_duration_minutes']} minutes ({loop_data['total_duration_minutes']//60}h {loop_data['total_duration_minutes']%60}m)")
    output.append(f"Total Rounds: {loop_data['total_rounds']}")
    output.append("")
    
    # Interview Rounds
    output.append("INTERVIEW ROUNDS")
    output.append("-" * 40)
    
    sorted_rounds = sorted(loop_data['rounds'].items(), key=lambda x: x[1]['order'])
    for round_name, round_info in sorted_rounds:
        output.append(f"\nRound {round_info['order']}: {round_info['name']}")
        output.append(f"Duration: {round_info['duration_minutes']} minutes")
        output.append(f"Format: {round_info['format'].replace('_', ' ').title()}")
        
        output.append("Objectives:")
        for obj in round_info['objectives']:
            output.append(f"  • {obj}")
        
        output.append("Focus Areas:")
        for area in round_info['focus_areas']:
            output.append(f"  • {area.replace('_', ' ').title()}")
    
    # Suggested Schedule
    output.append("\nSUGGESTED SCHEDULE")
    output.append("-" * 40)
    
    schedule = loop_data['suggested_schedule']
    output.append(f"Schedule Type: {schedule['type'].replace('_', ' ').title()}")
    
    for day_name, day_info in schedule['day_structure'].items():
        output.append(f"\n{day_name.replace('_', ' ').title()}:")
        output.append(f"Time: {day_info['start_time']} - {day_info['end_time']}")
        
        for item in day_info['rounds']:
            if item['type'] == 'interview':
                output.append(f"  {item['start_time']}-{item['end_time']}: {item['title']} ({item['duration_minutes']}min)")
            else:
                output.append(f"  {item['start_time']}-{item['end_time']}: {item['type'].title()} ({item['duration_minutes']}min)")
    
    # Interviewer Requirements
    output.append("\nINTERVIEWER REQUIREMENTS")
    output.append("-" * 40)
    
    for round_name, requirements in loop_data['interviewer_requirements'].items():
        round_display = round_name.split("_", 2)[-1].replace("_", " ").title()
        output.append(f"\n{round_display}:")
        output.append(f"Required Skills: {', '.join(requirements['required_skills'])}")
        output.append(f"Suggested Interviewers: {', '.join(requirements['suggested_interviewers'])}")
        output.append(f"Calibration Level: {requirements['calibration_level'].title()}")
    
    # Scorecard Overview
    output.append("\nSCORECARD TEMPLATE")
    output.append("-" * 40)
    
    scorecard = loop_data['scorecard_template']
    output.append("Scoring Scale:")
    for score, description in scorecard['scoring_scale'].items():
        output.append(f"  {score}: {description}")
    
    output.append("\nEvaluation Dimensions:")
    for dim in scorecard['dimensions']:
        output.append(f"  • {dim['dimension'].replace('_', ' ').title()} (Weight: {dim['weight']})")
    
    # Calibration Notes
    output.append("\nCALIBRATION NOTES")
    output.append("-" * 40)
    
    calibration = loop_data['calibration_notes']
    output.append(f"Hiring Bar: {calibration['hiring_bar_notes']}")
    
    output.append("\nCommon Pitfalls:")
    for pitfall in calibration['common_pitfalls']:
        output.append(f"  • {pitfall}")
    
    return "\n".join(output)


def main():
    parser = argparse.ArgumentParser(description="Generate calibrated interview loops for specific roles and levels")
    parser.add_argument("--role", type=str, help="Job role title (e.g., 'Senior Software Engineer')")
    parser.add_argument("--level", type=str, help="Experience level (junior, mid, senior, staff, principal)")
    parser.add_argument("--team", type=str, help="Team or department (optional)")
    parser.add_argument("--competencies", type=str, help="Comma-separated list of specific competencies to focus on")
    parser.add_argument("--input", type=str, help="Input JSON file with role definition")
    parser.add_argument("--output", type=str, help="Output directory or file path")
    parser.add_argument("--format", choices=["json", "text", "both"], default="both", help="Output format")
    
    args = parser.parse_args()
    
    designer = InterviewLoopDesigner()
    
    # Handle input
    if args.input:
        try:
            with open(args.input, 'r') as f:
                role_data = json.load(f)
            role = role_data.get('role') or role_data.get('title', '')
            level = role_data.get('level', 'senior')
            team = role_data.get('team')
            competencies = role_data.get('competencies')
        except Exception as e:
            print(f"Error reading input file: {e}")
            sys.exit(1)
    else:
        if not args.role or not args.level:
            print("Error: --role and --level are required when not using --input")
            sys.exit(1)
        
        role = args.role
        level = args.level
        team = args.team
        competencies = args.competencies.split(',') if args.competencies else None
    
    # Generate interview loop
    try:
        loop_data = designer.generate_interview_loop(role, level, team, competencies)
        
        # Handle output
        if args.output:
            output_path = args.output
            if os.path.isdir(output_path):
                safe_role = "".join(c for c in role.lower() if c.isalnum() or c in (' ', '-', '_')).replace(' ', '_')
                base_filename = f"{safe_role}_{level}_interview_loop"
                json_path = os.path.join(output_path, f"{base_filename}.json")
                text_path = os.path.join(output_path, f"{base_filename}.txt")
            else:
                # Use provided path as base
                json_path = output_path if output_path.endswith('.json') else f"{output_path}.json"
                text_path = output_path.replace('.json', '.txt') if output_path.endswith('.json') else f"{output_path}.txt"
        else:
            safe_role = "".join(c for c in role.lower() if c.isalnum() or c in (' ', '-', '_')).replace(' ', '_')
            base_filename = f"{safe_role}_{level}_interview_loop"
            json_path = f"{base_filename}.json"
            text_path = f"{base_filename}.txt"
        
        # Write outputs
        if args.format in ["json", "both"]:
            with open(json_path, 'w') as f:
                json.dump(loop_data, f, indent=2, default=str)
            print(f"JSON output written to: {json_path}")
        
        if args.format in ["text", "both"]:
            with open(text_path, 'w') as f:
                f.write(format_human_readable(loop_data))
            print(f"Text output written to: {text_path}")
        
        # Always print summary to stdout
        print("\nInterview Loop Summary:")
        print(f"Role: {loop_data['role']} ({loop_data['level'].title()})")
        print(f"Total Duration: {loop_data['total_duration_minutes']} minutes")
        print(f"Number of Rounds: {loop_data['total_rounds']}")
        print(f"Schedule Type: {loop_data['suggested_schedule']['type'].replace('_', ' ').title()}")
        
    except Exception as e:
        print(f"Error generating interview loop: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()