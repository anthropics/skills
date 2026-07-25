#!/usr/bin/env python3
"""
Question Bank Generator

Generates comprehensive, competency-based interview questions with detailed scoring criteria.
Creates structured question banks organized by competency area with scoring rubrics, 
follow-up probes, and calibration examples.

Usage:
    python question_bank_generator.py --role "Frontend Engineer" --competencies react,typescript,system-design
    python question_bank_generator.py --role "Product Manager" --question-types behavioral,leadership
    python question_bank_generator.py --input role_requirements.json --output questions/
"""

import os
import sys
import json
import argparse
import random
from datetime import datetime
from typing import Dict, List, Optional, Any, Tuple
from collections import defaultdict


class QuestionBankGenerator:
    """Generates comprehensive interview question banks with scoring criteria."""
    
    def __init__(self):
        self.technical_questions = self._init_technical_questions()
        self.behavioral_questions = self._init_behavioral_questions()
        self.competency_mapping = self._init_competency_mapping()
        self.scoring_rubrics = self._init_scoring_rubrics()
        self.follow_up_strategies = self._init_follow_up_strategies()
        
    def _init_technical_questions(self) -> Dict[str, Dict]:
        """Initialize technical questions by competency area and level."""
        return {
            "coding_fundamentals": {
                "junior": [
                    {
                        "question": "Write a function to reverse a string without using built-in reverse methods.",
                        "competency": "coding_fundamentals",
                        "type": "coding",
                        "difficulty": "easy",
                        "time_limit": 15,
                        "key_concepts": ["loops", "string_manipulation", "basic_algorithms"]
                    },
                    {
                        "question": "Implement a function to check if a string is a palindrome.",
                        "competency": "coding_fundamentals", 
                        "type": "coding",
                        "difficulty": "easy",
                        "time_limit": 15,
                        "key_concepts": ["string_processing", "comparison", "edge_cases"]
                    },
                    {
                        "question": "Find the largest element in an array without using built-in max functions.",
                        "competency": "coding_fundamentals",
                        "type": "coding", 
                        "difficulty": "easy",
                        "time_limit": 10,
                        "key_concepts": ["arrays", "iteration", "comparison"]
                    }
                ],
                "mid": [
                    {
                        "question": "Implement a function to find the first non-repeating character in a string.",
                        "competency": "coding_fundamentals",
                        "type": "coding",
                        "difficulty": "medium",
                        "time_limit": 20,
                        "key_concepts": ["hash_maps", "string_processing", "efficiency"]
                    },
                    {
                        "question": "Write a function to merge two sorted arrays into one sorted array.",
                        "competency": "coding_fundamentals",
                        "type": "coding",
                        "difficulty": "medium", 
                        "time_limit": 25,
                        "key_concepts": ["merge_algorithms", "two_pointers", "optimization"]
                    }
                ],
                "senior": [
                    {
                        "question": "Implement a LRU (Least Recently Used) cache with O(1) operations.",
                        "competency": "coding_fundamentals",
                        "type": "coding",
                        "difficulty": "hard",
                        "time_limit": 35,
                        "key_concepts": ["data_structures", "hash_maps", "doubly_linked_lists"]
                    }
                ]
            },
            "system_design": {
                "mid": [
                    {
                        "question": "Design a URL shortener service like bit.ly for 10K users.",
                        "competency": "system_design",
                        "type": "design",
                        "difficulty": "medium",
                        "time_limit": 45,
                        "key_concepts": ["database_design", "hashing", "basic_scalability"]
                    }
                ],
                "senior": [
                    {
                        "question": "Design a real-time chat system supporting 1M concurrent users.",
                        "competency": "system_design",
                        "type": "design",
                        "difficulty": "hard",
                        "time_limit": 60,
                        "key_concepts": ["websockets", "load_balancing", "database_sharding", "caching"]
                    },
                    {
                        "question": "Design a distributed cache system like Redis with high availability.",
                        "competency": "system_design",
                        "type": "design",
                        "difficulty": "hard",
                        "time_limit": 60,
                        "key_concepts": ["distributed_systems", "replication", "consistency", "partitioning"]
                    }
                ],
                "staff": [
                    {
                        "question": "Design the architecture for a global content delivery network (CDN).",
                        "competency": "system_design",
                        "type": "design",
                        "difficulty": "expert",
                        "time_limit": 75,
                        "key_concepts": ["global_architecture", "edge_computing", "content_optimization", "network_protocols"]
                    }
                ]
            },
            "frontend_development": {
                "junior": [
                    {
                        "question": "Create a responsive navigation menu using HTML, CSS, and vanilla JavaScript.",
                        "competency": "frontend_development",
                        "type": "coding",
                        "difficulty": "easy",
                        "time_limit": 30,
                        "key_concepts": ["html_css", "responsive_design", "dom_manipulation"]
                    }
                ],
                "mid": [
                    {
                        "question": "Build a React component that fetches and displays paginated data from an API.",
                        "competency": "frontend_development",
                        "type": "coding",
                        "difficulty": "medium",
                        "time_limit": 45,
                        "key_concepts": ["react_hooks", "api_integration", "state_management", "pagination"]
                    }
                ],
                "senior": [
                    {
                        "question": "Design and implement a custom React hook for managing complex form state with validation.",
                        "competency": "frontend_development",
                        "type": "coding",
                        "difficulty": "hard",
                        "time_limit": 60,
                        "key_concepts": ["custom_hooks", "form_validation", "state_management", "performance"]
                    }
                ]
            },
            "data_analysis": {
                "junior": [
                    {
                        "question": "Given a dataset of user activities, calculate the daily active users for the past month.",
                        "competency": "data_analysis",
                        "type": "analytical",
                        "difficulty": "easy",
                        "time_limit": 30,
                        "key_concepts": ["sql_basics", "date_functions", "aggregation"]
                    }
                ],
                "mid": [
                    {
                        "question": "Analyze conversion funnel data to identify the biggest drop-off point and propose solutions.",
                        "competency": "data_analysis", 
                        "type": "analytical",
                        "difficulty": "medium",
                        "time_limit": 45,
                        "key_concepts": ["funnel_analysis", "conversion_optimization", "statistical_significance"]
                    }
                ],
                "senior": [
                    {
                        "question": "Design an A/B testing framework to measure the impact of a new recommendation algorithm.",
                        "competency": "data_analysis",
                        "type": "analytical",
                        "difficulty": "hard", 
                        "time_limit": 60,
                        "key_concepts": ["experiment_design", "statistical_power", "bias_mitigation", "causal_inference"]
                    }
                ]
            },
            "machine_learning": {
                "mid": [
                    {
                        "question": "Explain how you would build a recommendation system for an e-commerce platform.",
                        "competency": "machine_learning",
                        "type": "conceptual",
                        "difficulty": "medium",
                        "time_limit": 45,
                        "key_concepts": ["collaborative_filtering", "content_based", "cold_start", "evaluation_metrics"]
                    }
                ],
                "senior": [
                    {
                        "question": "Design a real-time fraud detection system for financial transactions.",
                        "competency": "machine_learning",
                        "type": "design",
                        "difficulty": "hard",
                        "time_limit": 60,
                        "key_concepts": ["anomaly_detection", "real_time_ml", "feature_engineering", "model_monitoring"]
                    }
                ]
            },
            "product_strategy": {
                "mid": [
                    {
                        "question": "How would you prioritize features for a mobile app with limited engineering resources?",
                        "competency": "product_strategy",
                        "type": "case_study",
                        "difficulty": "medium",
                        "time_limit": 45,
                        "key_concepts": ["prioritization_frameworks", "resource_allocation", "impact_estimation"]
                    }
                ],
                "senior": [
                    {
                        "question": "Design a go-to-market strategy for a new B2B SaaS product entering a competitive market.",
                        "competency": "product_strategy",
                        "type": "strategic",
                        "difficulty": "hard",
                        "time_limit": 60,
                        "key_concepts": ["market_analysis", "competitive_positioning", "pricing_strategy", "channel_strategy"]
                    }
                ]
            }
        }
    
    def _init_behavioral_questions(self) -> Dict[str, List[Dict]]:
        """Initialize behavioral questions by competency area."""
        return {
            "leadership": [
                {
                    "question": "Tell me about a time when you had to lead a team through a significant change or challenge.",
                    "competency": "leadership",
                    "type": "behavioral",
                    "method": "STAR",
                    "focus_areas": ["change_management", "team_motivation", "communication"]
                },
                {
                    "question": "Describe a situation where you had to influence someone without having direct authority over them.",
                    "competency": "leadership", 
                    "type": "behavioral",
                    "method": "STAR",
                    "focus_areas": ["influence", "persuasion", "stakeholder_management"]
                },
                {
                    "question": "Give me an example of when you had to make a difficult decision that affected your team.",
                    "competency": "leadership",
                    "type": "behavioral", 
                    "method": "STAR",
                    "focus_areas": ["decision_making", "team_impact", "communication"]
                }
            ],
            "collaboration": [
                {
                    "question": "Describe a time when you had to work with a difficult colleague or stakeholder.",
                    "competency": "collaboration",
                    "type": "behavioral",
                    "method": "STAR", 
                    "focus_areas": ["conflict_resolution", "relationship_building", "professionalism"]
                },
                {
                    "question": "Tell me about a project where you had to coordinate across multiple teams or departments.",
                    "competency": "collaboration",
                    "type": "behavioral",
                    "method": "STAR",
                    "focus_areas": ["cross_functional_work", "communication", "project_coordination"]
                }
            ],
            "problem_solving": [
                {
                    "question": "Walk me through a complex problem you solved recently. What was your approach?",
                    "competency": "problem_solving",
                    "type": "behavioral",
                    "method": "STAR",
                    "focus_areas": ["analytical_thinking", "methodology", "creativity"]
                },
                {
                    "question": "Describe a time when you had to solve a problem with limited information or resources.",
                    "competency": "problem_solving",
                    "type": "behavioral",
                    "method": "STAR", 
                    "focus_areas": ["resourcefulness", "ambiguity_tolerance", "decision_making"]
                }
            ],
            "communication": [
                {
                    "question": "Tell me about a time when you had to present complex technical information to a non-technical audience.",
                    "competency": "communication",
                    "type": "behavioral",
                    "method": "STAR",
                    "focus_areas": ["technical_communication", "audience_adaptation", "clarity"]
                },
                {
                    "question": "Describe a situation where you had to deliver difficult feedback to a colleague.",
                    "competency": "communication",
                    "type": "behavioral", 
                    "method": "STAR",
                    "focus_areas": ["feedback_delivery", "empathy", "constructive_criticism"]
                }
            ],
            "adaptability": [
                {
                    "question": "Tell me about a time when you had to quickly learn a new technology or skill for work.",
                    "competency": "adaptability",
                    "type": "behavioral",
                    "method": "STAR",
                    "focus_areas": ["learning_agility", "growth_mindset", "knowledge_acquisition"]
                },
                {
                    "question": "Describe how you handled a situation when project requirements changed significantly mid-way.",
                    "competency": "adaptability",
                    "type": "behavioral",
                    "method": "STAR",
                    "focus_areas": ["flexibility", "change_management", "resilience"]
                }
            ],
            "innovation": [
                {
                    "question": "Tell me about a time when you came up with a creative solution to improve a process or solve a problem.",
                    "competency": "innovation", 
                    "type": "behavioral",
                    "method": "STAR",
                    "focus_areas": ["creative_thinking", "process_improvement", "initiative"]
                }
            ]
        }
    
    def _init_competency_mapping(self) -> Dict[str, Dict]:
        """Initialize role to competency mapping."""
        return {
            "software_engineer": {
                "core_competencies": ["coding_fundamentals", "system_design", "problem_solving", "collaboration"],
                "level_specific": {
                    "junior": ["coding_fundamentals", "debugging", "learning_agility"],
                    "mid": ["advanced_coding", "system_design", "mentoring_basics"], 
                    "senior": ["system_architecture", "technical_leadership", "innovation"],
                    "staff": ["architectural_vision", "organizational_impact", "strategic_thinking"]
                }
            },
            "frontend_engineer": {
                "core_competencies": ["frontend_development", "ui_ux_understanding", "problem_solving", "collaboration"],
                "level_specific": {
                    "junior": ["html_css_js", "responsive_design", "basic_frameworks"],
                    "mid": ["react_vue_angular", "state_management", "performance_optimization"],
                    "senior": ["frontend_architecture", "team_leadership", "cross_functional_collaboration"],
                    "staff": ["frontend_strategy", "technology_evaluation", "organizational_impact"]
                }
            },
            "backend_engineer": {
                "core_competencies": ["backend_development", "database_design", "api_design", "system_design"],
                "level_specific": {
                    "junior": ["server_side_programming", "database_basics", "api_consumption"],
                    "mid": ["microservices", "caching", "security_basics"],
                    "senior": ["distributed_systems", "performance_optimization", "technical_leadership"],
                    "staff": ["system_architecture", "technology_strategy", "cross_team_influence"]
                }
            },
            "product_manager": {
                "core_competencies": ["product_strategy", "user_research", "data_analysis", "stakeholder_management"],
                "level_specific": {
                    "junior": ["feature_specification", "user_stories", "basic_analytics"],
                    "mid": ["product_roadmap", "cross_functional_leadership", "market_research"],
                    "senior": ["business_strategy", "team_leadership", "p&l_responsibility"],
                    "staff": ["portfolio_management", "organizational_strategy", "market_creation"]
                }
            },
            "data_scientist": {
                "core_competencies": ["statistical_analysis", "machine_learning", "data_analysis", "business_acumen"],
                "level_specific": {
                    "junior": ["python_r", "sql", "basic_ml", "data_visualization"],
                    "mid": ["advanced_ml", "experiment_design", "model_evaluation"],
                    "senior": ["ml_systems", "data_strategy", "stakeholder_communication"],
                    "staff": ["data_platform", "ai_strategy", "organizational_impact"]
                }
            },
            "designer": {
                "core_competencies": ["design_process", "user_research", "visual_design", "collaboration"],
                "level_specific": {
                    "junior": ["design_tools", "user_empathy", "visual_communication"],
                    "mid": ["design_systems", "user_testing", "cross_functional_work"],
                    "senior": ["design_strategy", "team_leadership", "business_impact"],
                    "staff": ["design_vision", "organizational_design", "strategic_influence"]
                }
            },
            "devops_engineer": {
                "core_competencies": ["infrastructure", "automation", "monitoring", "troubleshooting"],
                "level_specific": {
                    "junior": ["scripting", "basic_cloud", "ci_cd_basics"],
                    "mid": ["infrastructure_as_code", "container_orchestration", "security"],
                    "senior": ["platform_design", "reliability_engineering", "team_leadership"],
                    "staff": ["platform_strategy", "organizational_infrastructure", "technology_vision"]
                }
            }
        }
    
    def _init_scoring_rubrics(self) -> Dict[str, Dict]:
        """Initialize scoring rubrics for different question types."""
        return {
            "coding": {
                "correctness": {
                    "4": "Solution is completely correct, handles all edge cases, optimal complexity",
                    "3": "Solution is correct for main cases, good complexity, minor edge case issues",
                    "2": "Solution works but has some bugs or suboptimal approach",
                    "1": "Solution has significant issues or doesn't work"
                },
                "code_quality": {
                    "4": "Clean, readable, well-structured code with excellent naming and comments",
                    "3": "Good code structure, readable with appropriate naming",
                    "2": "Code works but has style/structure issues",
                    "1": "Poor code quality, hard to understand"
                },
                "problem_solving_approach": {
                    "4": "Excellent problem breakdown, clear thinking process, considers alternatives",
                    "3": "Good approach, logical thinking, systematic problem solving",
                    "2": "Decent approach but some confusion or inefficiency",
                    "1": "Poor approach, unclear thinking process"
                },
                "communication": {
                    "4": "Excellent explanation of approach, asks clarifying questions, clear reasoning",
                    "3": "Good communication, explains thinking well",
                    "2": "Adequate communication, some explanation",
                    "1": "Poor communication, little explanation"
                }
            },
            "behavioral": {
                "situation_clarity": {
                    "4": "Clear, specific situation with relevant context and stakes",
                    "3": "Good situation description with adequate context",
                    "2": "Situation described but lacks some specifics",
                    "1": "Vague or unclear situation description"
                },
                "action_quality": {
                    "4": "Specific, thoughtful actions showing strong competency",
                    "3": "Good actions demonstrating competency",
                    "2": "Adequate actions but could be stronger",
                    "1": "Weak or inappropriate actions"
                },
                "result_impact": {
                    "4": "Significant positive impact with measurable results",
                    "3": "Good positive impact with clear outcomes",
                    "2": "Some positive impact demonstrated",
                    "1": "Little or no positive impact shown"
                },
                "self_awareness": {
                    "4": "Excellent self-reflection, learns from experience, acknowledges growth areas",
                    "3": "Good self-awareness and learning orientation",
                    "2": "Some self-reflection demonstrated",
                    "1": "Limited self-awareness or reflection"
                }
            },
            "design": {
                "system_thinking": {
                    "4": "Comprehensive system view, considers all components and interactions",
                    "3": "Good system understanding with most components identified",
                    "2": "Basic system thinking with some gaps",
                    "1": "Limited system thinking, misses key components"
                },
                "scalability": {
                    "4": "Excellent scalability considerations, multiple strategies discussed",
                    "3": "Good scalability awareness with practical solutions",
                    "2": "Basic scalability understanding",
                    "1": "Little to no scalability consideration"
                },
                "trade_offs": {
                    "4": "Excellent trade-off analysis, considers multiple dimensions",
                    "3": "Good trade-off awareness with clear reasoning",
                    "2": "Some trade-off consideration",
                    "1": "Limited trade-off analysis"
                },
                "technical_depth": {
                    "4": "Deep technical knowledge with implementation details",
                    "3": "Good technical knowledge with solid understanding",
                    "2": "Adequate technical knowledge",
                    "1": "Limited technical depth"
                }
            }
        }
    
    def _init_follow_up_strategies(self) -> Dict[str, List[str]]:
        """Initialize follow-up question strategies by competency."""
        return {
            "coding_fundamentals": [
                "How would you optimize this solution for better time complexity?",
                "What edge cases should we consider for this problem?",
                "How would you test this function?",
                "What would happen if the input size was very large?"
            ],
            "system_design": [
                "How would you handle if the system needed to scale 10x?",
                "What would you do if one of your services went down?",
                "How would you monitor this system in production?",
                "What security considerations would you implement?"
            ],
            "leadership": [
                "What would you do differently if you faced this situation again?",
                "How did you handle team members who were resistant to the change?",
                "What metrics did you use to measure success?",
                "How did you communicate progress to stakeholders?"
            ],
            "problem_solving": [
                "Walk me through your thought process step by step",
                "What alternative approaches did you consider?",
                "How did you validate your solution worked?",
                "What did you learn from this experience?"
            ],
            "collaboration": [
                "How did you build consensus among the different stakeholders?",
                "What communication channels did you use to keep everyone aligned?",
                "How did you handle disagreements or conflicts?",
                "What would you do to improve collaboration in the future?"
            ]
        }
    
    def generate_question_bank(self, role: str, level: str = "senior", 
                              competencies: Optional[List[str]] = None,
                              question_types: Optional[List[str]] = None,
                              num_questions: int = 20) -> Dict[str, Any]:
        """Generate a comprehensive question bank for the specified role and competencies."""
        
        # Normalize inputs
        role_key = self._normalize_role(role)
        level_key = level.lower()
        
        # Get competency requirements
        role_competencies = self._get_role_competencies(role_key, level_key, competencies)
        
        # Determine question types to include
        if question_types is None:
            question_types = ["technical", "behavioral", "situational"]
        
        # Generate questions
        questions = self._generate_questions(role_competencies, question_types, level_key, num_questions)
        
        # Create scoring rubrics
        scoring_rubrics = self._create_scoring_rubrics(questions)
        
        # Generate follow-up probes
        follow_up_probes = self._generate_follow_up_probes(questions)
        
        # Create calibration examples
        calibration_examples = self._create_calibration_examples(questions[:5])  # Sample for first 5 questions
        
        return {
            "role": role,
            "level": level,
            "competencies": role_competencies,
            "question_types": question_types,
            "generated_at": datetime.now().isoformat(),
            "total_questions": len(questions),
            "questions": questions,
            "scoring_rubrics": scoring_rubrics,
            "follow_up_probes": follow_up_probes,
            "calibration_examples": calibration_examples,
            "usage_guidelines": self._generate_usage_guidelines(role_key, level_key)
        }
    
    def _normalize_role(self, role: str) -> str:
        """Normalize role name to match competency mapping keys."""
        role_lower = role.lower().replace(" ", "_").replace("-", "_")
        
        # Map variations to standard roles
        role_mappings = {
            "software_engineer": ["engineer", "developer", "swe", "software_developer"],
            "frontend_engineer": ["frontend", "front_end", "ui_engineer", "web_developer"],
            "backend_engineer": ["backend", "back_end", "server_engineer", "api_developer"],
            "product_manager": ["pm", "product", "product_owner", "po"],
            "data_scientist": ["ds", "data", "analyst", "ml_engineer"],
            "designer": ["ux", "ui", "ux_ui", "product_designer", "visual_designer"],
            "devops_engineer": ["devops", "sre", "platform_engineer", "infrastructure"]
        }
        
        for standard_role, variations in role_mappings.items():
            if any(var in role_lower for var in variations):
                return standard_role
        
        # Default fallback
        return "software_engineer"
    
    def _get_role_competencies(self, role_key: str, level_key: str, 
                              custom_competencies: Optional[List[str]]) -> List[str]:
        """Get competencies for the role and level."""
        if role_key not in self.competency_mapping:
            role_key = "software_engineer"
        
        role_mapping = self.competency_mapping[role_key]
        competencies = role_mapping["core_competencies"].copy()
        
        # Add level-specific competencies
        if level_key in role_mapping["level_specific"]:
            competencies.extend(role_mapping["level_specific"][level_key])
        elif "senior" in role_mapping["level_specific"]:
            competencies.extend(role_mapping["level_specific"]["senior"])
        
        # Add custom competencies if specified
        if custom_competencies:
            competencies.extend([comp.strip() for comp in custom_competencies if comp.strip() not in competencies])
        
        return list(set(competencies))  # Remove duplicates
    
    def _generate_questions(self, competencies: List[str], question_types: List[str], 
                           level: str, num_questions: int) -> List[Dict[str, Any]]:
        """Generate questions based on competencies and types."""
        questions = []
        questions_per_competency = max(1, num_questions // len(competencies))
        
        for competency in competencies:
            competency_questions = []
            
            # Add technical questions if requested and available
            if "technical" in question_types and competency in self.technical_questions:
                tech_questions = []
                
                # Get questions for current level and below
                level_order = ["junior", "mid", "senior", "staff", "principal"]
                current_level_idx = level_order.index(level) if level in level_order else 2
                
                for lvl_idx in range(current_level_idx + 1):
                    lvl = level_order[lvl_idx]
                    if lvl in self.technical_questions[competency]:
                        tech_questions.extend(self.technical_questions[competency][lvl])
                
                competency_questions.extend(tech_questions[:questions_per_competency])
            
            # Add behavioral questions if requested
            if "behavioral" in question_types and competency in self.behavioral_questions:
                behavioral_q = self.behavioral_questions[competency][:questions_per_competency]
                competency_questions.extend(behavioral_q)
            
            # Add situational questions (variations of behavioral)
            if "situational" in question_types:
                situational_q = self._generate_situational_questions(competency, questions_per_competency)
                competency_questions.extend(situational_q)
            
            # Ensure we have enough questions for this competency
            while len(competency_questions) < questions_per_competency:
                competency_questions.extend(self._generate_fallback_questions(competency, level))
                if len(competency_questions) >= questions_per_competency:
                    break
            
            questions.extend(competency_questions[:questions_per_competency])
        
        # Shuffle and limit to requested number
        random.shuffle(questions)
        return questions[:num_questions]
    
    def _generate_situational_questions(self, competency: str, count: int) -> List[Dict[str, Any]]:
        """Generate situational questions for a competency."""
        situational_templates = {
            "leadership": [
                {
                    "question": "You're leading a project that's behind schedule and the client is unhappy. How do you handle this situation?",
                    "competency": competency,
                    "type": "situational",
                    "focus_areas": ["crisis_management", "client_communication", "team_leadership"]
                }
            ],
            "collaboration": [
                {
                    "question": "You're working on a cross-functional project and two team members have opposing views on the technical approach. How do you resolve this?",
                    "competency": competency, 
                    "type": "situational",
                    "focus_areas": ["conflict_resolution", "technical_decision_making", "facilitation"]
                }
            ],
            "problem_solving": [
                {
                    "question": "You've been assigned to improve the performance of a critical system, but you have limited time and budget. Walk me through your approach.",
                    "competency": competency,
                    "type": "situational", 
                    "focus_areas": ["prioritization", "resource_constraints", "systematic_approach"]
                }
            ]
        }
        
        if competency in situational_templates:
            return situational_templates[competency][:count]
        return []
    
    def _generate_fallback_questions(self, competency: str, level: str) -> List[Dict[str, Any]]:
        """Generate fallback questions when specific ones aren't available."""
        fallback_questions = [
            {
                "question": f"Describe your experience with {competency.replace('_', ' ')} in your current or previous role.",
                "competency": competency,
                "type": "experience",
                "focus_areas": ["experience_depth", "practical_application"]
            },
            {
                "question": f"What challenges have you faced related to {competency.replace('_', ' ')} and how did you overcome them?",
                "competency": competency,
                "type": "challenge_based",
                "focus_areas": ["problem_solving", "learning_from_experience"]
            }
        ]
        return fallback_questions
    
    def _create_scoring_rubrics(self, questions: List[Dict[str, Any]]) -> Dict[str, Dict]:
        """Create scoring rubrics for the generated questions."""
        rubrics = {}
        
        for i, question in enumerate(questions, 1):
            question_key = f"question_{i}"
            question_type = question.get("type", "behavioral")
            
            if question_type in self.scoring_rubrics:
                rubrics[question_key] = {
                    "question": question["question"],
                    "competency": question["competency"],
                    "type": question_type,
                    "scoring_criteria": self.scoring_rubrics[question_type],
                    "weight": self._determine_question_weight(question),
                    "time_limit": question.get("time_limit", 30)
                }
        
        return rubrics
    
    def _determine_question_weight(self, question: Dict[str, Any]) -> str:
        """Determine the weight/importance of a question."""
        competency = question.get("competency", "")
        question_type = question.get("type", "")
        difficulty = question.get("difficulty", "medium")
        
        # Core competencies get higher weight
        core_competencies = ["coding_fundamentals", "system_design", "leadership", "problem_solving"]
        
        if competency in core_competencies:
            return "high"
        elif question_type in ["coding", "design"] or difficulty == "hard":
            return "high" 
        elif difficulty == "easy":
            return "medium"
        else:
            return "medium"
    
    def _generate_follow_up_probes(self, questions: List[Dict[str, Any]]) -> Dict[str, List[str]]:
        """Generate follow-up probes for each question."""
        probes = {}
        
        for i, question in enumerate(questions, 1):
            question_key = f"question_{i}"
            competency = question.get("competency", "")
            
            # Get competency-specific follow-ups
            if competency in self.follow_up_strategies:
                competency_probes = self.follow_up_strategies[competency].copy()
            else:
                competency_probes = [
                    "Can you provide more specific details about your approach?",
                    "What would you do differently if you had to do this again?",
                    "What challenges did you face and how did you overcome them?"
                ]
            
            # Add question-type specific probes
            question_type = question.get("type", "")
            if question_type == "coding":
                competency_probes.extend([
                    "How would you test this solution?",
                    "What's the time and space complexity of your approach?",
                    "Can you think of any optimizations?"
                ])
            elif question_type == "behavioral":
                competency_probes.extend([
                    "What did you learn from this experience?",
                    "How did others react to your approach?",
                    "What metrics did you use to measure success?"
                ])
            elif question_type == "design":
                competency_probes.extend([
                    "How would you handle failure scenarios?",
                    "What monitoring would you implement?",
                    "How would this scale to 10x the load?"
                ])
            
            probes[question_key] = competency_probes[:5]  # Limit to 5 follow-ups
        
        return probes
    
    def _create_calibration_examples(self, sample_questions: List[Dict[str, Any]]) -> Dict[str, Dict]:
        """Create calibration examples with poor/good/great answers."""
        examples = {}
        
        for i, question in enumerate(sample_questions, 1):
            question_key = f"question_{i}"
            examples[question_key] = {
                "question": question["question"],
                "competency": question["competency"],
                "sample_answers": {
                    "poor_answer": self._generate_sample_answer(question, "poor"),
                    "good_answer": self._generate_sample_answer(question, "good"), 
                    "great_answer": self._generate_sample_answer(question, "great")
                },
                "scoring_rationale": self._generate_scoring_rationale(question)
            }
        
        return examples
    
    def _generate_sample_answer(self, question: Dict[str, Any], quality: str) -> Dict[str, str]:
        """Generate sample answers of different quality levels."""
        competency = question.get("competency", "")
        question_type = question.get("type", "")
        
        if quality == "poor":
            return {
                "answer": f"Sample poor answer for {competency} question - lacks detail, specificity, or demonstrates weak competency",
                "score": "1-2",
                "issues": ["Vague response", "Limited evidence of competency", "Poor structure"]
            }
        elif quality == "good":
            return {
                "answer": f"Sample good answer for {competency} question - adequate detail, demonstrates competency clearly",
                "score": "3", 
                "strengths": ["Clear structure", "Demonstrates competency", "Adequate detail"]
            }
        else:  # great
            return {
                "answer": f"Sample excellent answer for {competency} question - exceptional detail, strong evidence, goes above and beyond",
                "score": "4",
                "strengths": ["Exceptional detail", "Strong evidence", "Strategic thinking", "Goes beyond requirements"]
            }
    
    def _generate_scoring_rationale(self, question: Dict[str, Any]) -> Dict[str, str]:
        """Generate rationale for scoring this question."""
        competency = question.get("competency", "")
        return {
            "key_indicators": f"Look for evidence of {competency.replace('_', ' ')} competency",
            "red_flags": "Vague answers, lack of specifics, negative outcomes without learning",
            "green_flags": "Specific examples, clear impact, demonstrates growth and learning"
        }
    
    def _generate_usage_guidelines(self, role_key: str, level_key: str) -> Dict[str, Any]:
        """Generate usage guidelines for the question bank."""
        return {
            "interview_flow": {
                "warm_up": "Start with 1-2 easier questions to build rapport",
                "core_assessment": "Focus majority of time on core competency questions",
                "closing": "End with questions about candidate's questions/interests"
            },
            "time_management": {
                "technical_questions": "Allow extra time for coding/design questions",
                "behavioral_questions": "Keep to time limits but allow for follow-ups",
                "total_recommendation": "45-75 minutes per interview round"
            },
            "question_selection": {
                "variety": "Mix question types within each competency area",
                "difficulty": "Adjust based on candidate responses and energy",
                "customization": "Adapt questions based on candidate's background"
            },
            "common_mistakes": [
                "Don't ask all questions mechanically",
                "Don't skip follow-up questions",
                "Don't forget to assess cultural fit alongside competencies",
                "Don't let one strong/weak area bias overall assessment"
            ],
            "calibration_reminders": [
                "Compare against role standard, not other candidates",
                "Focus on evidence demonstrated, not potential",
                "Consider level-appropriate expectations",
                "Document specific examples in feedback"
            ]
        }


def format_human_readable(question_bank: Dict[str, Any]) -> str:
    """Format question bank data in human-readable format."""
    output = []
    
    # Header
    output.append(f"Interview Question Bank: {question_bank['role']} ({question_bank['level'].title()} Level)")
    output.append("=" * 70)
    output.append(f"Generated: {question_bank['generated_at']}")
    output.append(f"Total Questions: {question_bank['total_questions']}")
    output.append(f"Question Types: {', '.join(question_bank['question_types'])}")
    output.append(f"Target Competencies: {', '.join(question_bank['competencies'])}")
    output.append("")
    
    # Questions
    output.append("INTERVIEW QUESTIONS")
    output.append("-" * 50)
    
    for i, question in enumerate(question_bank['questions'], 1):
        output.append(f"\n{i}. {question['question']}")
        output.append(f"   Competency: {question['competency'].replace('_', ' ').title()}")
        output.append(f"   Type: {question.get('type', 'N/A').title()}")
        if 'time_limit' in question:
            output.append(f"   Time Limit: {question['time_limit']} minutes")
        if 'focus_areas' in question:
            output.append(f"   Focus Areas: {', '.join(question['focus_areas'])}")
    
    # Scoring Guidelines
    output.append("\n\nSCORING RUBRICS")
    output.append("-" * 50)
    
    # Show sample scoring criteria
    if question_bank['scoring_rubrics']:
        first_question = list(question_bank['scoring_rubrics'].keys())[0]
        sample_rubric = question_bank['scoring_rubrics'][first_question]
        
        output.append(f"Sample Scoring Criteria ({sample_rubric['type']} questions):")
        for criterion, scores in sample_rubric['scoring_criteria'].items():
            output.append(f"\n{criterion.replace('_', ' ').title()}:")
            for score, description in scores.items():
                output.append(f"  {score}: {description}")
    
    # Follow-up Probes
    output.append("\n\nFOLLOW-UP PROBE EXAMPLES")
    output.append("-" * 50)
    
    if question_bank['follow_up_probes']:
        first_question = list(question_bank['follow_up_probes'].keys())[0]
        sample_probes = question_bank['follow_up_probes'][first_question]
        
        output.append("Sample follow-up questions:")
        for probe in sample_probes[:3]:  # Show first 3
            output.append(f"  • {probe}")
    
    # Usage Guidelines
    output.append("\n\nUSAGE GUIDELINES")
    output.append("-" * 50)
    
    guidelines = question_bank['usage_guidelines']
    
    output.append("Interview Flow:")
    for phase, description in guidelines['interview_flow'].items():
        output.append(f"  • {phase.replace('_', ' ').title()}: {description}")
    
    output.append("\nTime Management:")
    for aspect, recommendation in guidelines['time_management'].items():
        output.append(f"  • {aspect.replace('_', ' ').title()}: {recommendation}")
    
    output.append("\nCommon Mistakes to Avoid:")
    for mistake in guidelines['common_mistakes'][:3]:  # Show first 3
        output.append(f"  • {mistake}")
    
    # Calibration Examples (if available)
    if question_bank['calibration_examples']:
        output.append("\n\nCALIBRATION EXAMPLES")
        output.append("-" * 50)
        
        first_example = list(question_bank['calibration_examples'].values())[0]
        output.append(f"Question: {first_example['question']}")
        
        output.append("\nSample Answer Quality Levels:")
        for quality, details in first_example['sample_answers'].items():
            output.append(f"  {quality.replace('_', ' ').title()} (Score {details['score']}):")
            if 'issues' in details:
                output.append(f"    Issues: {', '.join(details['issues'])}")
            if 'strengths' in details:
                output.append(f"    Strengths: {', '.join(details['strengths'])}")
    
    return "\n".join(output)


def main():
    parser = argparse.ArgumentParser(description="Generate comprehensive interview question banks with scoring criteria")
    parser.add_argument("--role", type=str, help="Job role title (e.g., 'Frontend Engineer')")
    parser.add_argument("--level", type=str, default="senior", help="Experience level (junior, mid, senior, staff, principal)")
    parser.add_argument("--competencies", type=str, help="Comma-separated list of competencies to focus on")
    parser.add_argument("--question-types", type=str, help="Comma-separated list of question types (technical, behavioral, situational)")
    parser.add_argument("--num-questions", type=int, default=20, help="Number of questions to generate")
    parser.add_argument("--input", type=str, help="Input JSON file with role requirements")
    parser.add_argument("--output", type=str, help="Output directory or file path")
    parser.add_argument("--format", choices=["json", "text", "both"], default="both", help="Output format")
    
    args = parser.parse_args()
    
    generator = QuestionBankGenerator()
    
    # Handle input
    if args.input:
        try:
            with open(args.input, 'r') as f:
                role_data = json.load(f)
            role = role_data.get('role') or role_data.get('title', '')
            level = role_data.get('level', 'senior')
            competencies = role_data.get('competencies')
            question_types = role_data.get('question_types')
            num_questions = role_data.get('num_questions', 20)
        except Exception as e:
            print(f"Error reading input file: {e}")
            sys.exit(1)
    else:
        if not args.role:
            print("Error: --role is required when not using --input")
            sys.exit(1)
        
        role = args.role
        level = args.level
        competencies = args.competencies.split(',') if args.competencies else None
        question_types = args.question_types.split(',') if args.question_types else None
        num_questions = args.num_questions
    
    # Generate question bank
    try:
        question_bank = generator.generate_question_bank(
            role=role,
            level=level,
            competencies=competencies,
            question_types=question_types,
            num_questions=num_questions
        )
        
        # Handle output
        if args.output:
            output_path = args.output
            if os.path.isdir(output_path):
                safe_role = "".join(c for c in role.lower() if c.isalnum() or c in (' ', '-', '_')).replace(' ', '_')
                base_filename = f"{safe_role}_{level}_questions"
                json_path = os.path.join(output_path, f"{base_filename}.json")
                text_path = os.path.join(output_path, f"{base_filename}.txt")
            else:
                json_path = output_path if output_path.endswith('.json') else f"{output_path}.json"
                text_path = output_path.replace('.json', '.txt') if output_path.endswith('.json') else f"{output_path}.txt"
        else:
            safe_role = "".join(c for c in role.lower() if c.isalnum() or c in (' ', '-', '_')).replace(' ', '_')
            base_filename = f"{safe_role}_{level}_questions"
            json_path = f"{base_filename}.json"
            text_path = f"{base_filename}.txt"
        
        # Write outputs
        if args.format in ["json", "both"]:
            with open(json_path, 'w') as f:
                json.dump(question_bank, f, indent=2, default=str)
            print(f"JSON output written to: {json_path}")
        
        if args.format in ["text", "both"]:
            with open(text_path, 'w') as f:
                f.write(format_human_readable(question_bank))
            print(f"Text output written to: {text_path}")
        
        # Print summary
        print(f"\nQuestion Bank Summary:")
        print(f"Role: {question_bank['role']} ({question_bank['level'].title()})")
        print(f"Total Questions: {question_bank['total_questions']}")
        print(f"Competencies Covered: {len(question_bank['competencies'])}")
        print(f"Question Types: {', '.join(question_bank['question_types'])}")
        
    except Exception as e:
        print(f"Error generating question bank: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()