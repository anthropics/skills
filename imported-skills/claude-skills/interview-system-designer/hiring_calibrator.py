#!/usr/bin/env python3
"""
Hiring Calibrator

Analyzes interview scores from multiple candidates and interviewers to detect bias, 
calibration issues, and inconsistent rubric application. Generates calibration reports
with specific recommendations for interviewer coaching and process improvements.

Usage:
    python hiring_calibrator.py --input interview_results.json --analysis-type comprehensive
    python hiring_calibrator.py --input data.json --competencies technical,leadership --output report.json
    python hiring_calibrator.py --input historical_data.json --trend-analysis --period quarterly
"""

import os
import sys
import json
import argparse
import statistics
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Any, Tuple
from collections import defaultdict, Counter
import math


class HiringCalibrator:
    """Analyzes interview data for bias detection and calibration issues."""
    
    def __init__(self):
        self.bias_thresholds = self._init_bias_thresholds()
        self.calibration_standards = self._init_calibration_standards()
        self.demographic_categories = self._init_demographic_categories()
        
    def _init_bias_thresholds(self) -> Dict[str, float]:
        """Initialize statistical thresholds for bias detection."""
        return {
            "score_variance_threshold": 1.5,  # Standard deviations
            "pass_rate_difference_threshold": 0.15,  # 15% difference
            "interviewer_consistency_threshold": 0.8,  # Correlation coefficient
            "demographic_parity_threshold": 0.10,  # 10% difference
            "score_inflation_threshold": 0.3,  # 30% above historical average
            "score_deflation_threshold": 0.3,  # 30% below historical average
            "minimum_sample_size": 5  # Minimum candidates per analysis
        }
    
    def _init_calibration_standards(self) -> Dict[str, Dict]:
        """Initialize expected calibration standards."""
        return {
            "score_distribution": {
                "target_mean": 2.8,  # Expected average score (1-4 scale)
                "target_std": 0.9,   # Expected standard deviation
                "expected_distribution": {
                    "1": 0.10,  # 10% score 1 (does not meet)
                    "2": 0.25,  # 25% score 2 (partially meets)
                    "3": 0.45,  # 45% score 3 (meets expectations) 
                    "4": 0.20   # 20% score 4 (exceeds expectations)
                }
            },
            "interviewer_agreement": {
                "minimum_correlation": 0.70,  # Minimum correlation between interviewers
                "maximum_std_deviation": 0.8,  # Maximum std dev in scores for same candidate
                "agreement_threshold": 0.75   # % of time interviewers should agree within 1 point
            },
            "pass_rates": {
                "junior_level": 0.25,   # 25% pass rate for junior roles
                "mid_level": 0.20,      # 20% pass rate for mid roles
                "senior_level": 0.15,   # 15% pass rate for senior roles
                "staff_level": 0.10,    # 10% pass rate for staff+ roles
                "leadership": 0.12      # 12% pass rate for leadership roles
            }
        }
    
    def _init_demographic_categories(self) -> List[str]:
        """Initialize demographic categories to analyze for bias."""
        return [
            "gender", "ethnicity", "education_level", "previous_company_size",
            "years_experience", "university_tier", "geographic_location"
        ]
    
    def analyze_hiring_calibration(self, interview_data: List[Dict[str, Any]], 
                                  analysis_type: str = "comprehensive",
                                  competencies: Optional[List[str]] = None,
                                  trend_analysis: bool = False,
                                  period: str = "monthly") -> Dict[str, Any]:
        """Perform comprehensive hiring calibration analysis."""
        
        # Validate and preprocess data
        processed_data = self._preprocess_interview_data(interview_data)
        
        if len(processed_data) < self.bias_thresholds["minimum_sample_size"]:
            return {
                "error": "Insufficient data for analysis",
                "minimum_required": self.bias_thresholds["minimum_sample_size"],
                "actual_samples": len(processed_data)
            }
        
        # Perform different types of analysis based on request
        analysis_results = {
            "analysis_type": analysis_type,
            "data_summary": self._generate_data_summary(processed_data),
            "generated_at": datetime.now().isoformat()
        }
        
        if analysis_type in ["comprehensive", "bias"]:
            analysis_results["bias_analysis"] = self._analyze_bias_patterns(processed_data, competencies)
        
        if analysis_type in ["comprehensive", "calibration"]:
            analysis_results["calibration_analysis"] = self._analyze_calibration_consistency(processed_data, competencies)
        
        if analysis_type in ["comprehensive", "interviewer"]:
            analysis_results["interviewer_analysis"] = self._analyze_interviewer_bias(processed_data)
        
        if analysis_type in ["comprehensive", "scoring"]:
            analysis_results["scoring_analysis"] = self._analyze_scoring_patterns(processed_data, competencies)
        
        if trend_analysis:
            analysis_results["trend_analysis"] = self._analyze_trends_over_time(processed_data, period)
        
        # Generate recommendations
        analysis_results["recommendations"] = self._generate_recommendations(analysis_results)
        
        # Calculate overall calibration health score
        analysis_results["calibration_health_score"] = self._calculate_health_score(analysis_results)
        
        return analysis_results
    
    def _preprocess_interview_data(self, raw_data: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """Clean and validate interview data."""
        processed_data = []
        
        for record in raw_data:
            if self._validate_interview_record(record):
                processed_record = self._standardize_record(record)
                processed_data.append(processed_record)
        
        return processed_data
    
    def _validate_interview_record(self, record: Dict[str, Any]) -> bool:
        """Validate that an interview record has required fields."""
        required_fields = ["candidate_id", "interviewer_id", "scores", "overall_recommendation", "date"]
        
        for field in required_fields:
            if field not in record or record[field] is None:
                return False
        
        # Validate scores format
        if not isinstance(record["scores"], dict):
            return False
        
        # Validate score values are numeric and in valid range (1-4)
        for competency, score in record["scores"].items():
            if not isinstance(score, (int, float)) or not (1 <= score <= 4):
                return False
        
        return True
    
    def _standardize_record(self, record: Dict[str, Any]) -> Dict[str, Any]:
        """Standardize record format and add computed fields."""
        standardized = record.copy()
        
        # Calculate average score
        scores = list(record["scores"].values())
        standardized["average_score"] = statistics.mean(scores)
        
        # Standardize recommendation to binary
        recommendation = record["overall_recommendation"].lower()
        standardized["hire_decision"] = recommendation in ["hire", "strong hire", "yes"]
        
        # Parse date if string
        if isinstance(record["date"], str):
            try:
                standardized["date"] = datetime.fromisoformat(record["date"].replace("Z", "+00:00"))
            except ValueError:
                standardized["date"] = datetime.now()
        
        # Add demographic info if available
        for category in self.demographic_categories:
            if category not in standardized:
                standardized[category] = "unknown"
        
        # Add level normalization
        role = record.get("role", "").lower()
        if any(level in role for level in ["junior", "associate", "entry"]):
            standardized["normalized_level"] = "junior"
        elif any(level in role for level in ["senior", "sr"]):
            standardized["normalized_level"] = "senior"  
        elif any(level in role for level in ["staff", "principal", "lead"]):
            standardized["normalized_level"] = "staff"
        else:
            standardized["normalized_level"] = "mid"
        
        return standardized
    
    def _generate_data_summary(self, data: List[Dict[str, Any]]) -> Dict[str, Any]:
        """Generate summary statistics for the dataset."""
        if not data:
            return {}
        
        total_candidates = len(data)
        unique_interviewers = len(set(record["interviewer_id"] for record in data))
        
        # Score statistics
        all_scores = []
        all_average_scores = []
        hire_decisions = []
        
        for record in data:
            all_scores.extend(record["scores"].values())
            all_average_scores.append(record["average_score"])
            hire_decisions.append(record["hire_decision"])
        
        # Date range
        dates = [record["date"] for record in data if record["date"]]
        date_range = {
            "start_date": min(dates).isoformat() if dates else None,
            "end_date": max(dates).isoformat() if dates else None,
            "total_days": (max(dates) - min(dates)).days if len(dates) > 1 else 0
        }
        
        # Role distribution
        roles = [record.get("role", "unknown") for record in data]
        role_distribution = dict(Counter(roles))
        
        return {
            "total_candidates": total_candidates,
            "unique_interviewers": unique_interviewers,
            "candidates_per_interviewer": round(total_candidates / unique_interviewers, 2),
            "date_range": date_range,
            "score_statistics": {
                "mean_individual_scores": round(statistics.mean(all_scores), 2),
                "std_individual_scores": round(statistics.stdev(all_scores) if len(all_scores) > 1 else 0, 2),
                "mean_average_scores": round(statistics.mean(all_average_scores), 2),
                "std_average_scores": round(statistics.stdev(all_average_scores) if len(all_average_scores) > 1 else 0, 2)
            },
            "hire_rate": round(sum(hire_decisions) / len(hire_decisions), 3),
            "role_distribution": role_distribution
        }
    
    def _analyze_bias_patterns(self, data: List[Dict[str, Any]], 
                              target_competencies: Optional[List[str]]) -> Dict[str, Any]:
        """Analyze potential bias patterns in interview decisions."""
        bias_analysis = {
            "demographic_bias": {},
            "interviewer_bias": {},
            "competency_bias": {},
            "overall_bias_score": 0
        }
        
        # Analyze demographic bias
        for demographic in self.demographic_categories:
            if all(record.get(demographic) == "unknown" for record in data):
                continue
                
            demographic_analysis = self._analyze_demographic_bias(data, demographic)
            if demographic_analysis["bias_detected"]:
                bias_analysis["demographic_bias"][demographic] = demographic_analysis
        
        # Analyze interviewer bias
        bias_analysis["interviewer_bias"] = self._analyze_interviewer_bias(data)
        
        # Analyze competency bias if specified
        if target_competencies:
            bias_analysis["competency_bias"] = self._analyze_competency_bias(data, target_competencies)
        
        # Calculate overall bias score
        bias_analysis["overall_bias_score"] = self._calculate_bias_score(bias_analysis)
        
        return bias_analysis
    
    def _analyze_demographic_bias(self, data: List[Dict[str, Any]], 
                                 demographic: str) -> Dict[str, Any]:
        """Analyze bias for a specific demographic category."""
        # Group data by demographic values
        demographic_groups = defaultdict(list)
        for record in data:
            demo_value = record.get(demographic, "unknown")
            if demo_value != "unknown":
                demographic_groups[demo_value].append(record)
        
        if len(demographic_groups) < 2:
            return {"bias_detected": False, "reason": "insufficient_groups"}
        
        # Calculate statistics for each group
        group_stats = {}
        for group, records in demographic_groups.items():
            if len(records) >= self.bias_thresholds["minimum_sample_size"]:
                scores = [r["average_score"] for r in records]
                hire_rate = sum(r["hire_decision"] for r in records) / len(records)
                
                group_stats[group] = {
                    "count": len(records),
                    "mean_score": statistics.mean(scores),
                    "hire_rate": hire_rate,
                    "std_score": statistics.stdev(scores) if len(scores) > 1 else 0
                }
        
        if len(group_stats) < 2:
            return {"bias_detected": False, "reason": "insufficient_sample_sizes"}
        
        # Detect statistical differences
        bias_detected = False
        bias_details = {}
        
        # Check for significant differences in hire rates
        hire_rates = [stats["hire_rate"] for stats in group_stats.values()]
        max_hire_rate_diff = max(hire_rates) - min(hire_rates)
        
        if max_hire_rate_diff > self.bias_thresholds["demographic_parity_threshold"]:
            bias_detected = True
            bias_details["hire_rate_disparity"] = {
                "max_difference": round(max_hire_rate_diff, 3),
                "threshold": self.bias_thresholds["demographic_parity_threshold"],
                "group_stats": group_stats
            }
        
        # Check for significant differences in scoring
        mean_scores = [stats["mean_score"] for stats in group_stats.values()]
        max_score_diff = max(mean_scores) - min(mean_scores)
        
        if max_score_diff > 0.5:  # Half point difference threshold
            bias_detected = True
            bias_details["scoring_disparity"] = {
                "max_difference": round(max_score_diff, 3),
                "group_stats": group_stats
            }
        
        return {
            "bias_detected": bias_detected,
            "demographic": demographic,
            "group_statistics": group_stats,
            "bias_details": bias_details,
            "recommendation": self._generate_demographic_bias_recommendation(demographic, bias_details) if bias_detected else None
        }
    
    def _analyze_interviewer_bias(self, data: List[Dict[str, Any]]) -> Dict[str, Any]:
        """Analyze bias patterns across different interviewers."""
        interviewer_stats = defaultdict(list)
        
        # Group by interviewer
        for record in data:
            interviewer_id = record["interviewer_id"]
            interviewer_stats[interviewer_id].append(record)
        
        # Calculate statistics per interviewer
        interviewer_analysis = {}
        for interviewer_id, records in interviewer_stats.items():
            if len(records) >= self.bias_thresholds["minimum_sample_size"]:
                scores = [r["average_score"] for r in records]
                hire_rate = sum(r["hire_decision"] for r in records) / len(records)
                
                interviewer_analysis[interviewer_id] = {
                    "total_interviews": len(records),
                    "mean_score": statistics.mean(scores),
                    "std_score": statistics.stdev(scores) if len(scores) > 1 else 0,
                    "hire_rate": hire_rate,
                    "score_inflation": self._detect_score_inflation(scores),
                    "consistency_score": self._calculate_interviewer_consistency(records)
                }
        
        # Identify outlier interviewers
        if len(interviewer_analysis) > 1:
            overall_mean_score = statistics.mean([stats["mean_score"] for stats in interviewer_analysis.values()])
            overall_hire_rate = statistics.mean([stats["hire_rate"] for stats in interviewer_analysis.values()])
            
            outlier_interviewers = {}
            for interviewer_id, stats in interviewer_analysis.items():
                issues = []
                
                # Check for score inflation/deflation
                if stats["mean_score"] > overall_mean_score * (1 + self.bias_thresholds["score_inflation_threshold"]):
                    issues.append("score_inflation")
                elif stats["mean_score"] < overall_mean_score * (1 - self.bias_thresholds["score_deflation_threshold"]):
                    issues.append("score_deflation")
                
                # Check for hire rate deviation
                hire_rate_diff = abs(stats["hire_rate"] - overall_hire_rate)
                if hire_rate_diff > self.bias_thresholds["pass_rate_difference_threshold"]:
                    issues.append("hire_rate_deviation")
                
                # Check for low consistency
                if stats["consistency_score"] < self.bias_thresholds["interviewer_consistency_threshold"]:
                    issues.append("low_consistency")
                
                if issues:
                    outlier_interviewers[interviewer_id] = {
                        "issues": issues,
                        "statistics": stats,
                        "severity": len(issues)  # More issues = higher severity
                    }
        
        return {
            "interviewer_statistics": interviewer_analysis,
            "outlier_interviewers": outlier_interviewers if len(interviewer_analysis) > 1 else {},
            "overall_consistency": self._calculate_overall_interviewer_consistency(data),
            "recommendations": self._generate_interviewer_recommendations(outlier_interviewers if len(interviewer_analysis) > 1 else {})
        }
    
    def _analyze_competency_bias(self, data: List[Dict[str, Any]], 
                               competencies: List[str]) -> Dict[str, Any]:
        """Analyze bias patterns within specific competencies."""
        competency_analysis = {}
        
        for competency in competencies:
            # Extract scores for this competency
            competency_scores = []
            for record in data:
                if competency in record["scores"]:
                    competency_scores.append({
                        "score": record["scores"][competency],
                        "interviewer": record["interviewer_id"],
                        "candidate": record["candidate_id"],
                        "overall_decision": record["hire_decision"]
                    })
            
            if len(competency_scores) < self.bias_thresholds["minimum_sample_size"]:
                continue
            
            # Analyze scoring patterns
            scores = [item["score"] for item in competency_scores]
            score_variance = statistics.variance(scores) if len(scores) > 1 else 0
            
            # Analyze by interviewer
            interviewer_competency_scores = defaultdict(list)
            for item in competency_scores:
                interviewer_competency_scores[item["interviewer"]].append(item["score"])
            
            interviewer_variations = {}
            if len(interviewer_competency_scores) > 1:
                interviewer_means = {interviewer: statistics.mean(scores) 
                                   for interviewer, scores in interviewer_competency_scores.items()
                                   if len(scores) >= 3}
                
                if len(interviewer_means) > 1:
                    mean_of_means = statistics.mean(interviewer_means.values())
                    for interviewer, mean_score in interviewer_means.items():
                        deviation = abs(mean_score - mean_of_means)
                        if deviation > 0.5:  # More than half point deviation
                            interviewer_variations[interviewer] = {
                                "mean_score": round(mean_score, 2),
                                "deviation_from_average": round(deviation, 2),
                                "sample_size": len(interviewer_competency_scores[interviewer])
                            }
            
            competency_analysis[competency] = {
                "total_scores": len(competency_scores),
                "mean_score": round(statistics.mean(scores), 2),
                "score_variance": round(score_variance, 2),
                "interviewer_variations": interviewer_variations,
                "bias_detected": len(interviewer_variations) > 0
            }
        
        return competency_analysis
    
    def _analyze_calibration_consistency(self, data: List[Dict[str, Any]], 
                                       target_competencies: Optional[List[str]]) -> Dict[str, Any]:
        """Analyze calibration consistency across interviews."""
        
        # Group candidates by those interviewed by multiple people
        candidate_interviewers = defaultdict(list)
        for record in data:
            candidate_interviewers[record["candidate_id"]].append(record)
        
        multi_interviewer_candidates = {
            candidate: records for candidate, records in candidate_interviewers.items()
            if len(records) > 1
        }
        
        if not multi_interviewer_candidates:
            return {
                "error": "No candidates with multiple interviewers found",
                "single_interviewer_analysis": self._analyze_single_interviewer_consistency(data)
            }
        
        # Calculate agreement statistics
        agreement_stats = []
        score_correlations = []
        
        for candidate, records in multi_interviewer_candidates.items():
            candidate_scores = []
            interviewer_pairs = []
            
            for record in records:
                avg_score = record["average_score"]
                candidate_scores.append(avg_score)
                interviewer_pairs.append(record["interviewer_id"])
            
            if len(candidate_scores) > 1:
                # Calculate standard deviation of scores for this candidate
                score_std = statistics.stdev(candidate_scores)
                agreement_stats.append(score_std)
                
                # Check if all interviewers agree within 1 point
                score_range = max(candidate_scores) - min(candidate_scores)
                agreement_within_one = score_range <= 1.0
                
                score_correlations.append({
                    "candidate": candidate,
                    "scores": candidate_scores,
                    "interviewers": interviewer_pairs,
                    "score_std": score_std,
                    "score_range": score_range,
                    "agreement_within_one": agreement_within_one
                })
        
        # Calculate overall calibration metrics
        mean_score_std = statistics.mean(agreement_stats) if agreement_stats else 0
        agreement_rate = sum(1 for corr in score_correlations if corr["agreement_within_one"]) / len(score_correlations) if score_correlations else 0
        
        calibration_quality = "good"
        if mean_score_std > self.calibration_standards["interviewer_agreement"]["maximum_std_deviation"]:
            calibration_quality = "poor"
        elif agreement_rate < self.calibration_standards["interviewer_agreement"]["agreement_threshold"]:
            calibration_quality = "fair"
        
        return {
            "multi_interviewer_candidates": len(multi_interviewer_candidates),
            "mean_score_standard_deviation": round(mean_score_std, 3),
            "agreement_within_one_point_rate": round(agreement_rate, 3),
            "calibration_quality": calibration_quality,
            "candidate_agreement_details": score_correlations,
            "target_standards": self.calibration_standards["interviewer_agreement"],
            "recommendations": self._generate_calibration_recommendations(mean_score_std, agreement_rate)
        }
    
    def _analyze_scoring_patterns(self, data: List[Dict[str, Any]], 
                                target_competencies: Optional[List[str]]) -> Dict[str, Any]:
        """Analyze overall scoring patterns and distributions."""
        
        # Overall score distribution
        all_individual_scores = []
        all_average_scores = []
        score_distribution = defaultdict(int)
        
        for record in data:
            avg_score = record["average_score"]
            all_average_scores.append(avg_score)
            
            for competency, score in record["scores"].items():
                if not target_competencies or competency in target_competencies:
                    all_individual_scores.append(score)
                    score_distribution[str(int(score))] += 1
        
        # Calculate distribution percentages
        total_scores = sum(score_distribution.values())
        score_percentages = {score: count/total_scores for score, count in score_distribution.items()}
        
        # Compare against expected distribution
        expected_dist = self.calibration_standards["score_distribution"]["expected_distribution"]
        distribution_analysis = {}
        
        for score in ["1", "2", "3", "4"]:
            expected_pct = expected_dist.get(score, 0)
            actual_pct = score_percentages.get(score, 0)
            difference = actual_pct - expected_pct
            
            distribution_analysis[score] = {
                "expected_percentage": expected_pct,
                "actual_percentage": round(actual_pct, 3),
                "difference": round(difference, 3),
                "significant_deviation": abs(difference) > 0.05  # 5% threshold
            }
        
        # Calculate scoring statistics
        mean_score = statistics.mean(all_individual_scores) if all_individual_scores else 0
        std_score = statistics.stdev(all_individual_scores) if len(all_individual_scores) > 1 else 0
        
        target_mean = self.calibration_standards["score_distribution"]["target_mean"]
        target_std = self.calibration_standards["score_distribution"]["target_std"]
        
        # Analyze pass rates by level
        level_pass_rates = {}
        level_groups = defaultdict(list)
        
        for record in data:
            level = record.get("normalized_level", "unknown")
            level_groups[level].append(record["hire_decision"])
        
        for level, decisions in level_groups.items():
            if len(decisions) >= self.bias_thresholds["minimum_sample_size"]:
                pass_rate = sum(decisions) / len(decisions)
                expected_rate = self.calibration_standards["pass_rates"].get(f"{level}_level", 0.15)
                
                level_pass_rates[level] = {
                    "actual_pass_rate": round(pass_rate, 3),
                    "expected_pass_rate": expected_rate,
                    "difference": round(pass_rate - expected_rate, 3),
                    "sample_size": len(decisions)
                }
        
        return {
            "score_statistics": {
                "mean_score": round(mean_score, 2),
                "std_score": round(std_score, 2),
                "target_mean": target_mean,
                "target_std": target_std,
                "mean_deviation": round(abs(mean_score - target_mean), 2),
                "std_deviation": round(abs(std_score - target_std), 2)
            },
            "score_distribution": distribution_analysis,
            "level_pass_rates": level_pass_rates,
            "overall_assessment": self._assess_scoring_health(distribution_analysis, mean_score, target_mean)
        }
    
    def _analyze_trends_over_time(self, data: List[Dict[str, Any]], period: str) -> Dict[str, Any]:
        """Analyze trends in hiring patterns over time."""
        
        # Sort data by date
        dated_data = [record for record in data if record.get("date")]
        dated_data.sort(key=lambda x: x["date"])
        
        if len(dated_data) < 10:  # Need minimum data for trend analysis
            return {"error": "Insufficient data for trend analysis", "minimum_required": 10}
        
        # Group by time period
        period_groups = defaultdict(list)
        
        for record in dated_data:
            date = record["date"]
            
            if period == "weekly":
                period_key = date.strftime("%Y-W%U")
            elif period == "monthly":
                period_key = date.strftime("%Y-%m")
            elif period == "quarterly":
                quarter = (date.month - 1) // 3 + 1
                period_key = f"{date.year}-Q{quarter}"
            else:  # daily
                period_key = date.strftime("%Y-%m-%d")
            
            period_groups[period_key].append(record)
        
        # Calculate metrics for each period
        period_metrics = {}
        for period_key, records in period_groups.items():
            if len(records) >= 3:  # Minimum for meaningful metrics
                scores = [r["average_score"] for r in records]
                hire_rate = sum(r["hire_decision"] for r in records) / len(records)
                
                period_metrics[period_key] = {
                    "count": len(records),
                    "mean_score": statistics.mean(scores),
                    "hire_rate": hire_rate,
                    "std_score": statistics.stdev(scores) if len(scores) > 1 else 0
                }
        
        if len(period_metrics) < 3:
            return {"error": "Insufficient periods for trend analysis"}
        
        # Analyze trends
        sorted_periods = sorted(period_metrics.keys())
        mean_scores = [period_metrics[p]["mean_score"] for p in sorted_periods]
        hire_rates = [period_metrics[p]["hire_rate"] for p in sorted_periods]
        
        # Simple linear trend calculation
        score_trend = self._calculate_linear_trend(mean_scores)
        hire_rate_trend = self._calculate_linear_trend(hire_rates)
        
        return {
            "period": period,
            "total_periods": len(period_metrics),
            "period_metrics": period_metrics,
            "trends": {
                "score_trend": {
                    "direction": "increasing" if score_trend > 0.01 else "decreasing" if score_trend < -0.01 else "stable",
                    "slope": round(score_trend, 4),
                    "significance": "significant" if abs(score_trend) > 0.05 else "minor"
                },
                "hire_rate_trend": {
                    "direction": "increasing" if hire_rate_trend > 0.005 else "decreasing" if hire_rate_trend < -0.005 else "stable",
                    "slope": round(hire_rate_trend, 4),
                    "significance": "significant" if abs(hire_rate_trend) > 0.02 else "minor"
                }
            },
            "insights": self._generate_trend_insights(score_trend, hire_rate_trend, period_metrics)
        }
    
    def _calculate_linear_trend(self, values: List[float]) -> float:
        """Calculate simple linear trend slope."""
        if len(values) < 2:
            return 0
        
        n = len(values)
        x = list(range(n))
        
        # Calculate slope using least squares
        x_mean = statistics.mean(x)
        y_mean = statistics.mean(values)
        
        numerator = sum((x[i] - x_mean) * (values[i] - y_mean) for i in range(n))
        denominator = sum((x[i] - x_mean) ** 2 for i in range(n))
        
        return numerator / denominator if denominator != 0 else 0
    
    def _detect_score_inflation(self, scores: List[float]) -> Dict[str, Any]:
        """Detect if an interviewer shows score inflation patterns."""
        if len(scores) < 5:
            return {"insufficient_data": True}
        
        mean_score = statistics.mean(scores)
        std_score = statistics.stdev(scores)
        
        # Check against expected mean (2.8)
        expected_mean = self.calibration_standards["score_distribution"]["target_mean"]
        deviation = mean_score - expected_mean
        
        # High scores with low variance might indicate inflation
        high_scores_low_variance = mean_score > 3.2 and std_score < 0.5
        
        # Check distribution - too many 4s might indicate inflation
        score_counts = Counter([int(score) for score in scores])
        four_count_ratio = score_counts.get(4, 0) / len(scores)
        
        return {
            "mean_score": round(mean_score, 2),
            "expected_mean": expected_mean,
            "deviation": round(deviation, 2),
            "high_scores_low_variance": high_scores_low_variance,
            "four_count_ratio": round(four_count_ratio, 2),
            "inflation_detected": deviation > 0.3 or high_scores_low_variance or four_count_ratio > 0.4
        }
    
    def _calculate_interviewer_consistency(self, records: List[Dict[str, Any]]) -> float:
        """Calculate consistency score for an interviewer."""
        if len(records) < 3:
            return 0.5  # Neutral score for insufficient data
        
        # Look at variance in scoring
        avg_scores = [r["average_score"] for r in records]
        score_variance = statistics.variance(avg_scores)
        
        # Look at decision consistency relative to scores
        decisions = [r["hire_decision"] for r in records]
        scores_of_hires = [r["average_score"] for r in records if r["hire_decision"]]
        scores_of_no_hires = [r["average_score"] for r in records if not r["hire_decision"]]
        
        # Good consistency means hires have higher average scores
        decision_consistency = 0.5
        if scores_of_hires and scores_of_no_hires:
            hire_mean = statistics.mean(scores_of_hires)
            no_hire_mean = statistics.mean(scores_of_no_hires)
            score_gap = hire_mean - no_hire_mean
            decision_consistency = min(1.0, max(0.0, score_gap / 2.0))  # Normalize to 0-1
        
        # Combine metrics (lower variance = higher consistency)
        variance_consistency = max(0.0, 1.0 - (score_variance / 2.0))
        
        return (decision_consistency + variance_consistency) / 2
    
    def _calculate_overall_interviewer_consistency(self, data: List[Dict[str, Any]]) -> Dict[str, Any]:
        """Calculate overall consistency across all interviewers."""
        interviewer_consistency_scores = []
        
        interviewer_records = defaultdict(list)
        for record in data:
            interviewer_records[record["interviewer_id"]].append(record)
        
        for interviewer_id, records in interviewer_records.items():
            if len(records) >= 3:
                consistency = self._calculate_interviewer_consistency(records)
                interviewer_consistency_scores.append(consistency)
        
        if not interviewer_consistency_scores:
            return {"error": "Insufficient data per interviewer for consistency analysis"}
        
        return {
            "mean_consistency": round(statistics.mean(interviewer_consistency_scores), 3),
            "std_consistency": round(statistics.stdev(interviewer_consistency_scores) if len(interviewer_consistency_scores) > 1 else 0, 3),
            "min_consistency": round(min(interviewer_consistency_scores), 3),
            "max_consistency": round(max(interviewer_consistency_scores), 3),
            "interviewers_analyzed": len(interviewer_consistency_scores),
            "target_threshold": self.bias_thresholds["interviewer_consistency_threshold"]
        }
    
    def _calculate_bias_score(self, bias_analysis: Dict[str, Any]) -> float:
        """Calculate overall bias score (0-1, where 1 is most biased)."""
        bias_factors = []
        
        # Demographic bias factors
        demographic_bias = bias_analysis.get("demographic_bias", {})
        for demo, analysis in demographic_bias.items():
            if analysis.get("bias_detected"):
                bias_factors.append(0.3)  # Each demographic bias adds 0.3
        
        # Interviewer bias factors
        interviewer_bias = bias_analysis.get("interviewer_bias", {})
        outlier_interviewers = interviewer_bias.get("outlier_interviewers", {})
        if outlier_interviewers:
            # Scale by severity and number of outliers
            total_severity = sum(info["severity"] for info in outlier_interviewers.values())
            bias_factors.append(min(0.5, total_severity * 0.1))
        
        # Competency bias factors  
        competency_bias = bias_analysis.get("competency_bias", {})
        for comp, analysis in competency_bias.items():
            if analysis.get("bias_detected"):
                bias_factors.append(0.2)  # Each competency bias adds 0.2
        
        return min(1.0, sum(bias_factors))
    
    def _calculate_health_score(self, analysis: Dict[str, Any]) -> Dict[str, Any]:
        """Calculate overall calibration health score."""
        health_factors = []
        
        # Bias score (lower is better)
        bias_analysis = analysis.get("bias_analysis", {})
        bias_score = bias_analysis.get("overall_bias_score", 0)
        bias_health = max(0, 1 - bias_score)
        health_factors.append(("bias", bias_health, 0.3))
        
        # Calibration consistency
        calibration_analysis = analysis.get("calibration_analysis", {})
        if "calibration_quality" in calibration_analysis:
            quality_map = {"good": 1.0, "fair": 0.7, "poor": 0.3}
            calibration_health = quality_map.get(calibration_analysis["calibration_quality"], 0.5)
            health_factors.append(("calibration", calibration_health, 0.25))
        
        # Interviewer consistency
        interviewer_analysis = analysis.get("interviewer_analysis", {})
        overall_consistency = interviewer_analysis.get("overall_consistency", {})
        if "mean_consistency" in overall_consistency:
            consistency_health = overall_consistency["mean_consistency"]
            health_factors.append(("interviewer_consistency", consistency_health, 0.25))
        
        # Scoring patterns health
        scoring_analysis = analysis.get("scoring_analysis", {})
        if "overall_assessment" in scoring_analysis:
            assessment_map = {"healthy": 1.0, "concerning": 0.6, "poor": 0.2}
            scoring_health = assessment_map.get(scoring_analysis["overall_assessment"], 0.5)
            health_factors.append(("scoring_patterns", scoring_health, 0.2))
        
        # Calculate weighted average
        if health_factors:
            weighted_sum = sum(score * weight for _, score, weight in health_factors)
            total_weight = sum(weight for _, _, weight in health_factors)
            overall_score = weighted_sum / total_weight
        else:
            overall_score = 0.5  # Neutral if no data
        
        # Categorize health
        if overall_score >= 0.8:
            health_category = "excellent"
        elif overall_score >= 0.7:
            health_category = "good"
        elif overall_score >= 0.5:
            health_category = "fair"
        else:
            health_category = "poor"
        
        return {
            "overall_score": round(overall_score, 3),
            "health_category": health_category,
            "component_scores": {name: round(score, 3) for name, score, _ in health_factors},
            "improvement_priority": self._identify_improvement_priorities(health_factors)
        }
    
    def _identify_improvement_priorities(self, health_factors: List[Tuple[str, float, float]]) -> List[str]:
        """Identify areas that need the most improvement."""
        priorities = []
        
        for name, score, weight in health_factors:
            impact = (1 - score) * weight  # Low scores with high weights = high priority
            if impact > 0.15:  # Significant impact threshold
                priorities.append(name)
        
        # Sort by impact (highest first)
        priorities.sort(key=lambda name: next((1 - score) * weight for n, score, weight in health_factors if n == name), reverse=True)
        
        return priorities
    
    def _generate_recommendations(self, analysis: Dict[str, Any]) -> List[Dict[str, Any]]:
        """Generate actionable recommendations based on analysis results."""
        recommendations = []
        
        # Bias-related recommendations
        bias_analysis = analysis.get("bias_analysis", {})
        
        # Demographic bias recommendations
        for demo, demo_analysis in bias_analysis.get("demographic_bias", {}).items():
            if demo_analysis.get("bias_detected"):
                recommendations.append({
                    "priority": "high",
                    "category": "bias_mitigation",
                    "title": f"Address {demo.replace('_', ' ').title()} Bias",
                    "description": demo_analysis.get("recommendation", f"Implement bias mitigation strategies for {demo}"),
                    "actions": [
                        "Conduct unconscious bias training focused on this demographic",
                        "Review and standardize interview questions",
                        "Implement diverse interview panels",
                        "Monitor hiring metrics by demographic group"
                    ]
                })
        
        # Interviewer-specific recommendations
        interviewer_analysis = bias_analysis.get("interviewer_bias", {})
        outlier_interviewers = interviewer_analysis.get("outlier_interviewers", {})
        
        for interviewer_id, outlier_info in outlier_interviewers.items():
            issues = outlier_info["issues"]
            priority = "high" if outlier_info["severity"] >= 3 else "medium"
            
            actions = []
            if "score_inflation" in issues:
                actions.extend([
                    "Provide calibration training on scoring standards",
                    "Shadow experienced interviewers for recalibration",
                    "Review examples of each score level"
                ])
            if "score_deflation" in issues:
                actions.extend([
                    "Review expectations for role level",
                    "Calibrate against recent successful hires",
                    "Discuss evaluation criteria with hiring manager"
                ])
            if "hire_rate_deviation" in issues:
                actions.extend([
                    "Review hiring bar standards",
                    "Participate in calibration sessions",
                    "Compare decision criteria with team"
                ])
            if "low_consistency" in issues:
                actions.extend([
                    "Practice structured interviewing techniques",
                    "Use standardized scorecards",
                    "Document specific examples for each score"
                ])
            
            recommendations.append({
                "priority": priority,
                "category": "interviewer_coaching",
                "title": f"Coach Interviewer {interviewer_id}",
                "description": f"Address issues: {', '.join(issues)}",
                "actions": list(set(actions))  # Remove duplicates
            })
        
        # Calibration recommendations
        calibration_analysis = analysis.get("calibration_analysis", {})
        if calibration_analysis.get("calibration_quality") in ["fair", "poor"]:
            recommendations.append({
                "priority": "high",
                "category": "calibration_improvement",
                "title": "Improve Interview Calibration",
                "description": f"Current calibration quality: {calibration_analysis.get('calibration_quality')}",
                "actions": [
                    "Conduct monthly calibration sessions",
                    "Create shared examples of good/poor answers",
                    "Implement mandatory interviewer shadowing",
                    "Standardize scoring rubrics across all interviewers",
                    "Review and align on role expectations"
                ]
            })
        
        # Scoring pattern recommendations
        scoring_analysis = analysis.get("scoring_analysis", {})
        if scoring_analysis.get("overall_assessment") in ["concerning", "poor"]:
            recommendations.append({
                "priority": "medium",
                "category": "scoring_standards",
                "title": "Adjust Scoring Standards",
                "description": "Scoring patterns deviate significantly from expected distribution",
                "actions": [
                    "Review and communicate target score distributions",
                    "Provide examples for each score level",
                    "Monitor pass rates by role level",
                    "Adjust hiring bar if consistently too high/low"
                ]
            })
        
        # Health score recommendations
        health_score = analysis.get("calibration_health_score", {})
        priorities = health_score.get("improvement_priority", [])
        
        if "bias" in priorities:
            recommendations.append({
                "priority": "critical",
                "category": "bias_mitigation", 
                "title": "Implement Comprehensive Bias Mitigation",
                "description": "Multiple bias indicators detected across the hiring process",
                "actions": [
                    "Mandatory unconscious bias training for all interviewers",
                    "Implement structured interview protocols",
                    "Diversify interview panels",
                    "Regular bias audits and monitoring",
                    "Create accountability metrics for fair hiring"
                ]
            })
        
        # Sort by priority
        priority_order = {"critical": 0, "high": 1, "medium": 2, "low": 3}
        recommendations.sort(key=lambda x: priority_order.get(x["priority"], 3))
        
        return recommendations
    
    def _generate_demographic_bias_recommendation(self, demographic: str, bias_details: Dict[str, Any]) -> str:
        """Generate specific recommendation for demographic bias."""
        if "hire_rate_disparity" in bias_details:
            return f"Significant hire rate disparity detected for {demographic}. Implement structured interviews and diverse panels."
        elif "scoring_disparity" in bias_details:
            return f"Scoring disparity detected for {demographic}. Provide unconscious bias training and standardize evaluation criteria."
        else:
            return f"Potential bias detected for {demographic}. Monitor closely and implement bias mitigation strategies."
    
    def _generate_interviewer_recommendations(self, outlier_interviewers: Dict[str, Any]) -> List[str]:
        """Generate recommendations for interviewer issues."""
        if not outlier_interviewers:
            return ["All interviewers performing within expected ranges"]
        
        recommendations = []
        for interviewer, info in outlier_interviewers.items():
            issues = info["issues"]
            if len(issues) >= 2:
                recommendations.append(f"Interviewer {interviewer}: Requires comprehensive recalibration - multiple issues detected")
            elif "score_inflation" in issues:
                recommendations.append(f"Interviewer {interviewer}: Provide calibration training on scoring standards")
            elif "hire_rate_deviation" in issues:
                recommendations.append(f"Interviewer {interviewer}: Review hiring bar standards and decision criteria")
        
        return recommendations
    
    def _generate_calibration_recommendations(self, mean_std: float, agreement_rate: float) -> List[str]:
        """Generate calibration improvement recommendations."""
        recommendations = []
        
        if mean_std > self.calibration_standards["interviewer_agreement"]["maximum_std_deviation"]:
            recommendations.append("High score variance detected - implement regular calibration sessions")
            recommendations.append("Create shared examples of scoring standards for each competency")
        
        if agreement_rate < self.calibration_standards["interviewer_agreement"]["agreement_threshold"]:
            recommendations.append("Low interviewer agreement rate - standardize interview questions and evaluation criteria")
            recommendations.append("Implement mandatory interviewer training on consistent evaluation")
        
        if not recommendations:
            recommendations.append("Calibration appears healthy - maintain current practices")
        
        return recommendations
    
    def _assess_scoring_health(self, distribution: Dict[str, Any], mean_score: float, target_mean: float) -> str:
        """Assess overall health of scoring patterns."""
        issues = 0
        
        # Check distribution deviations
        for score_level, analysis in distribution.items():
            if analysis["significant_deviation"]:
                issues += 1
        
        # Check mean deviation
        if abs(mean_score - target_mean) > 0.3:
            issues += 1
        
        if issues == 0:
            return "healthy"
        elif issues <= 2:
            return "concerning"
        else:
            return "poor"
    
    def _generate_trend_insights(self, score_trend: float, hire_rate_trend: float, period_metrics: Dict[str, Any]) -> List[str]:
        """Generate insights from trend analysis."""
        insights = []
        
        if abs(score_trend) > 0.05:
            direction = "increasing" if score_trend > 0 else "decreasing"
            insights.append(f"Significant {direction} trend in average scores over time")
            
            if score_trend > 0:
                insights.append("May indicate score inflation or improving candidate quality")
            else:
                insights.append("May indicate stricter evaluation or declining candidate quality")
        
        if abs(hire_rate_trend) > 0.02:
            direction = "increasing" if hire_rate_trend > 0 else "decreasing"
            insights.append(f"Significant {direction} trend in hire rates over time")
            
            if hire_rate_trend > 0:
                insights.append("Consider if hiring bar has lowered or candidate pool improved")
            else:
                insights.append("Consider if hiring bar has raised or candidate pool declined")
        
        # Check for consistency
        period_values = list(period_metrics.values())
        hire_rates = [p["hire_rate"] for p in period_values]
        hire_rate_variance = statistics.variance(hire_rates) if len(hire_rates) > 1 else 0
        
        if hire_rate_variance > 0.01:  # High variance in hire rates
            insights.append("High variance in hire rates across periods - consider process standardization")
        
        if not insights:
            insights.append("Hiring patterns appear stable over time")
        
        return insights
    
    def _analyze_single_interviewer_consistency(self, data: List[Dict[str, Any]]) -> Dict[str, Any]:
        """Analyze consistency for single-interviewer candidates."""
        # Look at consistency within individual interviewers
        interviewer_scores = defaultdict(list)
        
        for record in data:
            interviewer_scores[record["interviewer_id"]].extend(record["scores"].values())
        
        consistency_analysis = {}
        for interviewer, scores in interviewer_scores.items():
            if len(scores) >= 10:  # Need sufficient data
                consistency_analysis[interviewer] = {
                    "mean_score": round(statistics.mean(scores), 2),
                    "std_score": round(statistics.stdev(scores), 2),
                    "coefficient_of_variation": round(statistics.stdev(scores) / statistics.mean(scores), 2),
                    "total_scores": len(scores)
                }
        
        return consistency_analysis


def format_human_readable(calibration_report: Dict[str, Any]) -> str:
    """Format calibration report in human-readable format."""
    output = []
    
    # Header
    output.append("HIRING CALIBRATION ANALYSIS REPORT")
    output.append("=" * 60)
    output.append(f"Analysis Type: {calibration_report.get('analysis_type', 'N/A').title()}")
    output.append(f"Generated: {calibration_report.get('generated_at', 'N/A')}")
    
    if "error" in calibration_report:
        output.append(f"\nError: {calibration_report['error']}")
        return "\n".join(output)
    
    # Data Summary
    data_summary = calibration_report.get("data_summary", {})
    if data_summary:
        output.append(f"\nDATA SUMMARY")
        output.append("-" * 30)
        output.append(f"Total Candidates: {data_summary.get('total_candidates', 0)}")
        output.append(f"Unique Interviewers: {data_summary.get('unique_interviewers', 0)}")
        output.append(f"Overall Hire Rate: {data_summary.get('hire_rate', 0):.1%}")
        
        score_stats = data_summary.get("score_statistics", {})
        output.append(f"Average Score: {score_stats.get('mean_average_scores', 0):.2f}")
        output.append(f"Score Std Dev: {score_stats.get('std_average_scores', 0):.2f}")
    
    # Health Score
    health_score = calibration_report.get("calibration_health_score", {})
    if health_score:
        output.append(f"\nCALIBRATION HEALTH SCORE")
        output.append("-" * 30)
        output.append(f"Overall Score: {health_score.get('overall_score', 0):.3f}")
        output.append(f"Health Category: {health_score.get('health_category', 'Unknown').title()}")
        
        if health_score.get("improvement_priority"):
            output.append(f"Priority Areas: {', '.join(health_score['improvement_priority'])}")
    
    # Bias Analysis
    bias_analysis = calibration_report.get("bias_analysis", {})
    if bias_analysis:
        output.append(f"\nBIAS ANALYSIS")
        output.append("-" * 30)
        output.append(f"Overall Bias Score: {bias_analysis.get('overall_bias_score', 0):.3f}")
        
        # Demographic bias
        demographic_bias = bias_analysis.get("demographic_bias", {})
        if demographic_bias:
            output.append(f"\nDemographic Bias Issues:")
            for demo, analysis in demographic_bias.items():
                output.append(f"  • {demo.replace('_', ' ').title()}: {analysis.get('bias_details', {}).keys()}")
        
        # Interviewer bias
        interviewer_bias = bias_analysis.get("interviewer_bias", {})
        outlier_interviewers = interviewer_bias.get("outlier_interviewers", {})
        if outlier_interviewers:
            output.append(f"\nOutlier Interviewers:")
            for interviewer, info in outlier_interviewers.items():
                issues = ", ".join(info["issues"])
                output.append(f"  • {interviewer}: {issues}")
    
    # Calibration Analysis
    calibration_analysis = calibration_report.get("calibration_analysis", {})
    if calibration_analysis and "error" not in calibration_analysis:
        output.append(f"\nCALIBRATION CONSISTENCY")
        output.append("-" * 30)
        output.append(f"Quality: {calibration_analysis.get('calibration_quality', 'Unknown').title()}")
        output.append(f"Agreement Rate: {calibration_analysis.get('agreement_within_one_point_rate', 0):.1%}")
        output.append(f"Score Std Dev: {calibration_analysis.get('mean_score_standard_deviation', 0):.3f}")
    
    # Scoring Analysis
    scoring_analysis = calibration_report.get("scoring_analysis", {})
    if scoring_analysis:
        output.append(f"\nSCORING PATTERNS")
        output.append("-" * 30)
        output.append(f"Overall Assessment: {scoring_analysis.get('overall_assessment', 'Unknown').title()}")
        
        score_stats = scoring_analysis.get("score_statistics", {})
        output.append(f"Mean Score: {score_stats.get('mean_score', 0):.2f} (Target: {score_stats.get('target_mean', 0):.2f})")
        
        # Distribution analysis
        distribution = scoring_analysis.get("score_distribution", {})
        if distribution:
            output.append(f"\nScore Distribution vs Expected:")
            for score in ["1", "2", "3", "4"]:
                if score in distribution:
                    actual = distribution[score]["actual_percentage"]
                    expected = distribution[score]["expected_percentage"]
                    output.append(f"  Score {score}: {actual:.1%} (Expected: {expected:.1%})")
    
    # Top Recommendations
    recommendations = calibration_report.get("recommendations", [])
    if recommendations:
        output.append(f"\nTOP RECOMMENDATIONS")
        output.append("-" * 30)
        for i, rec in enumerate(recommendations[:5], 1):  # Show top 5
            output.append(f"{i}. {rec['title']} ({rec['priority'].title()} Priority)")
            output.append(f"   {rec['description']}")
            if rec.get('actions'):
                output.append(f"   Actions: {len(rec['actions'])} specific action items")
    
    return "\n".join(output)


def main():
    parser = argparse.ArgumentParser(description="Analyze interview data for bias and calibration issues")
    parser.add_argument("--input", type=str, required=True, help="Input JSON file with interview results data")
    parser.add_argument("--analysis-type", type=str, choices=["comprehensive", "bias", "calibration", "interviewer", "scoring"], 
                       default="comprehensive", help="Type of analysis to perform")
    parser.add_argument("--competencies", type=str, help="Comma-separated list of competencies to focus on")
    parser.add_argument("--trend-analysis", action="store_true", help="Perform trend analysis over time")
    parser.add_argument("--period", type=str, choices=["daily", "weekly", "monthly", "quarterly"], 
                       default="monthly", help="Time period for trend analysis")
    parser.add_argument("--output", type=str, help="Output file path")
    parser.add_argument("--format", choices=["json", "text", "both"], default="both", help="Output format")
    
    args = parser.parse_args()
    
    # Load input data
    try:
        with open(args.input, 'r') as f:
            interview_data = json.load(f)
        
        if not isinstance(interview_data, list):
            print("Error: Input data must be a JSON array of interview records")
            sys.exit(1)
    except FileNotFoundError:
        print(f"Error: Input file '{args.input}' not found")
        sys.exit(1)
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON in input file: {e}")
        sys.exit(1)
    except Exception as e:
        print(f"Error reading input file: {e}")
        sys.exit(1)
    
    # Initialize calibrator and run analysis
    calibrator = HiringCalibrator()
    
    competencies = args.competencies.split(',') if args.competencies else None
    
    try:
        results = calibrator.analyze_hiring_calibration(
            interview_data=interview_data,
            analysis_type=args.analysis_type,
            competencies=competencies,
            trend_analysis=args.trend_analysis,
            period=args.period
        )
        
        # Handle output
        if args.output:
            output_path = args.output
            json_path = output_path if output_path.endswith('.json') else f"{output_path}.json"
            text_path = output_path.replace('.json', '.txt') if output_path.endswith('.json') else f"{output_path}.txt"
        else:
            base_filename = f"calibration_report_{datetime.now().strftime('%Y%m%d_%H%M%S')}"
            json_path = f"{base_filename}.json"
            text_path = f"{base_filename}.txt"
        
        # Write outputs
        if args.format in ["json", "both"]:
            with open(json_path, 'w') as f:
                json.dump(results, f, indent=2, default=str)
            print(f"JSON report written to: {json_path}")
        
        if args.format in ["text", "both"]:
            with open(text_path, 'w') as f:
                f.write(format_human_readable(results))
            print(f"Text report written to: {text_path}")
        
        # Print summary
        print(f"\nCalibration Analysis Summary:")
        if "error" in results:
            print(f"Error: {results['error']}")
        else:
            health_score = results.get("calibration_health_score", {})
            print(f"Health Score: {health_score.get('overall_score', 0):.3f} ({health_score.get('health_category', 'Unknown').title()})")
            
            bias_score = results.get("bias_analysis", {}).get("overall_bias_score", 0)
            print(f"Bias Score: {bias_score:.3f} (Lower is better)")
            
            recommendations = results.get("recommendations", [])
            print(f"Recommendations Generated: {len(recommendations)}")
            
            if recommendations:
                print(f"Top Priority: {recommendations[0]['title']} ({recommendations[0]['priority'].title()})")
        
    except Exception as e:
        print(f"Error during analysis: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()