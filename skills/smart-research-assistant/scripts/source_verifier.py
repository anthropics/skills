#!/usr/bin/env python3
"""
Source Verification Script for Research Skills

This script helps verify the credibility and reliability of online sources
using various fact-checking techniques and source evaluation methods.
"""

import requests
import json
import re
from datetime import datetime
from urllib.parse import urlparse
import sys

class SourceVerifier:
    def __init__(self):
        self.fact_check_apis = {
            'google_fact_check': 'https://factchecktools.googleapis.com/v1alpha1/claims:search',
            'media_bias': 'https://mediabiasfactcheck.com/api/',
        }
        
        self.credible_domains = [
            'reuters.com', 'ap.org', 'bbc.com', 'npr.org', 'pbs.org',
            'nytimes.com', 'washingtonpost.com', 'wsj.com', 'theguardian.com',
            'nature.com', 'science.org', 'pnas.org', 'cell.com', 'lancet.com'
        ]
        
        self.suspicious_patterns = [
            r'clickbait|shocking|unbelievable|incredible',
            r'you won\'t believe|must see|breaking.*news',
            r'conspiracy|cover.*up|hidden.*truth',
            r'miracle|cure.*all|instant.*result'
        ]

    def check_url_credibility(self, url):
        """Check basic credibility indicators of a URL"""
        try:
            parsed = urlparse(url)
            domain = parsed.netloc.lower()
            
            credibility_score = 0
            checks = {}
            
            # Check against credible domains list
            checks['credible_domain'] = any(cred in domain for cred in self.credible_domains)
            if checks['credible_domain']:
                credibility_score += 30
            
            # Check for HTTPS
            checks['has_https'] = parsed.scheme == 'https'
            if checks['has_https']:
                credibility_score += 10
            
            # Check for suspicious patterns in URL
            checks['suspicious_url'] = any(re.search(pattern, url, re.IGNORECASE) 
                                          for pattern in self.suspicious_patterns)
            if checks['suspicious_url']:
                credibility_score -= 20
            
            # Check domain age (simplified)
            checks['established_domain'] = len(domain.split('.')) >= 2 and not any(temp in domain 
                                        for temp in ['blog', 'wordpress', 'medium', 'substack'])
            if checks['established_domain']:
                credibility_score += 15
            
            return {
                'score': max(0, min(100, credibility_score)),
                'checks': checks,
                'domain': domain
            }
            
        except Exception as e:
            return {'error': str(e), 'score': 0}

    def analyze_content_credibility(self, content):
        """Analyze text content for credibility indicators"""
        analysis = {
            'word_count': len(content.split()),
            'caps_ratio': sum(1 for c in content if c.isupper()) / len(content) if content else 0,
            'exclamation_count': content.count('!'),
            'question_count': content.count('?'),
            'citation_count': len(re.findall(r'\[\d+\]|\(\d{4}\)|\w+ \d{4}', content)),
            'sensational_words': 0,
            'objective_language': 0
        }
        
        # Check for sensational language
        sensational_words = ['shocking', 'unbelievable', 'incredible', 'amazing', 
                            'miracle', 'breakthrough', 'revolutionary']
        analysis['sensational_words'] = sum(1 for word in sensational_words 
                                          if word.lower() in content.lower())
        
        # Check for objective language indicators
        objective_phrases = ['according to', 'research shows', 'data indicates', 
                           'studies suggest', 'evidence points']
        analysis['objective_language'] = sum(1 for phrase in objective_phrases 
                                           if phrase.lower() in content.lower())
        
        # Calculate credibility score
        score = 50  # Base score
        
        # Positive indicators
        if analysis['word_count'] > 300:
            score += 10
        if analysis['citation_count'] > 0:
            score += analysis['citation_count'] * 5
        if analysis['objective_language'] > 0:
            score += analysis['objective_language'] * 3
        
        # Negative indicators
        if analysis['caps_ratio'] > 0.1:
            score -= 15
        if analysis['exclamation_count'] > 3:
            score -= 10
        if analysis['sensational_words'] > 2:
            score -= analysis['sensational_words'] * 5
        
        analysis['credibility_score'] = max(0, min(100, score))
        
        return analysis

    def check_source_reputation(self, source_name):
        """Check source reputation using available APIs"""
        reputation_data = {
            'source': source_name,
            'bias_rating': 'unknown',
            'factual_reporting': 'unknown',
            'credibility_score': 50
        }
        
        # Note: In a real implementation, this would call actual APIs
        # For now, we'll use a simplified heuristic approach
        
        known_sources = {
            'reuters': {'bias': 'center', 'factual': 'very_high', 'score': 95},
            'associated press': {'bias': 'center', 'factual': 'very_high', 'score': 95},
            'bbc': {'bias': 'center', 'factual': 'high', 'score': 90},
            'new york times': {'bias': 'center-left', 'factual': 'high', 'score': 85},
            'wall street journal': {'bias': 'center-right', 'factual': 'high', 'score': 85},
            'fox news': {'bias': 'right', 'factual': 'mixed', 'score': 65},
            'cnn': {'bias': 'center-left', 'factual': 'mixed', 'score': 70},
        }
        
        source_key = source_name.lower()
        if source_key in known_sources:
            reputation_data.update(known_sources[source_key])
        
        return reputation_data

    def generate_verification_report(self, url, content=None, source_name=None):
        """Generate comprehensive verification report"""
        report = {
            'timestamp': datetime.now().isoformat(),
            'url': url,
            'overall_score': 0,
            'recommendations': [],
            'warnings': []
        }
        
        # URL credibility check
        url_analysis = self.check_url_credibility(url)
        report['url_analysis'] = url_analysis
        
        # Content analysis if provided
        if content:
            content_analysis = self.analyze_content_credibility(content)
            report['content_analysis'] = content_analysis
        
        # Source reputation if provided
        if source_name:
            source_reputation = self.check_source_reputation(source_name)
            report['source_reputation'] = source_reputation
        
        # Calculate overall score
        scores = [url_analysis.get('score', 50)]
        if 'content_analysis' in report:
            scores.append(report['content_analysis']['credibility_score'])
        if 'source_reputation' in report:
            scores.append(report['source_reputation']['credibility_score'])
        
        report['overall_score'] = sum(scores) / len(scores)
        
        # Generate recommendations
        if report['overall_score'] < 30:
            report['warnings'].append('Low credibility score - seek alternative sources')
            report['recommendations'].append('Verify information with multiple credible sources')
        elif report['overall_score'] < 60:
            report['warnings'].append('Medium credibility - exercise caution')
            report['recommendations'].append('Cross-reference with other sources')
        else:
            report['recommendations'].append('Source appears credible - still verify key claims')
        
        return report

def main():
    """Command line interface for source verification"""
    if len(sys.argv) < 2:
        print("Usage: python source_verifier.py <URL> [content_file] [source_name]")
        sys.exit(1)
    
    url = sys.argv[1]
    content = None
    source_name = None
    
    if len(sys.argv) > 2:
        try:
            with open(sys.argv[2], 'r', encoding='utf-8') as f:
                content = f.read()
        except FileNotFoundError:
            print(f"Content file {sys.argv[2]} not found")
    
    if len(sys.argv) > 3:
        source_name = sys.argv[3]
    
    verifier = SourceVerifier()
    report = verifier.generate_verification_report(url, content, source_name)
    
    print("=== Source Verification Report ===")
    print(f"URL: {report['url']}")
    print(f"Overall Credibility Score: {report['overall_score']:.1f}/100")
    print(f"Timestamp: {report['timestamp']}")
    
    if 'warnings' in report and report['warnings']:
        print("\n⚠️  Warnings:")
        for warning in report['warnings']:
            print(f"  - {warning}")
    
    if 'recommendations' in report and report['recommendations']:
        print("\n💡 Recommendations:")
        for rec in report['recommendations']:
            print(f"  - {rec}")
    
    print(f"\n📊 Detailed Analysis:")
    print(f"  URL Score: {report['url_analysis']['score']}/100")
    
    if 'content_analysis' in report:
        print(f"  Content Score: {report['content_analysis']['credibility_score']}/100")
    
    if 'source_reputation' in report:
        print(f"  Source Score: {report['source_reputation']['credibility_score']}/100")
    
    # Save detailed report
    with open('verification_report.json', 'w', encoding='utf-8') as f:
        json.dump(report, f, indent=2, ensure_ascii=False)
    
    print(f"\n📄 Detailed report saved to: verification_report.json")

if __name__ == "__main__":
    main()