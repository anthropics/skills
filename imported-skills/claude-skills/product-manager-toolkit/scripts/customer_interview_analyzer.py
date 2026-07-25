#!/usr/bin/env python3
"""
Customer Interview Analyzer
Extracts insights, patterns, and opportunities from user interviews
"""

import re
from typing import Dict, List, Tuple, Set
from collections import Counter, defaultdict
import json

class InterviewAnalyzer:
    """Analyze customer interviews for insights and patterns"""
    
    def __init__(self):
        # Pain point indicators
        self.pain_indicators = [
            'frustrat', 'annoy', 'difficult', 'hard', 'confus', 'slow',
            'problem', 'issue', 'struggle', 'challeng', 'pain', 'waste',
            'manual', 'repetitive', 'tedious', 'boring', 'time-consuming',
            'complicated', 'complex', 'unclear', 'wish', 'need', 'want'
        ]
        
        # Positive indicators
        self.delight_indicators = [
            'love', 'great', 'awesome', 'amazing', 'perfect', 'easy',
            'simple', 'quick', 'fast', 'helpful', 'useful', 'valuable',
            'save', 'efficient', 'convenient', 'intuitive', 'clear'
        ]
        
        # Feature request indicators
        self.request_indicators = [
            'would be nice', 'wish', 'hope', 'want', 'need', 'should',
            'could', 'would love', 'if only', 'it would help', 'suggest',
            'recommend', 'idea', 'what if', 'have you considered'
        ]
        
        # Jobs to be done patterns
        self.jtbd_patterns = [
            r'when i\s+(.+?),\s+i want to\s+(.+?)\s+so that\s+(.+)',
            r'i need to\s+(.+?)\s+because\s+(.+)',
            r'my goal is to\s+(.+)',
            r'i\'m trying to\s+(.+)',
            r'i use \w+ to\s+(.+)',
            r'helps me\s+(.+)',
        ]
    
    def analyze_interview(self, text: str) -> Dict:
        """Analyze a single interview transcript"""
        text_lower = text.lower()
        sentences = self._split_sentences(text)
        
        analysis = {
            'pain_points': self._extract_pain_points(sentences),
            'delights': self._extract_delights(sentences),
            'feature_requests': self._extract_requests(sentences),
            'jobs_to_be_done': self._extract_jtbd(text_lower),
            'sentiment_score': self._calculate_sentiment(text_lower),
            'key_themes': self._extract_themes(text_lower),
            'quotes': self._extract_key_quotes(sentences),
            'metrics_mentioned': self._extract_metrics(text),
            'competitors_mentioned': self._extract_competitors(text)
        }
        
        return analysis
    
    def _split_sentences(self, text: str) -> List[str]:
        """Split text into sentences"""
        # Simple sentence splitting
        sentences = re.split(r'[.!?]+', text)
        return [s.strip() for s in sentences if s.strip()]
    
    def _extract_pain_points(self, sentences: List[str]) -> List[Dict]:
        """Extract pain points from sentences"""
        pain_points = []
        
        for sentence in sentences:
            sentence_lower = sentence.lower()
            for indicator in self.pain_indicators:
                if indicator in sentence_lower:
                    # Extract context around the pain point
                    pain_points.append({
                        'quote': sentence,
                        'indicator': indicator,
                        'severity': self._assess_severity(sentence_lower)
                    })
                    break
        
        return pain_points[:10]  # Return top 10
    
    def _extract_delights(self, sentences: List[str]) -> List[Dict]:
        """Extract positive feedback"""
        delights = []
        
        for sentence in sentences:
            sentence_lower = sentence.lower()
            for indicator in self.delight_indicators:
                if indicator in sentence_lower:
                    delights.append({
                        'quote': sentence,
                        'indicator': indicator,
                        'strength': self._assess_strength(sentence_lower)
                    })
                    break
        
        return delights[:10]
    
    def _extract_requests(self, sentences: List[str]) -> List[Dict]:
        """Extract feature requests and suggestions"""
        requests = []
        
        for sentence in sentences:
            sentence_lower = sentence.lower()
            for indicator in self.request_indicators:
                if indicator in sentence_lower:
                    requests.append({
                        'quote': sentence,
                        'type': self._classify_request(sentence_lower),
                        'priority': self._assess_request_priority(sentence_lower)
                    })
                    break
        
        return requests[:10]
    
    def _extract_jtbd(self, text: str) -> List[Dict]:
        """Extract Jobs to Be Done patterns"""
        jobs = []
        
        for pattern in self.jtbd_patterns:
            matches = re.findall(pattern, text, re.IGNORECASE)
            for match in matches:
                if isinstance(match, tuple):
                    job = ' → '.join(match)
                else:
                    job = match
                
                jobs.append({
                    'job': job,
                    'pattern': pattern.pattern if hasattr(pattern, 'pattern') else pattern
                })
        
        return jobs[:5]
    
    def _calculate_sentiment(self, text: str) -> Dict:
        """Calculate overall sentiment of the interview"""
        positive_count = sum(1 for ind in self.delight_indicators if ind in text)
        negative_count = sum(1 for ind in self.pain_indicators if ind in text)
        
        total = positive_count + negative_count
        if total == 0:
            sentiment_score = 0
        else:
            sentiment_score = (positive_count - negative_count) / total
        
        if sentiment_score > 0.3:
            sentiment_label = 'positive'
        elif sentiment_score < -0.3:
            sentiment_label = 'negative'
        else:
            sentiment_label = 'neutral'
        
        return {
            'score': round(sentiment_score, 2),
            'label': sentiment_label,
            'positive_signals': positive_count,
            'negative_signals': negative_count
        }
    
    def _extract_themes(self, text: str) -> List[str]:
        """Extract key themes using word frequency"""
        # Remove common words
        stop_words = {'the', 'a', 'an', 'and', 'or', 'but', 'in', 'on', 'at',
                     'to', 'for', 'of', 'with', 'by', 'from', 'as', 'is',
                     'was', 'are', 'were', 'been', 'be', 'have', 'has',
                     'had', 'do', 'does', 'did', 'will', 'would', 'could',
                     'should', 'may', 'might', 'must', 'can', 'shall',
                     'it', 'i', 'you', 'we', 'they', 'them', 'their'}
        
        # Extract meaningful words
        words = re.findall(r'\b[a-z]{4,}\b', text)
        meaningful_words = [w for w in words if w not in stop_words]
        
        # Count frequency
        word_freq = Counter(meaningful_words)
        
        # Extract themes (top frequent meaningful words)
        themes = [word for word, count in word_freq.most_common(10) if count >= 3]
        
        return themes
    
    def _extract_key_quotes(self, sentences: List[str]) -> List[str]:
        """Extract the most insightful quotes"""
        scored_sentences = []
        
        for sentence in sentences:
            if len(sentence) < 20 or len(sentence) > 200:
                continue
            
            score = 0
            sentence_lower = sentence.lower()
            
            # Score based on insight indicators
            if any(ind in sentence_lower for ind in self.pain_indicators):
                score += 2
            if any(ind in sentence_lower for ind in self.request_indicators):
                score += 2
            if 'because' in sentence_lower:
                score += 1
            if 'but' in sentence_lower:
                score += 1
            if '?' in sentence:
                score += 1
            
            if score > 0:
                scored_sentences.append((score, sentence))
        
        # Sort by score and return top quotes
        scored_sentences.sort(reverse=True)
        return [s[1] for s in scored_sentences[:5]]
    
    def _extract_metrics(self, text: str) -> List[str]:
        """Extract any metrics or numbers mentioned"""
        metrics = []
        
        # Find percentages
        percentages = re.findall(r'\d+%', text)
        metrics.extend(percentages)
        
        # Find time metrics
        time_metrics = re.findall(r'\d+\s*(?:hours?|minutes?|days?|weeks?|months?)', text, re.IGNORECASE)
        metrics.extend(time_metrics)
        
        # Find money metrics
        money_metrics = re.findall(r'\$[\d,]+', text)
        metrics.extend(money_metrics)
        
        # Find general numbers with context
        number_contexts = re.findall(r'(\d+)\s+(\w+)', text)
        for num, context in number_contexts:
            if context.lower() not in ['the', 'a', 'an', 'and', 'or', 'of']:
                metrics.append(f"{num} {context}")
        
        return list(set(metrics))[:10]
    
    def _extract_competitors(self, text: str) -> List[str]:
        """Extract competitor mentions"""
        # Common competitor indicators
        competitor_patterns = [
            r'(?:use|used|using|tried|trying|switch from|switched from|instead of)\s+(\w+)',
            r'(\w+)\s+(?:is better|works better|is easier)',
            r'compared to\s+(\w+)',
            r'like\s+(\w+)',
            r'similar to\s+(\w+)',
        ]
        
        competitors = set()
        for pattern in competitor_patterns:
            matches = re.findall(pattern, text, re.IGNORECASE)
            competitors.update(matches)
        
        # Filter out common words
        common_words = {'this', 'that', 'it', 'them', 'other', 'another', 'something'}
        competitors = [c for c in competitors if c.lower() not in common_words and len(c) > 2]
        
        return list(competitors)[:5]
    
    def _assess_severity(self, text: str) -> str:
        """Assess severity of pain point"""
        if any(word in text for word in ['very', 'extremely', 'really', 'totally', 'completely']):
            return 'high'
        elif any(word in text for word in ['somewhat', 'bit', 'little', 'slightly']):
            return 'low'
        return 'medium'
    
    def _assess_strength(self, text: str) -> str:
        """Assess strength of positive feedback"""
        if any(word in text for word in ['absolutely', 'definitely', 'really', 'very']):
            return 'strong'
        return 'moderate'
    
    def _classify_request(self, text: str) -> str:
        """Classify the type of request"""
        if any(word in text for word in ['ui', 'design', 'look', 'color', 'layout']):
            return 'ui_improvement'
        elif any(word in text for word in ['feature', 'add', 'new', 'build']):
            return 'new_feature'
        elif any(word in text for word in ['fix', 'bug', 'broken', 'work']):
            return 'bug_fix'
        elif any(word in text for word in ['faster', 'slow', 'performance', 'speed']):
            return 'performance'
        return 'general'
    
    def _assess_request_priority(self, text: str) -> str:
        """Assess priority of request"""
        if any(word in text for word in ['critical', 'urgent', 'asap', 'immediately', 'blocking']):
            return 'critical'
        elif any(word in text for word in ['need', 'important', 'should', 'must']):
            return 'high'
        elif any(word in text for word in ['nice', 'would', 'could', 'maybe']):
            return 'low'
        return 'medium'

def aggregate_interviews(interviews: List[Dict]) -> Dict:
    """Aggregate insights from multiple interviews"""
    aggregated = {
        'total_interviews': len(interviews),
        'common_pain_points': defaultdict(list),
        'common_requests': defaultdict(list),
        'jobs_to_be_done': [],
        'overall_sentiment': {
            'positive': 0,
            'negative': 0,
            'neutral': 0
        },
        'top_themes': Counter(),
        'metrics_summary': set(),
        'competitors_mentioned': Counter()
    }
    
    for interview in interviews:
        # Aggregate pain points
        for pain in interview.get('pain_points', []):
            indicator = pain.get('indicator', 'unknown')
            aggregated['common_pain_points'][indicator].append(pain['quote'])
        
        # Aggregate requests
        for request in interview.get('feature_requests', []):
            req_type = request.get('type', 'general')
            aggregated['common_requests'][req_type].append(request['quote'])
        
        # Aggregate JTBD
        aggregated['jobs_to_be_done'].extend(interview.get('jobs_to_be_done', []))
        
        # Aggregate sentiment
        sentiment = interview.get('sentiment_score', {}).get('label', 'neutral')
        aggregated['overall_sentiment'][sentiment] += 1
        
        # Aggregate themes
        for theme in interview.get('key_themes', []):
            aggregated['top_themes'][theme] += 1
        
        # Aggregate metrics
        aggregated['metrics_summary'].update(interview.get('metrics_mentioned', []))
        
        # Aggregate competitors
        for competitor in interview.get('competitors_mentioned', []):
            aggregated['competitors_mentioned'][competitor] += 1
    
    # Process aggregated data
    aggregated['common_pain_points'] = dict(aggregated['common_pain_points'])
    aggregated['common_requests'] = dict(aggregated['common_requests'])
    aggregated['top_themes'] = dict(aggregated['top_themes'].most_common(10))
    aggregated['metrics_summary'] = list(aggregated['metrics_summary'])
    aggregated['competitors_mentioned'] = dict(aggregated['competitors_mentioned'])
    
    return aggregated

def format_single_interview(analysis: Dict) -> str:
    """Format single interview analysis"""
    output = ["=" * 60]
    output.append("CUSTOMER INTERVIEW ANALYSIS")
    output.append("=" * 60)
    
    # Sentiment
    sentiment = analysis['sentiment_score']
    output.append(f"\n📊 Overall Sentiment: {sentiment['label'].upper()}")
    output.append(f"   Score: {sentiment['score']}")
    output.append(f"   Positive signals: {sentiment['positive_signals']}")
    output.append(f"   Negative signals: {sentiment['negative_signals']}")
    
    # Pain Points
    if analysis['pain_points']:
        output.append("\n🔥 Pain Points Identified:")
        for i, pain in enumerate(analysis['pain_points'][:5], 1):
            output.append(f"\n{i}. [{pain['severity'].upper()}] {pain['quote'][:100]}...")
    
    # Feature Requests
    if analysis['feature_requests']:
        output.append("\n💡 Feature Requests:")
        for i, req in enumerate(analysis['feature_requests'][:5], 1):
            output.append(f"\n{i}. [{req['type']}] Priority: {req['priority']}")
            output.append(f"   \"{req['quote'][:100]}...\"")
    
    # Jobs to Be Done
    if analysis['jobs_to_be_done']:
        output.append("\n🎯 Jobs to Be Done:")
        for i, job in enumerate(analysis['jobs_to_be_done'], 1):
            output.append(f"{i}. {job['job']}")
    
    # Key Themes
    if analysis['key_themes']:
        output.append("\n🏷️ Key Themes:")
        output.append(", ".join(analysis['key_themes']))
    
    # Key Quotes
    if analysis['quotes']:
        output.append("\n💬 Key Quotes:")
        for i, quote in enumerate(analysis['quotes'][:3], 1):
            output.append(f'{i}. "{quote}"')
    
    # Metrics
    if analysis['metrics_mentioned']:
        output.append("\n📈 Metrics Mentioned:")
        output.append(", ".join(analysis['metrics_mentioned']))
    
    # Competitors
    if analysis['competitors_mentioned']:
        output.append("\n🏢 Competitors Mentioned:")
        output.append(", ".join(analysis['competitors_mentioned']))
    
    return "\n".join(output)

def main():
    import sys
    import argparse

    parser = argparse.ArgumentParser(
        description="Customer Interview Analyzer - Extracts insights, patterns, and opportunities from user interviews"
    )
    parser.add_argument(
        "file", nargs="?", default=None,
        help="Interview transcript text file to analyze"
    )
    parser.add_argument(
        "--json", action="store_true",
        help="Output results as JSON"
    )
    args = parser.parse_args()

    if not args.file:
        print("Usage: python customer_interview_analyzer.py <interview_file.txt>")
        print("\nThis tool analyzes customer interview transcripts to extract:")
        print("  - Pain points and frustrations")
        print("  - Feature requests and suggestions")
        print("  - Jobs to be done")
        print("  - Sentiment analysis")
        print("  - Key themes and quotes")
        sys.exit(1)

    with open(args.file, 'r') as f:
        interview_text = f.read()

    analyzer = InterviewAnalyzer()
    analysis = analyzer.analyze_interview(interview_text)

    if args.json:
        print(json.dumps(analysis, indent=2))
    else:
        print(format_single_interview(analysis))

if __name__ == "__main__":
    main()
