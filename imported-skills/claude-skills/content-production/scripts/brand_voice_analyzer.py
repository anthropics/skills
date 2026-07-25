#!/usr/bin/env python3
"""
Brand Voice Analyzer - Analyzes content to establish and maintain brand voice consistency
"""

import re
from typing import Dict, List, Tuple
import json

class BrandVoiceAnalyzer:
    def __init__(self):
        self.voice_dimensions = {
            'formality': {
                'formal': ['hereby', 'therefore', 'furthermore', 'pursuant', 'regarding'],
                'casual': ['hey', 'cool', 'awesome', 'stuff', 'yeah', 'gonna']
            },
            'tone': {
                'professional': ['expertise', 'solution', 'optimize', 'leverage', 'strategic'],
                'friendly': ['happy', 'excited', 'love', 'enjoy', 'together', 'share']
            },
            'perspective': {
                'authoritative': ['proven', 'research shows', 'experts agree', 'data indicates'],
                'conversational': ['you might', 'let\'s explore', 'we think', 'imagine if']
            }
        }
    
    def analyze_text(self, text: str) -> Dict:
        """Analyze text for brand voice characteristics"""
        text_lower = text.lower()
        word_count = len(text.split())
        
        results = {
            'word_count': word_count,
            'readability_score': self._calculate_readability(text),
            'voice_profile': {},
            'sentence_analysis': self._analyze_sentences(text),
            'recommendations': []
        }
        
        # Analyze voice dimensions
        for dimension, categories in self.voice_dimensions.items():
            dim_scores = {}
            for category, keywords in categories.items():
                score = sum(1 for keyword in keywords if keyword in text_lower)
                dim_scores[category] = score
            
            # Determine dominant voice
            if sum(dim_scores.values()) > 0:
                dominant = max(dim_scores, key=dim_scores.get)
                results['voice_profile'][dimension] = {
                    'dominant': dominant,
                    'scores': dim_scores
                }
        
        # Generate recommendations
        results['recommendations'] = self._generate_recommendations(results)
        
        return results
    
    def _calculate_readability(self, text: str) -> float:
        """Calculate Flesch Reading Ease score"""
        sentences = re.split(r'[.!?]+', text)
        words = text.split()
        syllables = sum(self._count_syllables(word) for word in words)
        
        if len(sentences) == 0 or len(words) == 0:
            return 0
        
        avg_sentence_length = len(words) / len(sentences)
        avg_syllables_per_word = syllables / len(words)
        
        # Flesch Reading Ease formula
        score = 206.835 - 1.015 * avg_sentence_length - 84.6 * avg_syllables_per_word
        return max(0, min(100, score))
    
    def _count_syllables(self, word: str) -> int:
        """Count syllables in a word (simplified)"""
        word = word.lower()
        vowels = 'aeiou'
        syllable_count = 0
        previous_was_vowel = False
        
        for char in word:
            is_vowel = char in vowels
            if is_vowel and not previous_was_vowel:
                syllable_count += 1
            previous_was_vowel = is_vowel
        
        # Adjust for silent e
        if word.endswith('e'):
            syllable_count -= 1
        
        return max(1, syllable_count)
    
    def _analyze_sentences(self, text: str) -> Dict:
        """Analyze sentence structure"""
        sentences = re.split(r'[.!?]+', text)
        sentences = [s.strip() for s in sentences if s.strip()]
        
        if not sentences:
            return {'average_length': 0, 'variety': 'low'}
        
        lengths = [len(s.split()) for s in sentences]
        avg_length = sum(lengths) / len(lengths) if lengths else 0
        
        # Calculate variety
        if len(set(lengths)) < 3:
            variety = 'low'
        elif len(set(lengths)) < 5:
            variety = 'medium'
        else:
            variety = 'high'
        
        return {
            'average_length': round(avg_length, 1),
            'variety': variety,
            'count': len(sentences)
        }
    
    def _generate_recommendations(self, analysis: Dict) -> List[str]:
        """Generate recommendations based on analysis"""
        recommendations = []
        
        # Readability recommendations
        if analysis['readability_score'] < 30:
            recommendations.append("Consider simplifying language for better readability")
        elif analysis['readability_score'] > 70:
            recommendations.append("Content is very easy to read - consider if this matches your audience")
        
        # Sentence variety
        if analysis['sentence_analysis']['variety'] == 'low':
            recommendations.append("Vary sentence length for better flow and engagement")
        
        # Voice consistency
        if analysis['voice_profile']:
            recommendations.append("Maintain consistent voice across all content")
        
        return recommendations

def analyze_content(content: str, output_format: str = 'json') -> str:
    """Main function to analyze content"""
    analyzer = BrandVoiceAnalyzer()
    results = analyzer.analyze_text(content)
    
    if output_format == 'json':
        return json.dumps(results, indent=2)
    else:
        # Human-readable format
        output = [
            f"=== Brand Voice Analysis ===",
            f"Word Count: {results['word_count']}",
            f"Readability Score: {results['readability_score']:.1f}/100",
            f"",
            f"Voice Profile:"
        ]
        
        for dimension, profile in results['voice_profile'].items():
            output.append(f"  {dimension.title()}: {profile['dominant']}")
        
        output.extend([
            f"",
            f"Sentence Analysis:",
            f"  Average Length: {results['sentence_analysis']['average_length']} words",
            f"  Variety: {results['sentence_analysis']['variety']}",
            f"  Total Sentences: {results['sentence_analysis']['count']}",
            f"",
            f"Recommendations:"
        ])
        
        for rec in results['recommendations']:
            output.append(f"  • {rec}")
        
        return '\n'.join(output)

if __name__ == "__main__":
    import sys
    import argparse

    parser = argparse.ArgumentParser(
        description="Brand Voice Analyzer - Analyzes content to establish and maintain brand voice consistency"
    )
    parser.add_argument(
        "file", nargs="?", default=None,
        help="Text file to analyze"
    )
    parser.add_argument(
        "--format", choices=["json", "text"], default="text",
        help="Output format (default: text)"
    )
    args = parser.parse_args()

    if args.file:
        with open(args.file, 'r') as f:
            content = f.read()
        print(analyze_content(content, args.format))
    else:
        print("Usage: python brand_voice_analyzer.py <file> [--format json|text]")
