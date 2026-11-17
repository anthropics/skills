#!/usr/bin/env python3
"""
Peer Review Integration
Sends completed documents to GPT-5.2 or Gemini for review.

Author: Tyler 'Oooo-pus Pimp-Daddy' Lofall & Claude (A-Team Productions)
"""

from dataclasses import dataclass
from typing import Optional, List, Dict, Any
from datetime import datetime
import json


@dataclass
class ReviewFeedback:
    """Structured feedback from peer review."""
    reviewer: str  # "gpt-5.2" or "gemini"
    timestamp: str
    overall_score: int  # 1-10
    completeness: int  # 1-10 - Are all elements properly structured?
    specificity: int  # 1-10 - Are facts specific enough?
    linkage: int  # 1-10 - Does each fact connect to defendant?
    legal_sufficiency: int  # 1-10 - Would this survive motion to strike?
    consistency: int  # 1-10 - Any internal contradictions?
    issues: List[str]
    suggestions: List[str]
    strengths: List[str]


def generate_review_prompt(document_text: str, document_type: str = "declaration") -> str:
    """Generate the prompt to send to GPT-5.2 for review."""
    
    return f"""You are a legal document peer reviewer. Review this {document_type} for quality and completeness.

DOCUMENT TO REVIEW:
```
{document_text}
```

Evaluate the document on these criteria (score 1-10 for each):

1. COMPLETENESS - Are all elements properly structured (2 circumstances, 2 elements, 1+ party link per fact)?
2. SPECIFICITY - Are facts specific enough to be actionable in court?
3. LINKAGE - Does each fact properly connect to the defendant's liability?
4. LEGAL SUFFICIENCY - Would this survive a motion to strike?
5. CONSISTENCY - Are there any internal contradictions?

Return your review as JSON in this exact format:
{{
    "overall_score": <1-10>,
    "completeness": <1-10>,
    "specificity": <1-10>,
    "linkage": <1-10>,
    "legal_sufficiency": <1-10>,
    "consistency": <1-10>,
    "issues": ["issue 1", "issue 2", ...],
    "suggestions": ["suggestion 1", "suggestion 2", ...],
    "strengths": ["strength 1", "strength 2", ...]
}}

Be thorough but constructive. Focus on actionable improvements.
"""


def parse_review_response(response_text: str, reviewer: str) -> ReviewFeedback:
    """Parse the JSON response from GPT-5.2 or Gemini."""
    
    # Try to extract JSON from response
    try:
        # Handle case where JSON is wrapped in markdown code blocks
        if "```json" in response_text:
            json_start = response_text.find("```json") + 7
            json_end = response_text.find("```", json_start)
            response_text = response_text[json_start:json_end]
        elif "```" in response_text:
            json_start = response_text.find("```") + 3
            json_end = response_text.find("```", json_start)
            response_text = response_text[json_start:json_end]
        
        data = json.loads(response_text.strip())
        
        return ReviewFeedback(
            reviewer=reviewer,
            timestamp=datetime.now().isoformat(),
            overall_score=data.get("overall_score", 0),
            completeness=data.get("completeness", 0),
            specificity=data.get("specificity", 0),
            linkage=data.get("linkage", 0),
            legal_sufficiency=data.get("legal_sufficiency", 0),
            consistency=data.get("consistency", 0),
            issues=data.get("issues", []),
            suggestions=data.get("suggestions", []),
            strengths=data.get("strengths", []),
        )
    except json.JSONDecodeError:
        # Return empty feedback if parsing fails
        return ReviewFeedback(
            reviewer=reviewer,
            timestamp=datetime.now().isoformat(),
            overall_score=0,
            completeness=0,
            specificity=0,
            linkage=0,
            legal_sufficiency=0,
            consistency=0,
            issues=["Failed to parse review response"],
            suggestions=[],
            strengths=[],
        )


def format_feedback_report(feedback: ReviewFeedback) -> str:
    """Format feedback as a readable report."""
    
    lines = [
        "=" * 60,
        f"PEER REVIEW REPORT - {feedback.reviewer.upper()}",
        "=" * 60,
        f"Reviewed: {feedback.timestamp}",
        "",
        "SCORES:",
        f"  Overall:           {feedback.overall_score}/10",
        f"  Completeness:      {feedback.completeness}/10",
        f"  Specificity:       {feedback.specificity}/10",
        f"  Linkage:           {feedback.linkage}/10",
        f"  Legal Sufficiency: {feedback.legal_sufficiency}/10",
        f"  Consistency:       {feedback.consistency}/10",
        "",
    ]
    
    if feedback.strengths:
        lines.append("STRENGTHS:")
        for s in feedback.strengths:
            lines.append(f"  ✓ {s}")
        lines.append("")
    
    if feedback.issues:
        lines.append("ISSUES:")
        for i in feedback.issues:
            lines.append(f"  ✗ {i}")
        lines.append("")
    
    if feedback.suggestions:
        lines.append("SUGGESTIONS:")
        for s in feedback.suggestions:
            lines.append(f"  → {s}")
        lines.append("")
    
    lines.append("=" * 60)
    
    return "\n".join(lines)


# ============================================================================
# GPT-5.2 CLIENT (for integration with council-hub)
# ============================================================================

class GPT52Client:
    """
    Client for GPT-5.2 integration.
    
    Uses the council-hub infrastructure when available,
    or can make direct API calls.
    """
    
    def __init__(self, api_key: Optional[str] = None):
        self.api_key = api_key
        self.model = "gpt-5.2-xhigh"
    
    async def review(self, document_text: str, document_type: str = "declaration") -> ReviewFeedback:
        """
        Send document to GPT-5.2 for review.
        
        In production, this integrates with council-hub.
        For now, returns a placeholder.
        """
        
        prompt = generate_review_prompt(document_text, document_type)
        
        # TODO: Integrate with council-hub OpenAIAdapter
        # For now, return placeholder indicating review needed
        
        return ReviewFeedback(
            reviewer="gpt-5.2",
            timestamp=datetime.now().isoformat(),
            overall_score=0,
            completeness=0,
            specificity=0,
            linkage=0,
            legal_sufficiency=0,
            consistency=0,
            issues=["Review pending - send to GPT-5.2 via council-hub"],
            suggestions=["Use council-hub CouncilEngine for actual review"],
            strengths=[],
        )
    
    def get_review_prompt(self, document_text: str, document_type: str = "declaration") -> str:
        """Get the prompt that would be sent to GPT-5.2."""
        return generate_review_prompt(document_text, document_type)


# ============================================================================
# GEMINI CLIENT (backup reviewer)
# ============================================================================

class GeminiClient:
    """
    Backup reviewer using Gemini.
    """
    
    def __init__(self, api_key: Optional[str] = None):
        self.api_key = api_key
    
    async def review(self, document_text: str, document_type: str = "declaration") -> ReviewFeedback:
        """Send document to Gemini for review."""
        
        # TODO: Implement Gemini API integration
        
        return ReviewFeedback(
            reviewer="gemini",
            timestamp=datetime.now().isoformat(),
            overall_score=0,
            completeness=0,
            specificity=0,
            linkage=0,
            legal_sufficiency=0,
            consistency=0,
            issues=["Gemini review not yet implemented"],
            suggestions=[],
            strengths=[],
        )


# ============================================================================
# MAIN REVIEW FUNCTION
# ============================================================================

async def review_document(
    document_text: str,
    document_type: str = "declaration",
    reviewer: str = "gpt-5.2",
) -> ReviewFeedback:
    """
    Send document for peer review.
    
    Args:
        document_text: The document content to review
        document_type: Type of document (declaration, brief, motion, etc.)
        reviewer: Which model to use (gpt-5.2, gemini)
        
    Returns:
        ReviewFeedback with scores and suggestions
    """
    
    if reviewer == "gpt-5.2":
        client = GPT52Client()
        return await client.review(document_text, document_type)
    elif reviewer == "gemini":
        client = GeminiClient()
        return await client.review(document_text, document_type)
    else:
        raise ValueError(f"Unknown reviewer: {reviewer}")


# ============================================================================
# DEMO
# ============================================================================

if __name__ == "__main__":
    # Demo: Generate review prompt for a sample declaration
    
    sample_doc = """
DECLARATION OF TYLER LOFALL

I, Tyler Lofall, declare under penalty of perjury under the laws of 
the United States and the State of Oregon that the following is true and correct:

FACT 1: FALSE STATEMENTS IN MOTION TO DISMISS

CIRCUMSTANCE 1: In December 2024, Defendants filed a Motion to Dismiss in this matter.
CIRCUMSTANCE 2: Defendants, through their counsel, prepared and submitted the Motion to Dismiss.
ELEMENT 1: Defendants' Motion to Dismiss contained material misrepresentations of fact.
ELEMENT 2: These misrepresentations were made with knowledge of their falsity.
PARTY LINK (Clackamas County): Clackamas County deliberately included material 
misrepresentations in their Motion to Dismiss with intent to deceive this Court.

I declare under penalty of perjury that the foregoing is true and correct.
Executed on December 20, 2024 at Oregon City, Oregon.
"""
    
    prompt = generate_review_prompt(sample_doc, "declaration")
    
    print("=" * 60)
    print("REVIEW PROMPT FOR GPT-5.2")
    print("=" * 60)
    print(prompt[:1000] + "...\n")
    
    # Simulate a review response
    mock_response = json.dumps({
        "overall_score": 7,
        "completeness": 8,
        "specificity": 6,
        "linkage": 8,
        "legal_sufficiency": 7,
        "consistency": 9,
        "issues": [
            "ELEMENT 2 needs more specific supporting details",
            "Missing witness references for Fact 1",
        ],
        "suggestions": [
            "Add specific dates when misrepresentations were made",
            "Include citations to the exact statements in MTD",
            "Add evidence UIDs linking to exhibits",
        ],
        "strengths": [
            "Clear 2+2+1 structure followed",
            "Strong party linkage to Clackamas County",
            "Perjury declaration properly formatted",
        ],
    })
    
    feedback = parse_review_response(mock_response, "gpt-5.2")
    print(format_feedback_report(feedback))
