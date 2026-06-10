#!/usr/bin/env python3
"""
Pimp Slap Card Generator
1980s Batman style courtroom comics for completed legal documents.

"Big Claude Pimpin' Service - Pimp Slap the Otha' Paaaarty!"

Author: Tyler 'Oooo-pus Pimp-Daddy' Lofall & Claude (A-Team Productions)
"""

from dataclasses import dataclass, field
from typing import Optional, List, Dict
from datetime import datetime
from enum import Enum
import hashlib


class CardRarity(Enum):
    COMMON = ("Common", "#888888", "○")
    UNCOMMON = ("Uncommon", "#1eff00", "◐")
    RARE = ("Rare", "#0070dd", "●")
    EPIC = ("Epic", "#a335ee", "★")
    LEGENDARY = ("Legendary", "#ff8000", "✦")
    
    def __init__(self, label: str, color: str, symbol: str):
        self.label = label
        self.color = color
        self.symbol = symbol


class LitigationStage(Enum):
    """Numbered stages - cards ordered by litigation progression."""
    S01_COMPLAINT = ("01", "Complaint", "First Strike")
    S02_ANSWER = ("02", "Answer", "The Response")
    S03_DISCOVERY = ("03", "Discovery", "Uncovering Truth")
    S04_MTD = ("04", "Motion to Dismiss", "Dismissal Deflector")
    S05_MSJ = ("05", "Summary Judgment", "The Slam Dunk")
    S06_OPPOSITION = ("06", "Opposition", "Counter-Slap")
    S07_REPLY = ("07", "Reply", "The Last Word")
    S08_TRIAL_PREP = ("08", "Trial Prep", "Battle Ready")
    S09_TRIAL = ("09", "Trial", "The Main Event")
    S10_POST_TRIAL = ("10", "Post-Trial", "Aftermath")
    S11_NOTICE_APPEAL = ("11", "Notice of Appeal", "Round Two")
    S12_APPELLATE_BRIEF = ("12", "Appellate Brief", "The Supreme Slap")
    S13_ORAL_ARGUMENT = ("13", "Oral Argument", "Face to Face")
    S14_VICTORY = ("14", "Victory", "Total Domination")
    
    def __init__(self, num: str, stage_name: str, card_title: str):
        self.num = num
        self.stage_name = stage_name
        self.card_title = card_title


# Stage to rarity mapping
STAGE_RARITY = {
    LitigationStage.S01_COMPLAINT: CardRarity.COMMON,
    LitigationStage.S02_ANSWER: CardRarity.COMMON,
    LitigationStage.S03_DISCOVERY: CardRarity.UNCOMMON,
    LitigationStage.S04_MTD: CardRarity.UNCOMMON,
    LitigationStage.S05_MSJ: CardRarity.RARE,
    LitigationStage.S06_OPPOSITION: CardRarity.UNCOMMON,
    LitigationStage.S07_REPLY: CardRarity.UNCOMMON,
    LitigationStage.S08_TRIAL_PREP: CardRarity.RARE,
    LitigationStage.S09_TRIAL: CardRarity.EPIC,
    LitigationStage.S10_POST_TRIAL: CardRarity.RARE,
    LitigationStage.S11_NOTICE_APPEAL: CardRarity.RARE,
    LitigationStage.S12_APPELLATE_BRIEF: CardRarity.RARE,
    LitigationStage.S13_ORAL_ARGUMENT: CardRarity.EPIC,
    LitigationStage.S14_VICTORY: CardRarity.LEGENDARY,
}


# Default quotes per stage
STAGE_QUOTES = {
    LitigationStage.S01_COMPLAINT: "LET'S GET IT STARTED!",
    LitigationStage.S02_ANSWER: "IS THAT ALL YOU GOT?",
    LitigationStage.S03_DISCOVERY: "SHOW ME WHAT YOU'RE HIDING!",
    LitigationStage.S04_MTD: "NOT TODAY, CLOWN!",
    LitigationStage.S05_MSJ: "THE FACTS DON'T LIE!",
    LitigationStage.S06_OPPOSITION: "OBJECTION... SUSTAINED!",
    LitigationStage.S07_REPLY: "CHECKMATE!",
    LitigationStage.S08_TRIAL_PREP: "READY FOR BATTLE!",
    LitigationStage.S09_TRIAL: "JUSTICE IS SERVED!",
    LitigationStage.S10_POST_TRIAL: "AND STAY DOWN!",
    LitigationStage.S11_NOTICE_APPEAL: "THIS ISN'T OVER!",
    LitigationStage.S12_APPELLATE_BRIEF: "READ IT AND WEEP!",
    LitigationStage.S13_ORAL_ARGUMENT: "SPEECHLESS, AREN'T YOU?",
    LitigationStage.S14_VICTORY: "WHO'S THE PIMP DADDY NOW?!",
}


@dataclass
class PimpSlapCard:
    """A collectible marketing card."""
    card_id: str
    stage: LitigationStage
    rarity: CardRarity
    slapper: str
    slapped: str
    action_quote: str
    flavor_text: str
    case_number: str = ""
    date_earned: str = ""
    referral_code: str = ""
    custom_title: Optional[str] = None
    issue_summary: str = ""  # Summary of what the motion addressed
    
    def __post_init__(self):
        if not self.date_earned:
            self.date_earned = datetime.now().strftime("%Y-%m-%d")
        if not self.referral_code:
            self._generate_referral_code()
    
    def _generate_referral_code(self):
        data = f"{self.card_id}{self.date_earned}{self.slapper}"
        hash_val = hashlib.md5(data.encode()).hexdigest()[:8].upper()
        self.referral_code = f"SLAP-{hash_val}"
    
    @property
    def title(self) -> str:
        return self.custom_title or self.stage.card_title
    
    @classmethod
    def create(
        cls,
        stage: LitigationStage,
        slapped: str = "Clackamas County",
        slapper: str = "Tyler 'Oooo-pus Pimp-Daddy'",
        custom_quote: Optional[str] = None,
        custom_title: Optional[str] = None,
        case_number: str = "",
        issue_summary: str = "",
    ) -> "PimpSlapCard":
        """Create a new card."""
        
        card_num = datetime.now().strftime("%Y%m%d%H%M%S")
        
        return cls(
            card_id=f"PSLAP-{stage.num}-{card_num}",
            stage=stage,
            rarity=STAGE_RARITY.get(stage, CardRarity.COMMON),
            slapper=slapper,
            slapped=slapped,
            action_quote=custom_quote or STAGE_QUOTES.get(stage, "SLAPPED!"),
            flavor_text=f"Stage {stage.num}: {stage.stage_name}",
            case_number=case_number,
            custom_title=custom_title,
            issue_summary=issue_summary,
        )
    
    def render_ascii(self) -> str:
        """Render as ASCII art for terminal display."""
        
        border = "═" * 48
        title_display = self.title[:44]
        slapper_display = self.slapper[:20]
        slapped_display = self.slapped[:20]
        quote_display = self.action_quote[:42]
        flavor_display = self.flavor_text[:44]
        
        lines = [
            f"╔{border}╗",
            f"║  {self.rarity.symbol} {title_display:<44}  ║",
            f"║{'─' * 48}║",
            f"║                                                ║",
            f"║              🖐️  *SLAP*  🖐️                    ║",
            f"║                                                ║",
            f"║    {slapper_display:^20} → {slapped_display:^20}    ║",
            f"║                                                ║",
            f"║{'─' * 48}║",
            f"║  \"{quote_display:<42}\"  ║",
            f"║                                                ║",
            f"║  {flavor_display:<44}  ║",
            f"║                                                ║",
            f"║{'─' * 48}║",
            f"║  Rarity: {self.rarity.label:<37}  ║",
            f"║  Date: {self.date_earned:<39}  ║",
            f"║  Code: {self.referral_code:<39}  ║",
            f"╚{border}╝",
        ]
        
        return "\n".join(lines)
    
    def render_html(self) -> str:
        """Render as HTML for app display - 1980s Batman comic style."""
        
        return f'''<!DOCTYPE html>
<html>
<head>
    <meta charset="UTF-8">
    <style>
        @import url('https://fonts.googleapis.com/css2?family=Bangers&display=swap');
        
        body {{
            margin: 0;
            padding: 20px;
            background: #1a1a2e;
            display: flex;
            justify-content: center;
            align-items: center;
            min-height: 100vh;
        }}
        
        .card {{
            width: 350px;
            background: linear-gradient(135deg, #16213e 0%, #0f3460 50%, #1a1a2e 100%);
            border: 4px solid {self.rarity.color};
            border-radius: 15px;
            padding: 20px;
            box-shadow: 
                0 0 30px {self.rarity.color}40,
                inset 0 0 20px rgba(0,0,0,0.5);
            font-family: 'Courier New', monospace;
            color: #e94560;
            position: relative;
            overflow: hidden;
        }}
        
        .card::before {{
            content: '';
            position: absolute;
            top: -50%;
            left: -50%;
            width: 200%;
            height: 200%;
            background: repeating-linear-gradient(
                45deg,
                transparent,
                transparent 10px,
                rgba(233,69,96,0.03) 10px,
                rgba(233,69,96,0.03) 20px
            );
            pointer-events: none;
        }}
        
        .header {{
            text-align: center;
            border-bottom: 2px solid {self.rarity.color};
            padding-bottom: 15px;
            margin-bottom: 15px;
        }}
        
        .rarity {{
            color: {self.rarity.color};
            font-size: 0.9em;
            text-transform: uppercase;
            letter-spacing: 2px;
        }}
        
        .title {{
            font-family: 'Bangers', cursive;
            font-size: 1.8em;
            color: {self.rarity.color};
            margin: 10px 0;
            text-shadow: 2px 2px 0 #000, -1px -1px 0 #000;
        }}
        
        .slap-zone {{
            text-align: center;
            padding: 25px 0;
            position: relative;
        }}
        
        .slap-effect {{
            font-family: 'Bangers', cursive;
            font-size: 3em;
            color: #ffeb3b;
            text-shadow: 
                3px 3px 0 #e94560,
                6px 6px 0 #000;
            animation: slap 0.5s ease-in-out infinite alternate;
        }}
        
        @keyframes slap {{
            from {{ transform: rotate(-5deg) scale(1); }}
            to {{ transform: rotate(5deg) scale(1.1); }}
        }}
        
        .parties {{
            display: flex;
            justify-content: center;
            align-items: center;
            gap: 10px;
            margin-top: 15px;
            font-size: 0.9em;
        }}
        
        .slapper {{
            color: #4ecca3;
            font-weight: bold;
        }}
        
        .arrow {{
            color: #ffeb3b;
            font-size: 1.5em;
        }}
        
        .slapped {{
            color: #ff6b6b;
            font-weight: bold;
        }}
        
        .quote-box {{
            background: rgba(0,0,0,0.4);
            border: 2px dashed {self.rarity.color};
            border-radius: 10px;
            padding: 15px;
            margin: 15px 0;
            text-align: center;
        }}
        
        .quote {{
            font-family: 'Bangers', cursive;
            font-size: 1.3em;
            color: #ffeb3b;
        }}
        
        .flavor {{
            font-style: italic;
            color: #aaa;
            font-size: 0.85em;
            margin-top: 10px;
        }}
        
        .footer {{
            border-top: 2px solid #333;
            padding-top: 15px;
            margin-top: 15px;
            font-size: 0.8em;
            color: #888;
        }}
        
        .footer div {{
            margin: 5px 0;
        }}
        
        .referral {{
            background: linear-gradient(90deg, {self.rarity.color}, transparent);
            padding: 5px 10px;
            border-radius: 5px;
            display: inline-block;
            color: #fff;
            font-weight: bold;
        }}
        
        .case-number {{
            color: {self.rarity.color};
        }}
    </style>
</head>
<body>
    <div class="card">
        <div class="header">
            <div class="rarity">{self.rarity.symbol} {self.rarity.label}</div>
            <div class="title">{self.title}</div>
        </div>
        
        <div class="slap-zone">
            <div class="slap-effect">💥 SLAP! 💥</div>
            <div class="parties">
                <span class="slapper">{self.slapper}</span>
                <span class="arrow">➜</span>
                <span class="slapped">{self.slapped}</span>
            </div>
        </div>
        
        <div class="quote-box">
            <div class="quote">"{self.action_quote}"</div>
            <div class="flavor">{self.flavor_text}</div>
        </div>
        
        <div class="footer">
            <div>📋 Stage: {self.stage.num} - {self.stage.stage_name}</div>
            <div>📅 Earned: {self.date_earned}</div>
            {"<div class='case-number'>⚖️ Case: " + self.case_number + "</div>" if self.case_number else ""}
            <div>🎟️ <span class="referral">{self.referral_code}</span></div>
        </div>
    </div>
</body>
</html>'''
    
    def save_html(self, path: str) -> str:
        """Save card as HTML file."""
        with open(path, 'w') as f:
            f.write(self.render_html())
        return path


# Special cards
SPECIAL_CARDS = {
    "FRAUD_EXPOSED": {
        "title": "Fraud Upon the Court",
        "quote": "FIVE YEARS OF LIES EXPOSED!",
        "flavor": "The truth always comes out. Always.",
        "rarity": CardRarity.LEGENDARY,
        "stage": LitigationStage.S14_VICTORY,
    },
    "HALF_TRUTHS": {
        "title": "Half Truths Are Whole Lies",
        "quote": "YOU SAID IT TWICE AND LIED TWICE!",
        "flavor": "Motion to Dismiss AND Reply - same lies.",
        "rarity": CardRarity.EPIC,
        "stage": LitigationStage.S06_OPPOSITION,
    },
    "LATE_FILING": {
        "title": "Time's Up, Clown",
        "quote": "YOUR REPLY IS LATE - STRIKE IT!",
        "flavor": "Deadlines apply to everyone. Even you.",
        "rarity": CardRarity.RARE,
        "stage": LitigationStage.S07_REPLY,
    },
}


def create_special_card(
    card_key: str,
    slapped: str = "Clackamas County",
    case_number: str = "",
) -> PimpSlapCard:
    """Create a special/legendary card."""
    
    if card_key not in SPECIAL_CARDS:
        raise ValueError(f"Unknown special card: {card_key}")
    
    spec = SPECIAL_CARDS[card_key]
    
    return PimpSlapCard(
        card_id=f"PSLAP-SPEC-{datetime.now().strftime('%Y%m%d%H%M%S')}",
        stage=spec["stage"],
        rarity=spec["rarity"],
        slapper="Tyler 'Oooo-pus Pimp-Daddy'",
        slapped=slapped,
        action_quote=spec["quote"],
        flavor_text=spec["flavor"],
        case_number=case_number,
        custom_title=spec["title"],
    )


# Demo
if __name__ == "__main__":
    # Create card for Tyler's declaration about false statements
    card = PimpSlapCard.create(
        stage=LitigationStage.S06_OPPOSITION,
        slapped="Clackamas County",
        custom_quote="HALF TRUTHS ARE WHOLE LIES!",
        custom_title="Declaration vs False Statements",
        case_number="25-6461",
        issue_summary="Defendants stated same false claims in MTD AND Reply",
    )
    
    print(card.render_ascii())
    
    # Save HTML
    html_path = "/mnt/user-data/outputs/PIMP_SLAP_CARD.html"
    card.save_html(html_path)
    print(f"\n✓ HTML card saved: {html_path}")
