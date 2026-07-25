#!/usr/bin/env python3
"""
User Story Generator with INVEST Criteria
Creates well-formed user stories with acceptance criteria
"""

import json
from typing import Dict, List, Tuple

class UserStoryGenerator:
    """Generate INVEST-compliant user stories"""
    
    def __init__(self):
        self.personas = {
            'end_user': {
                'name': 'End User',
                'needs': ['efficiency', 'simplicity', 'reliability', 'speed'],
                'context': 'daily usage of core features'
            },
            'admin': {
                'name': 'Administrator',
                'needs': ['control', 'visibility', 'security', 'configuration'],
                'context': 'system management and oversight'
            },
            'power_user': {
                'name': 'Power User',
                'needs': ['advanced features', 'automation', 'customization', 'shortcuts'],
                'context': 'expert usage and workflow optimization'
            },
            'new_user': {
                'name': 'New User',
                'needs': ['guidance', 'learning', 'safety', 'clarity'],
                'context': 'first-time experience and onboarding'
            }
        }
        
        self.story_templates = {
            'feature': "As a {persona}, I want to {action} so that {benefit}",
            'improvement': "As a {persona}, I need {capability} to {achieve_goal}",
            'fix': "As a {persona}, I expect {behavior} when {condition}",
            'integration': "As a {persona}, I want to {integrate} so that {workflow}"
        }
        
        self.acceptance_criteria_patterns = [
            "Given {precondition}, When {action}, Then {outcome}",
            "Should {behavior} when {condition}",
            "Must {requirement} to {achieve}",
            "Can {capability} without {negative_outcome}"
        ]
    
    def generate_epic_stories(self, epic: Dict) -> List[Dict]:
        """Break down epic into user stories"""
        stories = []
        
        # Analyze epic for key components
        epic_name = epic.get('name', 'Feature')
        epic_description = epic.get('description', '')
        personas = epic.get('personas', ['end_user'])
        scope = epic.get('scope', [])
        
        # Generate stories for each persona and scope item
        for persona in personas:
            for i, scope_item in enumerate(scope):
                story = self.generate_story(
                    persona=persona,
                    feature=scope_item,
                    epic=epic_name,
                    index=i+1
                )
                stories.append(story)
        
        # Add enabler stories (technical, infrastructure)
        if epic.get('technical_requirements'):
            for req in epic['technical_requirements']:
                enabler = self.generate_enabler_story(req, epic_name)
                stories.append(enabler)
        
        return stories
    
    def generate_story(self, persona: str, feature: str, epic: str, index: int) -> Dict:
        """Generate a single user story"""
        
        persona_data = self.personas.get(persona, self.personas['end_user'])
        
        # Create story
        story = {
            'id': f"{epic[:3].upper()}-{index:03d}",
            'type': 'story',
            'title': self._generate_title(feature),
            'narrative': self._generate_narrative(persona_data, feature),
            'acceptance_criteria': self._generate_acceptance_criteria(feature),
            'estimation': self._estimate_complexity(feature),
            'priority': self._determine_priority(persona, feature),
            'dependencies': [],
            'invest_check': self._check_invest_criteria(feature)
        }
        
        return story
    
    def generate_enabler_story(self, requirement: str, epic: str) -> Dict:
        """Generate technical enabler story"""
        
        return {
            'id': f"{epic[:3].upper()}-E{len(requirement):02d}",
            'type': 'enabler',
            'title': f"Technical: {requirement}",
            'narrative': f"As a developer, I need to {requirement} to enable user features",
            'acceptance_criteria': [
                f"Technical requirement {requirement} is implemented",
                "All tests pass",
                "Documentation is updated",
                "No regression in existing functionality"
            ],
            'estimation': 5,  # Default medium complexity
            'priority': 'high',
            'dependencies': [],
            'invest_check': {
                'independent': True,
                'negotiable': False,  # Technical requirements often non-negotiable
                'valuable': True,
                'estimable': True,
                'small': True,
                'testable': True
            }
        }
    
    def _generate_title(self, feature: str) -> str:
        """Generate concise story title"""
        # Simplify feature description to title
        words = feature.split()[:5]
        return ' '.join(words).title()
    
    def _generate_narrative(self, persona: Dict, feature: str) -> str:
        """Generate story narrative in standard format"""
        
        template = self.story_templates['feature']
        
        action = self._extract_action(feature)
        benefit = self._extract_benefit(feature, persona['needs'])
        
        return template.format(
            persona=persona['name'],
            action=action,
            benefit=benefit
        )
    
    def _generate_acceptance_criteria(self, feature: str) -> List[str]:
        """Generate acceptance criteria"""
        
        criteria = []
        
        # Happy path
        criteria.append(f"Given user has access, When they {self._extract_action(feature)}, Then {self._extract_outcome(feature)}")
        
        # Validation
        criteria.append(f"Should validate input before processing")
        
        # Error handling
        criteria.append(f"Must show clear error message when action fails")
        
        # Performance
        criteria.append(f"Should complete within 2 seconds")
        
        # Accessibility
        criteria.append(f"Must be accessible via keyboard navigation")
        
        return criteria
    
    def _extract_action(self, feature: str) -> str:
        """Extract action from feature description"""
        action_verbs = ['create', 'view', 'edit', 'delete', 'share', 'export', 'import', 'configure', 'search', 'filter']
        
        feature_lower = feature.lower()
        for verb in action_verbs:
            if verb in feature_lower:
                return feature_lower
        
        return f"use {feature.lower()}"
    
    def _extract_benefit(self, feature: str, needs: List[str]) -> str:
        """Extract benefit based on feature and persona needs"""
        
        feature_lower = feature.lower()
        
        if 'save' in feature_lower or 'quick' in feature_lower:
            return "I can save time and work more efficiently"
        elif 'share' in feature_lower or 'collab' in feature_lower:
            return "I can collaborate with my team effectively"
        elif 'report' in feature_lower or 'analyt' in feature_lower:
            return "I can make data-driven decisions"
        elif 'automat' in feature_lower:
            return "I can reduce manual work and errors"
        else:
            return f"I can achieve my goals related to {needs[0]}"
    
    def _extract_outcome(self, feature: str) -> str:
        """Extract expected outcome"""
        return f"the {feature.lower()} is successfully completed"
    
    def _estimate_complexity(self, feature: str) -> int:
        """Estimate story points based on complexity indicators"""
        
        feature_lower = feature.lower()
        
        # Complexity indicators
        complexity = 3  # Base complexity
        
        if any(word in feature_lower for word in ['simple', 'basic', 'view', 'display']):
            complexity = 1
        elif any(word in feature_lower for word in ['create', 'edit', 'update']):
            complexity = 3
        elif any(word in feature_lower for word in ['complex', 'advanced', 'integrate', 'migrate']):
            complexity = 8
        elif any(word in feature_lower for word in ['redesign', 'refactor', 'architect']):
            complexity = 13
        
        return complexity
    
    def _determine_priority(self, persona: str, feature: str) -> str:
        """Determine story priority"""
        
        feature_lower = feature.lower()
        
        # Critical features
        if any(word in feature_lower for word in ['security', 'fix', 'critical', 'broken']):
            return 'critical'
        
        # High priority for primary personas
        if persona in ['end_user', 'admin']:
            if any(word in feature_lower for word in ['core', 'essential', 'primary']):
                return 'high'
        
        # Medium for improvements
        if any(word in feature_lower for word in ['improve', 'enhance', 'optimize']):
            return 'medium'
        
        # Low for nice-to-haves
        return 'low'
    
    def _check_invest_criteria(self, feature: str) -> Dict[str, bool]:
        """Check INVEST criteria compliance"""
        
        return {
            'independent': not any(word in feature.lower() for word in ['after', 'depends', 'requires']),
            'negotiable': True,  # Most features can be negotiated
            'valuable': True,  # Assume value if it made it to backlog
            'estimable': len(feature.split()) < 20,  # Can estimate if not too vague
            'small': self._estimate_complexity(feature) <= 8,  # 8 points or less
            'testable': not any(word in feature.lower() for word in ['maybe', 'possibly', 'somehow'])
        }
    
    def generate_sprint_stories(self, capacity: int, backlog: List[Dict]) -> Dict:
        """Generate stories for a sprint based on capacity"""
        
        sprint = {
            'capacity': capacity,
            'committed': [],
            'stretch': [],
            'total_points': 0,
            'utilization': 0
        }
        
        # Sort backlog by priority and size
        sorted_backlog = sorted(
            backlog,
            key=lambda x: (
                {'critical': 0, 'high': 1, 'medium': 2, 'low': 3}[x['priority']],
                x['estimation']
            )
        )
        
        # Fill sprint
        for story in sorted_backlog:
            if sprint['total_points'] + story['estimation'] <= capacity:
                sprint['committed'].append(story)
                sprint['total_points'] += story['estimation']
            elif sprint['total_points'] + story['estimation'] <= capacity * 1.2:
                sprint['stretch'].append(story)
        
        sprint['utilization'] = round((sprint['total_points'] / capacity) * 100, 1)
        
        return sprint
    
    def format_story_output(self, story: Dict) -> str:
        """Format story for display"""
        
        output = []
        output.append(f"USER STORY: {story['id']}")
        output.append("=" * 40)
        output.append(f"Title: {story['title']}")
        output.append(f"Type: {story['type']}")
        output.append(f"Priority: {story['priority'].upper()}")
        output.append(f"Points: {story['estimation']}")
        output.append("")
        output.append("Story:")
        output.append(story['narrative'])
        output.append("")
        output.append("Acceptance Criteria:")
        for i, criterion in enumerate(story['acceptance_criteria'], 1):
            output.append(f"  {i}. {criterion}")
        output.append("")
        output.append("INVEST Checklist:")
        for criterion, passed in story['invest_check'].items():
            status = "✓" if passed else "✗"
            output.append(f"  {status} {criterion.capitalize()}")
        
        return "\n".join(output)

def create_sample_epic():
    """Create a sample epic for testing"""
    return {
        'name': 'User Dashboard',
        'description': 'Create a comprehensive dashboard for users to view their data',
        'personas': ['end_user', 'power_user'],
        'scope': [
            'View key metrics and KPIs',
            'Customize dashboard layout',
            'Export dashboard data',
            'Share dashboard with team members',
            'Set up automated reports'
        ],
        'technical_requirements': [
            'Implement caching for performance',
            'Set up real-time data pipeline'
        ]
    }

def main():
    import argparse

    parser = argparse.ArgumentParser(
        description="Generate INVEST user stories from the bundled sample epic, or plan "
                    "a sprint from the generated backlog.")
    parser.add_argument("mode", nargs="?", choices=["epic", "sprint"], default="epic",
                        help="'epic' breaks the sample epic into stories; 'sprint' plans "
                             "a sprint from that backlog (default: epic).")
    parser.add_argument("capacity", nargs="?", type=int, default=30,
                        help="Sprint capacity in story points (sprint mode, default: 30).")
    parser.add_argument("--sample", action="store_true",
                        help="Break the bundled sample epic into stories and exit 0 "
                             "(same as the default epic mode; kept for harness smoke tests).")
    args = parser.parse_args()

    generator = UserStoryGenerator()

    if args.mode == 'sprint':
        # Generate sprint planning
        capacity = args.capacity
        
        # Create sample backlog
        epic = create_sample_epic()
        backlog = generator.generate_epic_stories(epic)
        
        # Plan sprint
        sprint = generator.generate_sprint_stories(capacity, backlog)
        
        print("=" * 60)
        print("SPRINT PLANNING")
        print("=" * 60)
        print(f"Sprint Capacity: {sprint['capacity']} points")
        print(f"Committed: {sprint['total_points']} points ({sprint['utilization']}%)")
        print(f"Stories: {len(sprint['committed'])} committed + {len(sprint['stretch'])} stretch")
        print("\n📋 COMMITTED STORIES:\n")
        
        for story in sprint['committed']:
            print(f"  [{story['priority'][:1].upper()}] {story['id']}: {story['title']} ({story['estimation']}pts)")
        
        if sprint['stretch']:
            print("\n🎯 STRETCH GOALS:\n")
            for story in sprint['stretch']:
                print(f"  [{story['priority'][:1].upper()}] {story['id']}: {story['title']} ({story['estimation']}pts)")
    
    else:
        # Generate stories for epic
        epic = create_sample_epic()
        stories = generator.generate_epic_stories(epic)
        
        print(f"Generated {len(stories)} stories from epic: {epic['name']}\n")
        
        # Display first 3 stories in detail
        for story in stories[:3]:
            print(generator.format_story_output(story))
            print("\n")
        
        # Summary of all stories
        print("=" * 60)
        print("BACKLOG SUMMARY")
        print("=" * 60)
        total_points = sum(s['estimation'] for s in stories)
        print(f"Total Stories: {len(stories)}")
        print(f"Total Points: {total_points}")
        print(f"Average Size: {total_points/len(stories):.1f} points")
        print("\nPriority Breakdown:")
        for priority in ['critical', 'high', 'medium', 'low']:
            count = len([s for s in stories if s['priority'] == priority])
            if count > 0:
                print(f"  {priority.capitalize()}: {count} stories")

if __name__ == "__main__":
    main()
