#!/usr/bin/env python3
"""
Convert Agent Skills to Qoder Agent format

This script converts Agent Skills to Qoder agent module format.
Qoder is an agentic coding platform that supports agent-based automation.

Usage:
    python convert_to_qoder.py <skill_path> [output_path]
    
Example:
    python convert_to_qoder.py ../../skills/course-designer qoder-agents/
"""

import sys
import json
import re
from pathlib import Path

try:
    import yaml
    HAS_YAML = True
except ImportError:
    HAS_YAML = False


def parse_yaml_simple(text):
    """Simple YAML parser for frontmatter (handles basic key: value pairs)"""
    result = {}
    for line in text.split('\n'):
        line = line.strip()
        if ':' in line and not line.startswith('#'):
            key, value = line.split(':', 1)
            key = key.strip()
            value = value.strip().strip('"').strip("'")
            result[key] = value
    return result


def extract_frontmatter(content):
    """Extract YAML frontmatter from SKILL.md"""
    frontmatter_pattern = r'^---\n(.*?)\n---\n'
    match = re.match(frontmatter_pattern, content, re.DOTALL)
    
    if match:
        frontmatter_text = match.group(1)
        if HAS_YAML:
            frontmatter = yaml.safe_load(frontmatter_text)
        else:
            frontmatter = parse_yaml_simple(frontmatter_text)
        body_start = match.end()
        body = content[body_start:].strip()
        return frontmatter, body
    return {}, content.strip()


def extract_workflow_steps(body):
    """Extract workflow steps from skill body"""
    steps = []
    # Look for numbered lists or workflow sections
    lines = body.split('\n')
    current_step = None
    
    for line in lines:
        # Match numbered list items
        match = re.match(r'^(\d+)\.\s+(.+)$', line.strip())
        if match:
            step_num = match.group(1)
            step_desc = match.group(2)
            steps.append({
                "step": f"step-{step_num}",
                "description": step_desc
            })
        # Match ## sections as workflow steps
        elif line.startswith('## ') and '流程' in line or 'workflow' in line.lower():
            current_step = line.replace('##', '').strip()
    
    return steps if steps else [
        {"step": "analyze", "description": "Analyze requirements"},
        {"step": "execute", "description": "Execute skill task"},
        {"step": "output", "description": "Generate output"}
    ]


def convert_to_qoder_agent(skill_path, output_dir=None):
    """
    Convert Agent Skill to Qoder agent format
    
    Args:
        skill_path: Path to skill directory containing SKILL.md
        output_dir: Output directory for agent (optional)
    """
    skill_path = Path(skill_path)
    skill_file = skill_path / "SKILL.md"
    
    if not skill_file.exists():
        print(f"Error: SKILL.md not found in {skill_path}")
        return None
    
    # Read skill file
    with open(skill_file, "r", encoding="utf-8") as f:
        content = f.read()
    
    # Extract frontmatter and body
    frontmatter, body = extract_frontmatter(content)
    
    if not frontmatter:
        print(f"Warning: No frontmatter found in {skill_file}")
        frontmatter = {"name": skill_path.name, "description": ""}
    
    # Extract workflow steps
    workflow_steps = extract_workflow_steps(body)
    
    # Extract capabilities from description
    capabilities = []
    description = frontmatter.get("description", "")
    if "课程设计" in description or "course" in description.lower():
        capabilities.append("course-design")
    if "代码" in description or "code" in description.lower():
        capabilities.append("code-generation")
    if "测试" in description or "test" in description.lower():
        capabilities.append("testing")
    if not capabilities:
        capabilities = [frontmatter.get("name", skill_path.name)]
    
    # Create Qoder agent configuration
    agent_config = {
        "name": f"{frontmatter.get('name', skill_path.name)}-agent",
        "description": frontmatter.get("description", ""),
        "version": "1.0.0",
        "type": "skill-agent",
        "capabilities": capabilities,
        "workflow": workflow_steps,
        "instructions": "SKILL.md",
        "metadata": {
            "source": "teaching-ai-skills",
            "original_skill": frontmatter.get("name", skill_path.name)
        }
    }
    
    # Write output
    if output_dir:
        output_dir = Path(output_dir)
        output_dir.mkdir(parents=True, exist_ok=True)
        
        # Create agent directory
        agent_dir = output_dir / agent_config["name"]
        agent_dir.mkdir(parents=True, exist_ok=True)
        
        # Write agent config
        config_file = agent_dir / "qoder-agent-config.json"
        with open(config_file, "w", encoding="utf-8") as f:
            json.dump(agent_config, f, indent=2, ensure_ascii=False)
        
        # Copy SKILL.md
        import shutil
        shutil.copy2(skill_file, agent_dir / "SKILL.md")
        
        # Create Python agent module
        python_module = agent_dir / f"{frontmatter.get('name', skill_path.name).replace('-', '_')}_agent.py"
        create_python_agent_module(frontmatter, body, python_module)
        
        print(f"✅ Converted to Qoder agent: {agent_dir}")
        return agent_dir
    else:
        return agent_config


def create_python_agent_module(frontmatter, body, output_file):
    """Create Python agent module for Qoder"""
    skill_name = frontmatter.get("name", "skill")
    class_name = "".join(word.capitalize() for word in skill_name.split("-")) + "Agent"
    
    module_content = f'''"""
{frontmatter.get('description', 'Agent module')} for Qoder

This agent module was automatically generated from Agent Skill.
"""


class {class_name}:
    """
    Agent for {frontmatter.get('description', 'executing tasks')}
    """
    
    def __init__(self):
        self.name = "{skill_name}"
        self.description = "{frontmatter.get('description', '')}"
    
    def execute(self, task, context=None):
        """
        Execute the agent task
        
        Args:
            task: Task description or parameters
            context: Optional context information
            
        Returns:
            Task execution result
        """
        # Read instructions from SKILL.md
        # Execute skill workflow
        # Return result
        pass
    
    def get_capabilities(self):
        """Get agent capabilities"""
        return {{
            "name": self.name,
            "description": self.description,
            "capabilities": ["task-execution"]
        }}
'''
    
    with open(output_file, "w", encoding="utf-8") as f:
        f.write(module_content)


def convert_all_skills(skills_dir, output_dir):
    """Convert all skills in a directory"""
    skills_dir = Path(skills_dir)
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    
    converted = []
    for skill_dir in skills_dir.iterdir():
        if skill_dir.is_dir() and (skill_dir / "SKILL.md").exists():
            try:
                result = convert_to_qoder_agent(skill_dir, output_dir)
                if result:
                    converted.append(skill_dir.name)
            except Exception as e:
                print(f"Error converting {skill_dir.name}: {e}")
    
    print(f"\n✅ Converted {len(converted)} skills: {', '.join(converted)}")
    return converted


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python convert_to_qoder.py <skill_path> [output_path]")
        print("   or: python convert_to_qoder.py --all <skills_dir> <output_dir>")
        sys.exit(1)
    
    if sys.argv[1] == "--all":
        if len(sys.argv) < 4:
            print("Usage: python convert_to_qoder.py --all <skills_dir> <output_dir>")
            sys.exit(1)
        convert_all_skills(sys.argv[2], sys.argv[3])
    else:
        skill_path = sys.argv[1]
        output_path = sys.argv[2] if len(sys.argv) > 2 else None
        convert_to_qoder_agent(skill_path, output_path)
