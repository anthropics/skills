#!/usr/bin/env python3
"""Habit Runner — The execution engine for Agent Habits.

Loads a HABIT.md, walks through the Discovery, Plan, Execute, Evaluate, and Output
phases in accordance with the Agent Habits specification. All execution and
evaluation steps are performed via the Claude API.
"""

import argparse
import json
import os
import re
import sys
from pathlib import Path

# Try importing Anthropic
try:
    from anthropic import Anthropic
except ImportError:
    print("\033[91m[Error] The 'anthropic' python package is not installed. Please run: pip install anthropic\033[0m")
    sys.exit(1)

# ANSI colors for beautiful terminal output
class Colors:
    HEADER = '\033[95m'
    BLUE = '\033[94m'
    CYAN = '\033[96m'
    GREEN = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'

def print_header(text):
    print(f"\n{Colors.BOLD}{Colors.HEADER}=== {text} ==={Colors.ENDC}")

def print_step(text):
    print(f"{Colors.BOLD}{Colors.BLUE}--> {text}{Colors.ENDC}")

def print_success(text):
    print(f"{Colors.GREEN}[OK] {text}{Colors.ENDC}")

def print_warning(text):
    print(f"{Colors.WARNING}[WARN] {text}{Colors.ENDC}")

def print_error(text):
    print(f"{Colors.FAIL}[ERROR] {text}{Colors.ENDC}")

def parse_frontmatter(content):
    """Parse YAML-like frontmatter from markdown content."""
    if not content.strip().startswith('---'):
        return {}, content
    
    parts = content.split('---', 2)
    if len(parts) < 3:
        return {}, content
        
    yaml_text = parts[1]
    body = parts[2]
    
    metadata = {}
    for line in yaml_text.strip().split('\n'):
        if ':' in line:
            key, val = line.split(':', 1)
            val_clean = val.split('←')[0].strip()
            val_clean = val_clean.strip('"\'')
            metadata[key.strip()] = val_clean
            
    return metadata, body

def parse_markdown_table(table_text):
    """Parse a Markdown table into a list of dicts."""
    rows = []
    lines = [line.strip() for line in table_text.strip().split('\n')]
    if len(lines) < 3:
        return []
        
    headers = [col.strip() for col in lines[0].split('|')[1:-1]]
    
    for line in lines[2:]:
        if not line or not line.startswith('|'):
            continue
        cols = [col.strip() for col in line.split('|')[1:-1]]
        if len(cols) == len(headers):
            rows.append(dict(zip(headers, cols)))
            
    return rows

def load_habit(habit_path):
    """Load and parse HABIT.md and all skills in skills/."""
    habit_dir = Path(habit_path)
    if not habit_dir.exists():
        # Try checking in habits/ directory
        parent_habits_dir = Path(__file__).parent / habit_dir.name
        if parent_habits_dir.exists():
            habit_dir = parent_habits_dir
        else:
            raise FileNotFoundError(f"Habit directory not found: {habit_path}")
            
    habit_md_path = habit_dir / "HABIT.md"
    if not habit_md_path.exists():
        raise FileNotFoundError(f"HABIT.md not found in {habit_dir}")
        
    with open(habit_md_path, 'r', encoding='utf-8') as f:
        content = f.read()
        
    metadata, body = parse_frontmatter(content)
    
    sections = {}
    current_section = None
    section_content = []
    
    for line in body.split('\n'):
        match = re.match(r'^##\s+(.+)$', line)
        if match:
            if current_section:
                sections[current_section] = '\n'.join(section_content).strip()
            current_section = match.group(1).strip()
            section_content = []
        elif current_section:
            section_content.append(line)
            
    if current_section:
        sections[current_section] = '\n'.join(section_content).strip()
        
    skills_dir = habit_dir / "skills"
    skills = {}
    if skills_dir.exists():
        for skill_file in skills_dir.glob("*.md"):
            with open(skill_file, 'r', encoding='utf-8') as f:
                skill_content = f.read()
            skill_meta, skill_body = parse_frontmatter(skill_content)
            skills[skill_file.stem] = {
                "metadata": skill_meta,
                "body": skill_body,
                "full_content": skill_content,
                "path": skill_file
            }
            
    return {
        "dir": habit_dir,
        "metadata": metadata,
        "body": body,
        "sections": sections,
        "skills": skills
    }

def write_extracted_files(output_text, base_dir):
    """Automatically extract and write files generated in output_text."""
    # Pattern 1: [FILE: path]...[END_FILE]
    pattern1 = r'\[FILE:\s*(.*?)\](.*?)\[END_FILE\]'
    matches1 = re.findall(pattern1, output_text, re.DOTALL)
    
    # Pattern 2: [FILE: path]... (until next [FILE: ] or end of text)
    pattern2 = r'\[FILE:\s*(.*?)\](.*?)(?=\[FILE:|$$)'
    matches2 = re.findall(pattern2, output_text, re.DOTALL)
    
    # Pattern 3: ### File: `path` followed by ```language
    pattern3 = r'###\s+File:\s*[`\']?(.*?)[`\']?\s*\n```\w*\n(.*?)\n```'
    matches3 = re.findall(pattern3, output_text, re.DOTALL)
    
    all_files = []
    seen = set()
    
    for path, content in matches1:
        path = path.strip()
        if path not in seen:
            seen.add(path)
            all_files.append((path, content))
            
    for path, content in matches2:
        path = path.strip()
        if "[END_FILE]" in content:
            content = content.split("[END_FILE]")[0]
        if path not in seen:
            seen.add(path)
            all_files.append((path, content))
            
    for path, content in matches3:
        path = path.strip()
        if path not in seen:
            seen.add(path)
            all_files.append((path, content))
            
    for path_str, content in all_files:
        # Resolve path relative to base_dir
        file_path = base_dir / path_str
        file_path.parent.mkdir(parents=True, exist_ok=True)
        with open(file_path, 'w', encoding='utf-8') as f:
            f.write(content.strip())
        print(f"Automatically wrote generated file: {Colors.GREEN}{path_str}{Colors.ENDC}")

class HabitRunner:
    def __init__(self, habit_data, model_name):
        self.habit_data = habit_data
        self.metadata = habit_data["metadata"]
        self.name = self.metadata.get("name", "Unnamed Habit")
        self.quality_target = int(self.metadata.get("quality_target", 90))
        self.max_iterations = int(self.metadata.get("max_iterations", 3))
        self.skills = habit_data["skills"]
        self.model_name = model_name
        self.answers = {}
        self.execution_plan = []
        self.context = {}
        
        # Initialize Anthropic Client
        self.client = Anthropic()
        
    def run(self):
        print_header(f"Starting Habit: {self.name}")
        print(f"Goal: {self.habit_data['sections'].get('Goal', 'No goal specified.')}\n")
        print(f"API Model: {self.model_name}")
        
        # 1. DISCOVERY PHASE
        self.run_discovery()
        
        # 2. PLAN PHASE
        self.run_planning()
        
        # 3. EXECUTE & 4. EVALUATE LOOP
        iteration = 1
        success = False
        
        while iteration <= self.max_iterations:
            print_header(f"Execution Cycle (Iteration {iteration}/{self.max_iterations})")
            
            # Execute Phase
            self.run_execution()
            
            # Evaluate Phase
            score, breakdown, gap = self.run_evaluation()
            
            print(f"\n{Colors.BOLD}Evaluation Result:{Colors.ENDC}")
            print(f"  Quality Score: {score}/100 (Target: {self.quality_target})")
            print(f"  Breakdown: {breakdown}")
            if gap:
                print(f"  Gap identified: {Colors.WARNING}{gap}{Colors.ENDC}")
                
            if score >= self.quality_target:
                print_success(f"Quality target met! Workflow completed successfully.")
                success = True
                break
            elif score >= 75:
                print_warning(f"Score is between 75 and 89. Retrying execution with gap context...")
                self.context["gap_context"] = gap
                iteration += 1
            elif score >= 50:
                print_warning(f"Score is between 50 and 74. Re-planning the execution...")
                self.run_planning()
                self.context["gap_context"] = gap
                iteration += 1
            else:
                print_error(f"Score is below 50. Escalating!")
                self.run_escalation(score, gap)
                return False
                
        if not success:
            print_error(f"Reached maximum iterations ({self.max_iterations}) without meeting quality target.")
            self.run_escalation(0, "Max iterations reached without meeting quality target.")
            return False
            
        # 5. OUTPUT PHASE
        self.run_output()
        return True

    def run_discovery(self):
        print_step("Phase 1: DISCOVERY")
        discovery_skill = self.skills.get("discovery")
        if not discovery_skill:
            print_warning("No discovery.md skill found! Skipping interactive discovery.")
            return
            
        print(f"Running discovery skill: {discovery_skill['metadata'].get('description', '')}\n")
        
        body = discovery_skill["body"]
        questions = re.findall(r'###\s+(Q\d+:\s*([^\n]+))((?:\n(?!###).*)*)', body)
        
        for q_id_text, q_title, q_body in questions:
            q_id = q_id_text.split(':')[0].strip()
            print(f"\n{Colors.BOLD}{Colors.CYAN}{q_id_text.strip()}{Colors.ENDC}")
            
            q_type_match = re.search(r'-\s*\*?Type:\*?\s*(\w+)', q_body)
            q_type = q_type_match.group(1) if q_type_match else "free_text"
            
            options = []
            options_match = re.search(r'-\s*\*?Options:\*?\s*\[(.*?)\]', q_body)
            if options_match:
                options = [o.strip().strip('"\'') for o in options_match.group(1).split(',')]
            
            clean_body = re.sub(r'-\s*\*?Type:\*?.*', '', q_body)
            clean_body = re.sub(r'-\s*\*?Options:\*?.*', '', clean_body)
            clean_body = re.sub(r'-\s*\*?Maps to:\*?.*', '', clean_body).strip()
            if clean_body:
                print(clean_body)
                
            if options:
                for idx, opt in enumerate(options, 1):
                    print(f"  {idx}. {opt}")
                    
            while True:
                try:
                    val = input(f"{Colors.BOLD}> {Colors.ENDC}").strip()
                    if not val:
                        continue
                    if options:
                        if val.isdigit() and 1 <= int(val) <= len(options):
                            val = options[int(val) - 1]
                            break
                        elif val in options:
                            break
                        else:
                            print(f"Please select one of the valid options: {options}")
                    else:
                        break
                except KeyboardInterrupt:
                    print("\nAborting.")
                    sys.exit(1)
                    
            self.answers[q_id] = val
            
        print_success("Discovery answers gathered.")

    def run_planning(self):
        print_step("Phase 2: PLANNING")
        
        static_matrix_text = self.habit_data["sections"].get("Static Matrix", "")
        static_rows = parse_markdown_table(static_matrix_text)
        
        self.execution_plan = []
        for row in static_rows:
            skill_name = row.get("Skill to Run")
            order = int(row.get("Order", 99))
            condition = row.get("Condition", "always").lower()
            
            if skill_name == "discovery":
                continue
                
            self.execution_plan.append({
                "skill": skill_name,
                "order": order,
                "required": condition == "always",
                "condition": condition
            })
            
        discovery_skill = self.skills.get("discovery")
        mapping_rows = []
        if discovery_skill:
            mapping_text_match = re.search(r'##\s+Matrix\s+Mapping\s*\n((?:.|\n)*)', discovery_skill["body"])
            if mapping_text_match:
                mapping_rows = parse_markdown_table(mapping_text_match.group(1))
                
        for row in mapping_rows:
            ans_expr = row.get("Answer", "")
            effect = row.get("Effect on Matrix", "")
            
            match = re.match(r'(\w+)\s*=\s*(.*)', ans_expr)
            if match:
                q_id, expected_val = match.group(1), match.group(2).strip().lower()
                user_val = self.answers.get(q_id, "").lower()
                
                if user_val == expected_val:
                    if "skip" in effect.lower():
                        skip_skill = re.search(r'skip\s+([a-zA-Z0-9_-]+)', effect, re.IGNORECASE)
                        if skip_skill:
                            s_name = skip_skill.group(1)
                            self.execution_plan = [p for p in self.execution_plan if p["skill"] != s_name]
                            print_success(f"Dynamic Rule Applied: Skipping skill `{s_name}` due to {ans_expr}")
                    elif "use" in effect.lower() or "run" in effect.lower():
                        use_skill = re.search(r'(?:use|run)\s+([a-zA-Z0-9_-]+)', effect, re.IGNORECASE)
                        if use_skill:
                            s_name = use_skill.group(1)
                            if not any(p["skill"] == s_name for p in self.execution_plan):
                                before_match = re.search(r'before\s+([a-zA-Z0-9_-]+)', effect)
                                order = 50
                                if before_match:
                                    tgt = before_match.group(1)
                                    for idx, p in enumerate(self.execution_plan):
                                        if p["skill"] == tgt:
                                            order = p["order"] - 1
                                            break
                                self.execution_plan.append({
                                    "skill": s_name,
                                    "order": order,
                                    "required": True,
                                    "condition": ans_expr
                                })
                                print_success(f"Dynamic Rule Applied: Adding skill `{s_name}` due to {ans_expr}")
                    elif "quality_target" in effect:
                        qt_match = re.search(r'quality_target\s*=\s*(\d+)', effect)
                        if qt_match:
                            self.quality_target = int(qt_match.group(1))
                            print_success(f"Dynamic Rule Applied: quality_target updated to {self.quality_target} due to {ans_expr}")
                            
        self.execution_plan.sort(key=lambda x: x["order"])
        
        print("\nMerged Execution Plan:")
        for idx, item in enumerate(self.execution_plan, 1):
            req_str = "required" if item["required"] else "conditional"
            print(f"  {idx}. Skill: {Colors.BOLD}{item['skill']}{Colors.ENDC} (Order: {item['order']}, {req_str})")
        print("")

    def run_execution(self):
        print_step("Phase 3: EXECUTE")
        
        for idx, step in enumerate(self.execution_plan, 1):
            skill_name = step["skill"]
            skill_info = self.skills.get(skill_name)
            
            print(f"\n{Colors.BOLD}[Step {idx}/{len(self.execution_plan)}] Executing `{skill_name}` via Claude API...{Colors.ENDC}")
            
            if not skill_info:
                print_error(f"No skill definition found for `{skill_name}`. Skipping step.")
                continue
                
            # Build System Prompt (SKILL.md body)
            system_prompt = skill_info["full_content"]
            
            # Format User message containing current context
            user_msg_parts = [
                f"You are executing the Habit: '{self.name}'.",
                f"Goal: {self.habit_data['sections'].get('Goal', 'Not specified.')}",
                "\n### Discovery Answers:"
            ]
            for q_id, ans in self.answers.items():
                user_msg_parts.append(f"- {q_id}: {ans}")
                
            if "gap_context" in self.context:
                user_msg_parts.append(f"\n### Gaps to Fix (from previous iteration):\n{self.context['gap_context']}")
                
            if self.context:
                user_msg_parts.append("\n### Context and Outputs from Previous Steps:")
                for k, v in self.context.items():
                    if k != "gap_context":
                        user_msg_parts.append(f"#### Output of Skill `{k}`:\n{v}")
                        
            user_message = "\n".join(user_msg_parts)
            
            # Call Claude API
            print(f"Calling messages.create for skill `{skill_name}`...")
            try:
                response = self.client.messages.create(
                    model=self.model_name,
                    max_tokens=4000,
                    system=system_prompt,
                    messages=[
                        {"role": "user", "content": user_message}
                    ]
                )
                output_text = response.content[0].text
                
                # Print response summary
                print(f"\n{Colors.BOLD}--- Claude Output for `{skill_name}` ---{Colors.ENDC}")
                print(output_text)
                print(f"{Colors.BOLD}----------------------------------------{Colors.ENDC}\n")
                
                # Save output to context
                self.context[skill_name] = output_text
                
                # Extract and write files if any are generated in the output
                # Resolve base dir of workspace
                project_root = Path(self.habit_data["dir"]).parent.parent
                write_extracted_files(output_text, project_root)
                
                print_success(f"Completed skill `{skill_name}`.")
            except Exception as e:
                print_error(f"Claude API Call failed for skill `{skill_name}`: {str(e)}")
                sys.exit(1)

    def run_evaluation(self):
        print_step("Phase 4: EVALUATE")
        criteria_text = self.habit_data["sections"].get("Quality Criteria", "No rubric specified.")
        
        print("Evaluating output quality using Claude API...")
        
        eval_system_prompt = """You are an independent Quality Evaluator. Your job is to grade the outputs of a workflow against the provided Quality Criteria.

Return your evaluation STRICTLY as a JSON object with this exact structure:
{
  "score": <integer from 0 to 100>,
  "breakdown": "<brief breakdown of how the score was calculated against each criterion>",
  "gap": "<description of any gaps/missing items if score is less than the target, otherwise empty>"
}

Do not include any thinking process, explanations, markdown code blocks, or extra text. Output ONLY the raw JSON.
"""

        eval_user_msg = f"""Quality Rubric:
{criteria_text}

Target Score: {self.quality_target}

Workflow Output Data:
{json.dumps(self.context, indent=2)}
"""

        try:
            response = self.client.messages.create(
                model=self.model_name,
                max_tokens=2000,
                system=eval_system_prompt,
                messages=[
                    {"role": "user", "content": eval_user_msg}
                ]
            )
            raw_text = response.content[0].text.strip()
            
            # Extract JSON if Claude wrapped it in code blocks anyway
            json_match = re.search(r'```json\s*(.*?)\s*```', raw_text, re.DOTALL)
            if json_match:
                raw_text = json_match.group(1).strip()
            else:
                # Stripping standard backticks
                raw_text = raw_text.strip('`').strip()
                
            eval_data = json.loads(raw_text)
            score = int(eval_data.get("score", 0))
            breakdown = eval_data.get("breakdown", "No breakdown provided.")
            gap = eval_data.get("gap", "")
            
            return score, breakdown, gap
        except Exception as e:
            print_warning(f"Failed to perform automated evaluation via Claude API: {str(e)}. Falling back to manual scoring.")
            # Manual scoring fallback
            scores = []
            for i in range(1, 5):
                while True:
                    try:
                        score_input = input(f"  Criterion {i} Score (0-25): ").strip()
                        score = int(score_input)
                        if 0 <= score <= 25:
                            scores.append(score)
                            break
                        else:
                            print("Score must be between 0 and 25.")
                    except ValueError:
                        print("Invalid input. Please enter an integer.")
            total_score = sum(scores)
            breakdown_str = " + ".join(str(s) for s in scores) + f" = {total_score}"
            gap = ""
            if total_score < self.quality_target:
                gap = input("What gaps were identified?:\n> ").strip()
            return total_score, breakdown_str, gap

    def run_escalation(self, score, gap):
        print_step("Phase: ESCALATION")
        escalation_text = self.habit_data["sections"].get("Escalation", "")
        if escalation_text:
            print(f"Escalation Plan: {escalation_text}")
        else:
            print("Escalating to manual resolution.")
        print(f"\nFinal State - Failed with Score: {score}/100. Gap: {gap}")

    def run_output(self):
        print_step("Phase 5: OUTPUT")
        print_success("Final output is validated and ready!")

def main():
    parser = argparse.ArgumentParser(description="Run an Agent Habit end-to-end using Claude API.")
    parser.add_argument("habit", help="Path to or name of the Habit folder.")
    parser.add_argument("--model", default="claude-3-5-sonnet-latest", help="Claude API model to use.")
    args = parser.parse_args()
    
    try:
        habit_data = load_habit(args.habit)
        runner = HabitRunner(habit_data, args.model)
        runner.run()
    except Exception as e:
        print_error(str(e))
        sys.exit(1)

if __name__ == "__main__":
    main()
