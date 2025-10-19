#!/usr/bin/env python3
"""
Create a new Rocq/Coq proof file from templates.

Usage:
    python new_proof.py theorem_name
    python new_proof.py theorem_name --template induction
    python new_proof.py theorem_name --template case_analysis --output custom.v

Available templates:
    - simple: Basic proof structure
    - induction: Proof by induction
    - case_analysis: Proof by case analysis
    - rewriting: Rewriting-based proof
    - tactical: Complex proof with tactics
"""

import sys
import argparse
from pathlib import Path


# Template definitions
TEMPLATES = {
    'simple': '''(** {theorem_name} - Simple proof *)

Theorem {theorem_name} : forall (n : nat), (* TODO: Add property *).
Proof.
  intro n.
  (* TODO: Complete proof *)
Admitted. (* Replace with Qed when complete *)
''',

    'induction': '''(** {theorem_name} - Proof by induction *)

Theorem {theorem_name} : forall (n : nat), (* TODO: Add property about n *).
Proof.
  intro n.
  induction n as [| n' IHn'].
  - (* Base case: n = 0 *)
    (* TODO: Prove for 0 *)
  - (* Inductive case: n = S n' *)
    (* IHn' : property holds for n' *)
    (* TODO: Prove for S n' using IHn' *)
Admitted. (* Replace with Qed when complete *)
''',

    'case_analysis': '''(** {theorem_name} - Proof by case analysis *)

Theorem {theorem_name} : forall (x : (* TODO: type *)), (* TODO: property *).
Proof.
  intro x.
  destruct x as [  (* TODO: patterns *) ].
  - (* Case 1 *)
    (* TODO: Prove first case *)
  - (* Case 2 *)
    (* TODO: Prove second case *)
Admitted. (* Replace with Qed when complete *)
''',

    'rewriting': '''(** {theorem_name} - Proof using rewriting *)

Theorem {theorem_name} : forall (n m : nat),
  (* TODO: Add equality involving n and m *).
Proof.
  intros n m.
  (* TODO: Add hypotheses if needed *)
  (* rewrite lemma_name. *)
  (* simpl. *)
  (* reflexivity. *)
Admitted. (* Replace with Qed when complete *)
''',

    'tactical': '''(** {theorem_name} - Complex tactical proof *)

(** Helper lemma 1 *)
Lemma {theorem_name}_helper1 : (* TODO: Helper property *).
Proof.
  (* TODO: Prove helper *)
Admitted.

(** Helper lemma 2 *)
Lemma {theorem_name}_helper2 : (* TODO: Helper property *).
Proof.
  (* TODO: Prove helper *)
Admitted.

(** Main theorem *)
Theorem {theorem_name} : (* TODO: Main property *).
Proof.
  (* Break down the problem *)
  (* apply {theorem_name}_helper1. *)
  (* apply {theorem_name}_helper2. *)
Admitted. (* Replace with Qed when complete *)
'''
}


def sanitize_name(name):
    """Convert name to valid Coq identifier."""
    # Replace invalid characters with underscores
    sanitized = ''.join(c if c.isalnum() or c == '_' else '_' for c in name)
    # Ensure it starts with a letter
    if sanitized and sanitized[0].isdigit():
        sanitized = 'theorem_' + sanitized
    return sanitized or 'new_theorem'


def create_proof_file(theorem_name, template='simple', output=None):
    """
    Create a new proof file from template.

    Args:
        theorem_name: Name of the theorem
        template: Template to use
        output: Output file path (optional)

    Returns:
        Path to created file
    """
    # Sanitize theorem name
    clean_name = sanitize_name(theorem_name)

    # Get template
    if template not in TEMPLATES:
        print(f"Error: Unknown template '{template}'")
        print(f"Available templates: {', '.join(TEMPLATES.keys())}")
        return None

    template_content = TEMPLATES[template]

    # Generate content
    content = template_content.format(theorem_name=clean_name)

    # Determine output file
    if output:
        output_path = Path(output)
    else:
        output_path = Path(f"{clean_name}.v")

    # Check if file exists
    if output_path.exists():
        response = input(f"File {output_path} already exists. Overwrite? (y/N): ")
        if response.lower() != 'y':
            print("Cancelled.")
            return None

    # Write file
    try:
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(content)
        return output_path
    except Exception as e:
        print(f"Error writing file: {e}")
        return None


def main():
    parser = argparse.ArgumentParser(
        description="Create a new Rocq/Coq proof file from templates"
    )
    parser.add_argument('name', help='Name of the theorem')
    parser.add_argument('--template', '-t', default='simple',
                        choices=list(TEMPLATES.keys()),
                        help='Template to use (default: simple)')
    parser.add_argument('--output', '-o', help='Output file path')
    parser.add_argument('--list-templates', '-l', action='store_true',
                        help='List available templates')

    args = parser.parse_args()

    if args.list_templates:
        print("Available templates:")
        for name in TEMPLATES.keys():
            print(f"  - {name}")
        return 0

    print(f"Creating proof: {args.name}")
    print(f"Template: {args.template}")

    result = create_proof_file(args.name, args.template, args.output)

    if result:
        print(f"\n[SUCCESS] Created: {result}")
        print("\nNext steps:")
        print(f"  1. Edit {result} to complete the proof")
        print("  2. Replace TODO comments with actual proof")
        print(f"  3. Run: python scripts/verify_proof.py {result}")
        print("  4. Replace 'Admitted' with 'Qed' when proof is complete")
        return 0
    else:
        return 1


if __name__ == "__main__":
    sys.exit(main())
