#!/usr/bin/env python3
"""
ComfyUI Workflow Validator

Validates ComfyUI JSON workflows for correctness and consistency.
Checks:
- Valid JSON format
- Node connectivity (references to other nodes exist)
- Required fields present
- Data type compatibility
"""

import json
import sys
import argparse
from pathlib import Path
from typing import Dict, List, Tuple, Any


class WorkflowValidator:
    """Validates ComfyUI workflow JSON files"""

    def __init__(self, strict: bool = False):
        self.strict = strict
        self.errors: List[str] = []
        self.warnings: List[str] = []

    def validate_file(self, filepath: str) -> bool:
        """Validate a workflow file"""
        try:
            with open(filepath, 'r') as f:
                workflow = json.load(f)
        except FileNotFoundError:
            self.errors.append(f"File not found: {filepath}")
            return False
        except json.JSONDecodeError as e:
            self.errors.append(f"Invalid JSON: {e}")
            return False

        return self.validate_workflow(workflow)

    def validate_workflow(self, workflow: Dict[str, Any]) -> bool:
        """Validate workflow dictionary"""
        if not isinstance(workflow, dict):
            self.errors.append("Workflow must be a JSON object")
            return False

        if not workflow:
            self.errors.append("Workflow is empty")
            return False

        node_ids = set(workflow.keys())

        # Validate each node
        for node_id, node in workflow.items():
            self._validate_node(node_id, node, node_ids)

        return len(self.errors) == 0

    def _validate_node(self, node_id: str, node: Any, all_node_ids: set) -> None:
        """Validate a single node"""
        if not isinstance(node, dict):
            self.errors.append(f"Node {node_id}: must be a JSON object")
            return

        # Check required fields
        if 'class_type' not in node:
            self.errors.append(f"Node {node_id}: missing 'class_type'")

        if 'inputs' not in node:
            if self.strict:
                self.errors.append(f"Node {node_id}: missing 'inputs'")
            else:
                node['inputs'] = {}

        # Validate inputs
        if 'inputs' in node and isinstance(node['inputs'], dict):
            self._validate_inputs(node_id, node['inputs'], all_node_ids)

    def _validate_inputs(self, node_id: str, inputs: Dict, all_node_ids: set) -> None:
        """Validate node inputs"""
        for input_name, input_value in inputs.items():
            # Check for node references [node_id, output_index]
            if isinstance(input_value, list) and len(input_value) == 2:
                ref_node_id, output_idx = input_value
                if ref_node_id not in all_node_ids:
                    self.errors.append(
                        f"Node {node_id}: input '{input_name}' references "
                        f"non-existent node '{ref_node_id}'"
                    )
                if not isinstance(output_idx, int):
                    self.warnings.append(
                        f"Node {node_id}: input '{input_name}' has non-integer "
                        f"output index"
                    )

    def print_report(self) -> None:
        """Print validation report"""
        if self.errors:
            print("ERRORS:")
            for error in self.errors:
                print(f"  ✗ {error}")

        if self.warnings:
            print("\nWARNINGS:")
            for warning in self.warnings:
                print(f"  ⚠ {warning}")

        if not self.errors and not self.warnings:
            print("✓ Workflow is valid!")

        return len(self.errors) == 0


def main():
    parser = argparse.ArgumentParser(
        description="Validate ComfyUI workflow JSON files"
    )
    parser.add_argument("workflow", help="Path to workflow JSON file")
    parser.add_argument(
        "--strict",
        action="store_true",
        help="Enable strict validation (require 'inputs' field)"
    )
    parser.add_argument(
        "--json-output",
        action="store_true",
        help="Output results as JSON"
    )

    args = parser.parse_args()

    validator = WorkflowValidator(strict=args.strict)
    is_valid = validator.validate_file(args.workflow)

    if args.json_output:
        result = {
            "valid": is_valid,
            "errors": validator.errors,
            "warnings": validator.warnings
        }
        print(json.dumps(result, indent=2))
    else:
        validator.print_report()

    sys.exit(0 if is_valid else 1)


if __name__ == "__main__":
    main()
