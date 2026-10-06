#!/usr/bin/env python3
"""
Test Runner for Security Scanner
Tests scanner against all malicious samples and reports detection rate
"""

import sys
import json
from pathlib import Path
import subprocess

def run_tests():
    """Run scanner against all malicious samples"""
    
    test_dir = Path(__file__).parent.parent / "tests" / "malicious_samples"
    scanner = Path(__file__).parent / "security_scanner.py"
    
    if not scanner.exists():
        print("Error: Scanner not found")
        return 1
    
    # Expected detections per sample
    expected_detections = {
        '01_indirect_execution.py': ['Obfuscated Execution', 'getattr'],
        '02_hidden_payload.txt': ['Command Injection'],
        '03_encoding.py': ['Code Obfuscation', 'ROT'],
        '04_shell.py': ['Shell Injection'],
        '05_timebomb.py': ['Time Bomb'],
        '06_typosquat.py': ['Supply Chain', 'typosquat'],
        '07_env.py': ['Environment Manipulation'],
        '08_sandbox.py': ['Sandbox Escape', 'Class'],
        '09_exfil.py': ['Network Access'],
        '10_yaml.md': ['YAML Injection'],
        '11_import_hook.py': ['Import Hijacking'],
    }
    
    print("="*70)
    print("SECURITY SCANNER TEST SUITE")
    print("="*70)
    
    total_samples = len(expected_detections)
    detected = 0
    failed = []
    
    for sample_file, expected_patterns in expected_detections.items():
        sample_path = test_dir / sample_file
        
        if not sample_path.exists():
            print(f"⚠️  SKIP: {sample_file} (not found)")
            continue
        
        # Run scanner on this sample
        try:
            result = subprocess.run(
                [sys.executable, str(scanner), str(sample_path)],
                capture_output=True,
                text=True,
                timeout=5
            )
            
            report = json.loads(result.stdout)
            
            # Check if expected patterns were detected
            findings_text = json.dumps(report['findings']).lower()
            detected_count = sum(1 for pattern in expected_patterns 
                                if pattern.lower() in findings_text)
            
            if detected_count == len(expected_patterns):
                print(f"✓ PASS: {sample_file}")
                print(f"   Found: {report['summary']['total_findings']} findings")
                detected += 1
            else:
                print(f"✗ FAIL: {sample_file}")
                print(f"   Expected: {expected_patterns}")
                print(f"   Found {detected_count}/{len(expected_patterns)} patterns")
                failed.append(sample_file)
                
        except subprocess.TimeoutExpired:
            print(f"✗ TIMEOUT: {sample_file}")
            failed.append(sample_file)
        except json.JSONDecodeError:
            print(f"✗ ERROR: {sample_file} (invalid JSON)")
            failed.append(sample_file)
        except Exception as e:
            print(f"✗ ERROR: {sample_file} ({str(e)})")
            failed.append(sample_file)
    
    print("\n" + "="*70)
    print(f"RESULTS: {detected}/{total_samples} samples detected")
    print(f"Detection Rate: {detected/total_samples*100:.1f}%")
    
    if failed:
        print(f"\nFailed samples:")
        for f in failed:
            print(f"  - {f}")
    else:
        print("\n🎉 All tests passed!")
    
    print("="*70)
    
    return 0 if not failed else 1


if __name__ == '__main__':
    sys.exit(run_tests())
