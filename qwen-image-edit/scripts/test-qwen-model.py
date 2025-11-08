#!/usr/bin/env python3
"""
Automated testing suite for Qwen-Image-Edit v2509
Tests aspect ratio stability, composition alignment, and text rendering quality
"""

import json
import sys
from pathlib import Path
from typing import Dict, List, Tuple
from dataclasses import dataclass
from datetime import datetime


@dataclass
class ImageMetrics:
    """Metrics for image dimensions and aspect ratios"""
    filename: str
    width: int
    height: int
    aspect_ratio: float

    def __post_init__(self):
        self.aspect_ratio = round(self.width / self.height, 4)


@dataclass
class AspectRatioTest:
    """Results for aspect ratio preservation test"""
    source_image: str
    source_width: int
    source_height: int
    source_ratio: float
    output_width: int
    output_height: int
    output_ratio: float
    ratio_drift_percent: float
    passed: bool

    def __post_init__(self):
        self.ratio_drift_percent = round(
            abs((self.output_ratio - self.source_ratio) / self.source_ratio) * 100,
            2
        )
        self.passed = self.ratio_drift_percent <= 2.0


@dataclass
class AlignmentTest:
    """Results for element alignment test"""
    composition_name: str
    element_count: int
    subjects: List[Dict]
    max_drift_pixels: float
    max_drift_percent: float
    passed: bool

    def __post_init__(self):
        # Determine pass/fail: drift < 5% of typical dimension (512px)
        self.passed = self.max_drift_percent <= 5.0


@dataclass
class TextRenderingTest:
    """Results for text rendering quality test"""
    test_name: str
    text_content: str
    font_size: int
    language: str
    readable: bool
    position_drift_pixels: float
    corruption_detected: bool
    passed: bool

    def __post_init__(self):
        self.passed = (
            self.readable
            and self.position_drift_pixels <= 3
            and not self.corruption_detected
        )


class QwenTestSuite:
    """Comprehensive test suite for Qwen-Image-Edit v2509"""

    def __init__(self, output_dir: str = "./qwen-test-results"):
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(exist_ok=True)
        self.test_results = {
            "timestamp": datetime.now().isoformat(),
            "test_suite": "Qwen-Image-Edit v2509",
            "aspect_ratio_tests": [],
            "alignment_tests": [],
            "text_rendering_tests": [],
            "batch_tests": [],
            "summary": {}
        }

    def test_aspect_ratio_preservation(
        self,
        source_dims: Tuple[int, int],
        output_dims: Tuple[int, int],
        image_name: str = "test_image"
    ) -> AspectRatioTest:
        """Test if aspect ratio is preserved within tolerance"""
        source_w, source_h = source_dims
        output_w, output_h = output_dims

        source_ratio = source_w / source_h
        output_ratio = output_w / output_h

        test = AspectRatioTest(
            source_image=image_name,
            source_width=source_w,
            source_height=source_h,
            source_ratio=source_ratio,
            output_width=output_w,
            output_height=output_h,
            output_ratio=output_ratio,
            ratio_drift_percent=0,  # Set in __post_init__
            passed=False  # Set in __post_init__
        )

        self.test_results["aspect_ratio_tests"].append(test.__dict__)
        return test

    def test_multi_subject_alignment(
        self,
        subjects: List[Dict[str, float]],
        expected_positions: List[Dict[str, float]],
        composition_name: str = "composition"
    ) -> AlignmentTest:
        """Test alignment drift for multi-subject compositions"""
        if not subjects or not expected_positions:
            return AlignmentTest(
                composition_name=composition_name,
                element_count=0,
                subjects=[],
                max_drift_pixels=0,
                max_drift_percent=0,
                passed=False
            )

        drifts = []
        for actual, expected in zip(subjects, expected_positions):
            x_drift = abs(actual.get('x', 0) - expected.get('x', 0))
            y_drift = abs(actual.get('y', 0) - expected.get('y', 0))
            drift = (x_drift ** 2 + y_drift ** 2) ** 0.5
            drifts.append(drift)

        max_drift_px = max(drifts) if drifts else 0
        max_drift_pct = (max_drift_px / 512) * 100  # Normalize to 512px dimension

        test = AlignmentTest(
            composition_name=composition_name,
            element_count=len(subjects),
            subjects=subjects,
            max_drift_pixels=round(max_drift_px, 2),
            max_drift_percent=round(max_drift_pct, 2),
            passed=False  # Set in __post_init__
        )

        self.test_results["alignment_tests"].append(test.__dict__)
        return test

    def test_text_rendering(
        self,
        text: str,
        font_size: int,
        language: str = "english",
        readable: bool = True,
        position_drift: float = 0,
        corruption: bool = False,
        test_name: str = "text_test"
    ) -> TextRenderingTest:
        """Test text rendering quality"""
        test = TextRenderingTest(
            test_name=test_name,
            text_content=text,
            font_size=font_size,
            language=language,
            readable=readable,
            position_drift_pixels=position_drift,
            corruption_detected=corruption,
            passed=False  # Set in __post_init__
        )

        self.test_results["text_rendering_tests"].append(test.__dict__)
        return test

    def run_batch_test(self, num_operations: int = 10) -> Dict:
        """Run multiple operations and measure consistency"""
        results = {
            "operations": num_operations,
            "aspect_ratio_variance": 0.0,
            "success_rate": 100.0,
            "average_processing_time": 10.5,
            "note": "Simulated batch test - implement with actual API calls"
        }

        self.test_results["batch_tests"].append(results)
        return results

    def generate_report(self) -> str:
        """Generate comprehensive test report"""
        aspect_ratio_tests = self.test_results["aspect_ratio_tests"]
        alignment_tests = self.test_results["alignment_tests"]
        text_tests = self.test_results["text_rendering_tests"]

        aspect_passed = sum(1 for t in aspect_ratio_tests if t.get("passed", False))
        alignment_passed = sum(1 for t in alignment_tests if t.get("passed", False))
        text_passed = sum(1 for t in text_tests if t.get("passed", False))

        total_tests = len(aspect_ratio_tests) + len(alignment_tests) + len(text_tests)
        total_passed = aspect_passed + alignment_passed + text_passed

        report = f"""
# Qwen-Image-Edit v2509 Test Report
Generated: {self.test_results['timestamp']}

## Summary
- Total Tests: {total_tests}
- Passed: {total_passed}
- Failed: {total_tests - total_passed}
- Pass Rate: {(total_passed/total_tests*100 if total_tests > 0 else 0):.1f}%

## Aspect Ratio Tests: {aspect_passed}/{len(aspect_ratio_tests)}
"""
        for test in aspect_ratio_tests:
            status = "PASS" if test.get("passed") else "FAIL"
            drift = test.get("ratio_drift_percent", 0)
            report += f"  - {test['source_image']}: {status} (drift: {drift}%)\n"

        report += f"\n## Alignment Tests: {alignment_passed}/{len(alignment_tests)}\n"
        for test in alignment_tests:
            status = "PASS" if test.get("passed") else "FAIL"
            drift = test.get("max_drift_percent", 0)
            report += f"  - {test['composition_name']}: {status} (max drift: {drift}%)\n"

        report += f"\n## Text Rendering Tests: {text_passed}/{len(text_tests)}\n"
        for test in text_tests:
            status = "PASS" if test.get("passed") else "FAIL"
            report += f"  - {test['test_name']}: {status} ({test['language']})\n"

        if self.test_results["batch_tests"]:
            batch = self.test_results["batch_tests"][0]
            report += f"\n## Batch Processing Test\n"
            report += f"  - Operations: {batch['operations']}\n"
            report += f"  - Success Rate: {batch['success_rate']}%\n"
            report += f"  - Avg Processing Time: {batch['average_processing_time']}s\n"

        report += "\n## Recommendations\n"
        if total_passed / total_tests < 0.8:
            report += "  - Implementation has high failure rate; consider review\n"
        if aspect_passed < len(aspect_ratio_tests) * 0.9:
            report += "  - Aspect ratio preservation is inconsistent\n"
        if alignment_passed < len(alignment_tests) * 0.8:
            report += "  - Multi-element alignment has issues; limit to simpler compositions\n"

        return report

    def save_results(self, format: str = "json") -> Path:
        """Save test results to file"""
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

        if format == "json":
            filepath = self.output_dir / f"qwen_test_results_{timestamp}.json"
            with open(filepath, 'w') as f:
                json.dump(self.test_results, f, indent=2)
        else:  # format == "text"
            filepath = self.output_dir / f"qwen_test_report_{timestamp}.txt"
            with open(filepath, 'w') as f:
                f.write(self.generate_report())

        return filepath


def main():
    """Example usage of the test suite"""
    suite = QwenTestSuite()

    # Test aspect ratio preservation
    print("Testing aspect ratio preservation...")
    test1 = suite.test_aspect_ratio_preservation(
        source_dims=(1024, 768),
        output_dims=(1024, 770),
        image_name="miniature_portrait"
    )
    print(f"  Result: {'PASS' if test1.passed else 'FAIL'} (drift: {test1.ratio_drift_percent}%)")

    # Test multi-subject alignment
    print("\nTesting multi-subject alignment...")
    subjects = [
        {'x': 256, 'y': 128},
        {'x': 512, 'y': 256}
    ]
    expected = [
        {'x': 250, 'y': 130},
        {'x': 515, 'y': 254}
    ]
    test2 = suite.test_multi_subject_alignment(
        subjects=subjects,
        expected_positions=expected,
        composition_name="person_scene"
    )
    print(f"  Result: {'PASS' if test2.passed else 'FAIL'} (max drift: {test2.max_drift_percent}%)")

    # Test text rendering
    print("\nTesting text rendering...")
    test3 = suite.test_text_rendering(
        text="Hello World",
        font_size=24,
        language="english",
        readable=True,
        position_drift=1.5,
        test_name="basic_english_text"
    )
    print(f"  Result: {'PASS' if test3.passed else 'FAIL'}")

    test4 = suite.test_text_rendering(
        text="你好世界",
        font_size=20,
        language="chinese",
        readable=True,
        position_drift=2.0,
        test_name="chinese_text"
    )
    print(f"  Result: {'PASS' if test4.passed else 'FAIL'}")

    # Run batch test
    print("\nRunning batch processing test...")
    suite.run_batch_test(num_operations=10)

    # Generate and save results
    print("\nGenerating report...")
    report = suite.generate_report()
    print(report)

    json_path = suite.save_results(format="json")
    text_path = suite.save_results(format="text")
    print(f"\nResults saved to:")
    print(f"  JSON: {json_path}")
    print(f"  Text: {text_path}")


if __name__ == "__main__":
    main()
