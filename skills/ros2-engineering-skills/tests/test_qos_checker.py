"""Tests for qos_checker.py - QoS compatibility checker."""

import json
import os
import subprocess
import sys

import pytest

SCRIPT = os.path.join(os.path.dirname(__file__), "..", "scripts", "qos_checker.py")


def run_script(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, SCRIPT, *args],
        capture_output=True, text=True,
    )


# Also import the module directly for unit-level testing
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))
from qos_checker import (
    QoSProfile, Reliability, Durability, History, Liveliness,
    check_compatibility, parse_qos_string, _expand_qos_shorthand,
    QOS_SHORTHANDS, PRESETS,
)


class TestQoSProfileParsing:
    def test_parse_basic_4_field(self):
        p = parse_qos_string("reliable,volatile,keep_last,10", "test")
        assert p.reliability == Reliability.RELIABLE
        assert p.durability == Durability.VOLATILE
        assert p.history == History.KEEP_LAST
        assert p.depth == 10

    def test_parse_extended_8_field(self):
        p = parse_qos_string("best_effort,transient_local,keep_all,0,100,200,manual_by_topic,300", "test")
        assert p.reliability == Reliability.BEST_EFFORT
        assert p.durability == Durability.TRANSIENT_LOCAL
        assert p.history == History.KEEP_ALL
        assert p.depth == 0
        assert p.deadline_ms == 100
        assert p.lifespan_ms == 200
        assert p.liveliness == Liveliness.MANUAL_BY_TOPIC
        assert p.liveliness_lease_ms == 300

    def test_invalid_field_count_exits(self):
        with pytest.raises(SystemExit):
            parse_qos_string("reliable,volatile,keep_last", "test")

    def test_invalid_reliability_exits(self):
        with pytest.raises(SystemExit):
            parse_qos_string("invalid,volatile,keep_last,5", "test")

    def test_negative_depth_exits(self):
        with pytest.raises(SystemExit):
            parse_qos_string("reliable,volatile,keep_last,-1", "test")


class TestQoSShorthands:
    def test_reliable_shorthand(self):
        p = parse_qos_string("reliable", "test")
        assert p.reliability == Reliability.RELIABLE
        assert p.durability == Durability.VOLATILE
        assert p.depth == 10

    def test_best_effort_shorthand(self):
        p = parse_qos_string("best_effort", "test")
        assert p.reliability == Reliability.BEST_EFFORT

    def test_transient_local_shorthand(self):
        p = parse_qos_string("transient_local", "test")
        assert p.durability == Durability.TRANSIENT_LOCAL
        assert p.reliability == Reliability.RELIABLE

    def test_volatile_shorthand(self):
        p = parse_qos_string("volatile", "test")
        assert p.durability == Durability.VOLATILE

    def test_keep_all_shorthand(self):
        p = parse_qos_string("keep_all", "test")
        assert p.history == History.KEEP_ALL

    def test_expand_unknown_returns_unchanged(self):
        result = _expand_qos_shorthand("reliable,volatile,keep_last,5")
        assert result == "reliable,volatile,keep_last,5"

    def test_all_shorthands_registered(self):
        assert len(QOS_SHORTHANDS) >= 6

    def test_shorthand_cli(self):
        result = run_script("--pub", "reliable", "--sub", "best_effort")
        assert result.returncode == 0
        assert "COMPATIBLE" in result.stdout

    def test_shorthand_incompatible_cli(self):
        result = run_script("--pub", "best_effort", "--sub", "reliable")
        assert result.returncode != 0
        assert "INCOMPATIBLE" in result.stdout


class TestCompatibilityChecks:
    def test_matching_reliable_compatible(self):
        pub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 10)
        sub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 10)
        result = check_compatibility(pub, sub)
        assert result.compatible is True
        assert len(result.issues) == 0

    def test_best_effort_pub_reliable_sub_incompatible(self):
        pub = QoSProfile(Reliability.BEST_EFFORT, Durability.VOLATILE, History.KEEP_LAST, 5)
        sub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 5)
        result = check_compatibility(pub, sub)
        assert result.compatible is False
        assert any("RELIABILITY" in i for i in result.issues)

    def test_volatile_pub_transient_local_sub_incompatible(self):
        pub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 1)
        sub = QoSProfile(Reliability.RELIABLE, Durability.TRANSIENT_LOCAL, History.KEEP_LAST, 1)
        result = check_compatibility(pub, sub)
        assert result.compatible is False
        assert any("DURABILITY" in i for i in result.issues)

    def test_reliable_pub_best_effort_sub_compatible_with_warning(self):
        pub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 5)
        sub = QoSProfile(Reliability.BEST_EFFORT, Durability.VOLATILE, History.KEEP_LAST, 5)
        result = check_compatibility(pub, sub)
        assert result.compatible is True
        assert len(result.warnings) > 0

    def test_keep_all_pub_warns(self):
        pub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_ALL, 0)
        sub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 10)
        result = check_compatibility(pub, sub)
        assert any("KEEP_ALL" in w for w in result.warnings)

    def test_sub_depth_less_than_pub_warns(self):
        pub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 20)
        sub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 5)
        result = check_compatibility(pub, sub)
        assert any("depth" in w.lower() for w in result.warnings)

    def test_deadline_incompatible(self):
        pub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 1,
                         deadline_ms=200)
        sub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 1,
                         deadline_ms=100)
        result = check_compatibility(pub, sub)
        assert result.compatible is False
        assert any("DEADLINE" in i for i in result.issues)

    def test_deadline_incompatible_pub_no_deadline(self):
        """Publisher has no deadline (infinite) but subscriber expects one."""
        pub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 1,
                         deadline_ms=0)
        sub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 1,
                         deadline_ms=100)
        result = check_compatibility(pub, sub)
        assert result.compatible is False
        assert any("DEADLINE" in i for i in result.issues)

    def test_deadline_compatible_pub_has_sub_none(self):
        """Publisher has deadline, subscriber has none (infinite) — compatible."""
        pub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 1,
                         deadline_ms=100)
        sub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 1,
                         deadline_ms=0)
        result = check_compatibility(pub, sub)
        assert result.compatible is True

    def test_liveliness_incompatible(self):
        pub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 1,
                         liveliness=Liveliness.AUTOMATIC)
        sub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 1,
                         liveliness=Liveliness.MANUAL_BY_TOPIC)
        result = check_compatibility(pub, sub)
        assert result.compatible is False
        assert any("LIVELINESS" in i for i in result.issues)

    def test_liveliness_lease_incompatible(self):
        pub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 1,
                         liveliness=Liveliness.MANUAL_BY_TOPIC, liveliness_lease_ms=500)
        sub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 1,
                         liveliness=Liveliness.MANUAL_BY_TOPIC, liveliness_lease_ms=200)
        result = check_compatibility(pub, sub)
        assert result.compatible is False

    def test_liveliness_lease_incompatible_pub_no_lease(self):
        """Publisher has no lease (infinite) but subscriber expects one."""
        pub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 1,
                         liveliness=Liveliness.MANUAL_BY_TOPIC, liveliness_lease_ms=0)
        sub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 1,
                         liveliness=Liveliness.MANUAL_BY_TOPIC, liveliness_lease_ms=200)
        result = check_compatibility(pub, sub)
        assert result.compatible is False
        assert any("LIVELINESS LEASE" in i for i in result.issues)

    def test_depth_zero_keep_last_warns(self):
        pub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 0)
        sub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 1)
        result = check_compatibility(pub, sub)
        assert any("depth=0" in w for w in result.warnings)

    def test_lifespan_shorter_than_deadline_warns(self):
        pub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 1,
                         lifespan_ms=50)
        sub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 1,
                         deadline_ms=100)
        result = check_compatibility(pub, sub)
        assert any("lifespan" in w.lower() for w in result.warnings)


class TestPresets:
    def test_all_presets_exist(self):
        expected = {"sensor", "command", "map", "diagnostics",
                    "parameter_events", "action_feedback", "safety_heartbeat"}
        assert set(PRESETS.keys()) == expected

    def test_sensor_preset_is_best_effort(self):
        assert PRESETS["sensor"]["pub"].reliability == Reliability.BEST_EFFORT
        assert PRESETS["sensor"]["sub"].reliability == Reliability.BEST_EFFORT

    def test_map_preset_is_transient_local(self):
        assert PRESETS["map"]["pub"].durability == Durability.TRANSIENT_LOCAL
        assert PRESETS["map"]["sub"].durability == Durability.TRANSIENT_LOCAL

    def test_safety_heartbeat_has_deadline(self):
        pub = PRESETS["safety_heartbeat"]["pub"]
        assert pub.deadline_ms == 500
        assert pub.lifespan_ms == 1000

    def test_parameter_events_depth(self):
        assert PRESETS["parameter_events"]["pub"].depth == 1000

    def test_all_presets_self_compatible(self):
        for name, profiles in PRESETS.items():
            result = check_compatibility(profiles["pub"], profiles["sub"])
            assert result.compatible is True, f"Preset '{name}' is not self-compatible"


class TestCLI:
    def test_preset_sensor(self):
        result = run_script("--preset", "sensor")
        assert result.returncode == 0
        assert "COMPATIBLE" in result.stdout

    def test_incompatible_returns_nonzero(self):
        result = run_script(
            "--pub", "best_effort,volatile,keep_last,5",
            "--sub", "reliable,volatile,keep_last,5",
        )
        assert result.returncode != 0
        assert "INCOMPATIBLE" in result.stdout

    def test_json_output(self):
        result = run_script(
            "--pub", "reliable,volatile,keep_last,1",
            "--sub", "reliable,volatile,keep_last,1",
            "--json",
        )
        assert result.returncode == 0
        data = json.loads(result.stdout)
        assert data["compatible"] is True
        assert "publisher" in data
        assert "subscriber" in data

    def test_json_output_incompatible(self):
        result = run_script(
            "--pub", "best_effort,volatile,keep_last,5",
            "--sub", "reliable,volatile,keep_last,5",
            "--json",
        )
        data = json.loads(result.stdout)
        assert data["compatible"] is False
        assert len(data["errors"]) > 0

    def test_no_args_shows_help(self):
        result = run_script()
        assert result.returncode != 0

    def test_extended_format_cli(self):
        result = run_script(
            "--pub", "reliable,volatile,keep_last,1,100,0,automatic,0",
            "--sub", "reliable,volatile,keep_last,1,200,0,automatic,0",
        )
        assert result.returncode == 0


class TestParsingErrorPaths:
    """Test error-handling paths in parse_qos_string for coverage."""

    def test_invalid_durability_exits(self):
        with pytest.raises(SystemExit):
            parse_qos_string("reliable,invalid,keep_last,5", "test")

    def test_invalid_history_exits(self):
        with pytest.raises(SystemExit):
            parse_qos_string("reliable,volatile,invalid,5", "test")

    def test_non_numeric_depth_exits(self):
        with pytest.raises(SystemExit):
            parse_qos_string("reliable,volatile,keep_last,abc", "test")

    def test_negative_deadline_exits(self):
        with pytest.raises(SystemExit):
            parse_qos_string("reliable,volatile,keep_last,5,-1,0,automatic,0", "test")

    def test_negative_lifespan_exits(self):
        with pytest.raises(SystemExit):
            parse_qos_string("reliable,volatile,keep_last,5,0,-1,automatic,0", "test")

    def test_invalid_liveliness_exits(self):
        with pytest.raises(SystemExit):
            parse_qos_string("reliable,volatile,keep_last,5,0,0,invalid,0", "test")

    def test_negative_liveliness_lease_exits(self):
        with pytest.raises(SystemExit):
            parse_qos_string("reliable,volatile,keep_last,5,0,0,automatic,-1", "test")


class TestMainFunction:
    """Test main() directly for coverage."""

    def test_main_preset(self, monkeypatch):
        from qos_checker import main
        monkeypatch.setattr(
            "sys.argv", ["qos_checker.py", "--preset", "sensor"])
        with pytest.raises(SystemExit) as exc_info:
            main()
        assert exc_info.value.code == 0

    def test_main_custom_profiles(self, monkeypatch):
        from qos_checker import main
        monkeypatch.setattr(
            "sys.argv", ["qos_checker.py",
                         "--pub", "reliable,volatile,keep_last,1",
                         "--sub", "reliable,volatile,keep_last,1"])
        with pytest.raises(SystemExit) as exc_info:
            main()
        assert exc_info.value.code == 0

    def test_main_incompatible(self, monkeypatch):
        from qos_checker import main
        monkeypatch.setattr(
            "sys.argv", ["qos_checker.py",
                         "--pub", "best_effort,volatile,keep_last,5",
                         "--sub", "reliable,volatile,keep_last,5"])
        with pytest.raises(SystemExit) as exc_info:
            main()
        assert exc_info.value.code == 1

    def test_main_json_output(self, monkeypatch):
        from qos_checker import main
        monkeypatch.setattr(
            "sys.argv", ["qos_checker.py",
                         "--preset", "command", "--json"])
        with pytest.raises(SystemExit) as exc_info:
            main()
        assert exc_info.value.code == 0

    def test_main_no_args_exits(self, monkeypatch):
        from qos_checker import main
        monkeypatch.setattr("sys.argv", ["qos_checker.py"])
        with pytest.raises(SystemExit) as exc_info:
            main()
        assert exc_info.value.code == 1


class TestPrintFunctions:
    """Test print/display functions for coverage."""

    def test_print_result_compatible(self, capsys):
        from qos_checker import print_result
        pub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE,
                         History.KEEP_LAST, 1, "Pub")
        sub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE,
                         History.KEEP_LAST, 1, "Sub")
        result = check_compatibility(pub, sub)
        print_result(pub, sub, result)
        captured = capsys.readouterr()
        assert "COMPATIBLE" in captured.out

    def test_print_result_incompatible(self, capsys):
        from qos_checker import print_result
        pub = QoSProfile(Reliability.BEST_EFFORT, Durability.VOLATILE,
                         History.KEEP_LAST, 5, "Pub")
        sub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE,
                         History.KEEP_LAST, 5, "Sub")
        result = check_compatibility(pub, sub)
        print_result(pub, sub, result)
        captured = capsys.readouterr()
        assert "INCOMPATIBLE" in captured.out
        assert "ERROR" in captured.out
        assert "Suggestions" in captured.out

    def test_print_result_json(self, capsys):
        from qos_checker import print_result_json
        pub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE,
                         History.KEEP_LAST, 1, "Pub")
        sub = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE,
                         History.KEEP_LAST, 1, "Sub")
        result = check_compatibility(pub, sub)
        print_result_json(pub, sub, result)
        captured = capsys.readouterr()
        data = json.loads(captured.out)
        assert data["compatible"] is True


class TestVersion:
    def test_version_flag(self):
        result = run_script("--version")
        assert result.returncode == 0
        assert "0.1.0" in result.stdout


class TestQoSProfileDisplay:
    def test_str_representation(self):
        p = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 10, "Test")
        s = str(p)
        assert "[Test]" in s
        assert "reliable" in s
        assert "volatile" in s

    def test_to_dict(self):
        p = QoSProfile(Reliability.RELIABLE, Durability.VOLATILE, History.KEEP_LAST, 10, "Test")
        d = p.to_dict()
        assert d["reliability"] == "reliable"
        assert d["durability"] == "volatile"
        assert d["depth"] == 10
