"""Tests for extract_form_field_info.make_field_dict."""

from extract_form_field_info import make_field_dict


def test_choice_options_plain_strings() -> None:
    """PDF /Opt may be a list of strings, not [export, display] pairs."""
    field = {"/FT": "/Ch", "/_States_": ["Apple", "Banana"]}
    result = make_field_dict(field, "fruit")
    assert result["type"] == "choice"
    assert result["choice_options"] == [
        {"value": "Apple", "text": "Apple"},
        {"value": "Banana", "text": "Banana"},
    ]


def test_choice_options_export_display_pairs() -> None:
    field = {"/FT": "/Ch", "/_States_": [["US", "United States"], ["CA", "Canada"]]}
    result = make_field_dict(field, "country")
    assert result["choice_options"] == [
        {"value": "US", "text": "United States"},
        {"value": "CA", "text": "Canada"},
    ]


def test_choice_options_mixed() -> None:
    field = {"/FT": "/Ch", "/_States_": ["Solo", ["A", "Alpha"]]}
    result = make_field_dict(field, "mixed")
    assert result["choice_options"] == [
        {"value": "Solo", "text": "Solo"},
        {"value": "A", "text": "Alpha"},
    ]
