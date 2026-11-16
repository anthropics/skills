"""Regression tests for issue #1982, part 2.

The eval viewer's feedback endpoint (POST /api/feedback) used to accept
cross-origin writes with no Origin, Host or Content-Type check: a forged
POST with ``Origin: http://evil.example`` and ``Content-Type: text/plain``
returned 200 and overwrote feedback.json. DNS rebinding could also reach
GET /api/feedback because the Host header was never validated.

These tests drive the real ReviewHandler on a real ephemeral localhost
server (no mocking of the security checks) and compare feedback.json
byte-for-byte on every rejected write.

Part 1 of #1982 (script-context injection in the embedded JSON) is
covered by open PR #1990, not by this module.
"""

import http.client
import json
import sys
import threading
from functools import partial
from http.server import HTTPServer
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))

from generate_review import ReviewHandler  # noqa: E402

ORIGINAL_REVIEWS = {"reviews": [{"id": "original-review", "result": "keep"}]}
FORGED_REVIEWS = {"reviews": [{"id": "forged-review", "result": "approve"}]}


@pytest.fixture()
def server(tmp_path):
    """A workspace with one run and a review server on an ephemeral port."""
    workspace = tmp_path / "workspace"
    run_outputs = workspace / "iter-1" / "outputs"
    run_outputs.mkdir(parents=True)
    (run_outputs / "out.txt").write_text("some eval output\n")
    feedback_path = workspace / "feedback.json"
    feedback_path.write_text(json.dumps(ORIGINAL_REVIEWS) + "\n")

    handler = partial(ReviewHandler, workspace, "test-skill", feedback_path, {}, None)
    httpd = HTTPServer(("127.0.0.1", 0), handler)
    port = httpd.server_address[1]
    thread = threading.Thread(target=httpd.serve_forever, daemon=True)
    thread.start()
    try:
        yield port, feedback_path
    finally:
        httpd.shutdown()
        httpd.server_close()
        thread.join(timeout=5)


def request(port, method, path, body=None, *, origin="__omit__",
            referer="__omit__", content_type="__omit__", host="__omit__",
            skip_host=False):
    """One HTTP request against the review server.

    ``origin``/``referer``/``content_type``/``host`` default to omitted;
    pass an explicit value (including None) to send that header.
    """
    conn = http.client.HTTPConnection("127.0.0.1", port, timeout=5)
    try:
        # Use skip_host and send Host explicitly: putrequest() would
        # otherwise send the connection's own Host first, and the
        # server reads the first Host header it sees.
        conn.putrequest(method, path, skip_host=True)
        if not skip_host:
            if host == "__omit__":
                conn.putheader("Host", f"127.0.0.1:{port}")
            elif host is not None:
                conn.putheader("Host", host)
        if origin != "__omit__" and origin is not None:
            conn.putheader("Origin", origin)
        if referer != "__omit__" and referer is not None:
            conn.putheader("Referer", referer)
        if content_type != "__omit__" and content_type is not None:
            conn.putheader("Content-Type", content_type)
        body_bytes = None
        if body is not None:
            body_bytes = body if isinstance(body, bytes) else body.encode()
            conn.putheader("Content-Length", str(len(body_bytes)))
        conn.endheaders(body_bytes)
        resp = conn.getresponse()
        return resp.status, resp.read()
    finally:
        conn.close()


def same_origin(port, host="127.0.0.1"):
    return f"http://{host}:{port}"


def feedback_bytes(feedback_path):
    return feedback_path.read_bytes()


def original_bytes():
    return (json.dumps(ORIGINAL_REVIEWS) + "\n").encode()


# --- POST: legitimate writes -----------------------------------------------

def test_same_origin_post_writes_feedback(server):
    port, feedback_path = server
    status, body = request(
        port, "POST", "/api/feedback", json.dumps(FORGED_REVIEWS),
        origin=same_origin(port), content_type="application/json",
    )
    assert status == 200
    assert json.loads(body)["ok"] is True
    assert json.loads(feedback_bytes(feedback_path)) == FORGED_REVIEWS


def test_missing_origin_post_from_script_client_writes_feedback(server):
    port, feedback_path = server
    status, body = request(
        port, "POST", "/api/feedback", json.dumps(FORGED_REVIEWS),
        content_type="application/json",
    )
    assert status == 200
    assert json.loads(body)["ok"] is True
    assert json.loads(feedback_bytes(feedback_path)) == FORGED_REVIEWS


def test_localhost_host_post_writes_feedback(server):
    port, feedback_path = server
    status, _ = request(
        port, "POST", "/api/feedback", json.dumps(FORGED_REVIEWS),
        origin=same_origin(port, "localhost"),
        content_type="application/json",
        host=f"localhost:{port}",
    )
    assert status == 200
    assert json.loads(feedback_bytes(feedback_path)) == FORGED_REVIEWS


def test_json_charset_parameter_accepted(server):
    port, feedback_path = server
    status, _ = request(
        port, "POST", "/api/feedback", json.dumps(FORGED_REVIEWS),
        origin=same_origin(port),
        content_type="application/json; charset=utf-8",
    )
    assert status == 200
    assert json.loads(feedback_bytes(feedback_path)) == FORGED_REVIEWS


def test_json_content_type_case_insensitive(server):
    port, feedback_path = server
    status, _ = request(
        port, "POST", "/api/feedback", json.dumps(FORGED_REVIEWS),
        origin=same_origin(port), content_type="APPLICATION/JSON",
    )
    assert status == 200
    assert json.loads(feedback_bytes(feedback_path)) == FORGED_REVIEWS


# --- POST: the forged write from issue #1982 --------------------------------

def test_forged_cross_origin_text_plain_post_rejected(server):
    """The verbatim attack from #1982 part 2."""
    port, feedback_path = server
    status, body = request(
        port, "POST", "/api/feedback", json.dumps(FORGED_REVIEWS),
        origin="http://evil.example", content_type="text/plain",
    )
    assert status == 403
    assert feedback_bytes(feedback_path) == original_bytes()


def test_foreign_origin_json_post_rejected(server):
    port, feedback_path = server
    status, _ = request(
        port, "POST", "/api/feedback", json.dumps(FORGED_REVIEWS),
        origin="http://evil.example", content_type="application/json",
    )
    assert status == 403
    assert feedback_bytes(feedback_path) == original_bytes()


def test_foreign_origin_https_post_rejected(server):
    port, feedback_path = server
    status, _ = request(
        port, "POST", "/api/feedback", json.dumps(FORGED_REVIEWS),
        origin="https://evil.example", content_type="application/json",
    )
    assert status == 403
    assert feedback_bytes(feedback_path) == original_bytes()


def test_null_origin_post_rejected(server):
    port, feedback_path = server
    status, _ = request(
        port, "POST", "/api/feedback", json.dumps(FORGED_REVIEWS),
        origin="null", content_type="application/json",
    )
    assert status == 403
    assert feedback_bytes(feedback_path) == original_bytes()


def test_same_origin_text_plain_post_rejected(server):
    """Content-Type alone must reject, even from the right origin."""
    port, feedback_path = server
    status, _ = request(
        port, "POST", "/api/feedback", json.dumps(FORGED_REVIEWS),
        origin=same_origin(port), content_type="text/plain",
    )
    assert status == 415
    assert feedback_bytes(feedback_path) == original_bytes()


def test_missing_origin_text_plain_post_rejected(server):
    port, feedback_path = server
    status, _ = request(
        port, "POST", "/api/feedback", json.dumps(FORGED_REVIEWS),
        content_type="text/plain",
    )
    assert status == 415
    assert feedback_bytes(feedback_path) == original_bytes()


def test_missing_content_type_post_rejected(server):
    port, feedback_path = server
    status, _ = request(
        port, "POST", "/api/feedback", json.dumps(FORGED_REVIEWS),
        origin=same_origin(port),
    )
    assert status == 415
    assert feedback_bytes(feedback_path) == original_bytes()


def test_jsonp_content_type_post_rejected(server):
    port, feedback_path = server
    status, _ = request(
        port, "POST", "/api/feedback", json.dumps(FORGED_REVIEWS),
        origin=same_origin(port), content_type="application/jsonp",
    )
    assert status == 415
    assert feedback_bytes(feedback_path) == original_bytes()


def test_form_urlencoded_post_rejected(server):
    port, feedback_path = server
    status, _ = request(
        port, "POST", "/api/feedback", json.dumps(FORGED_REVIEWS),
        origin=same_origin(port),
        content_type="application/x-www-form-urlencoded",
    )
    assert status == 415
    assert feedback_bytes(feedback_path) == original_bytes()


def test_foreign_referer_without_origin_rejected(server):
    port, feedback_path = server
    status, _ = request(
        port, "POST", "/api/feedback", json.dumps(FORGED_REVIEWS),
        referer="http://evil.example/", content_type="application/json",
    )
    assert status == 403
    assert feedback_bytes(feedback_path) == original_bytes()


def test_same_origin_referer_without_origin_accepted(server):
    port, feedback_path = server
    status, _ = request(
        port, "POST", "/api/feedback", json.dumps(FORGED_REVIEWS),
        referer=same_origin(port) + "/", content_type="application/json",
    )
    assert status == 200
    assert json.loads(feedback_bytes(feedback_path)) == FORGED_REVIEWS


def test_foreign_host_post_rejected(server):
    port, feedback_path = server
    status, _ = request(
        port, "POST", "/api/feedback", json.dumps(FORGED_REVIEWS),
        origin=same_origin(port), content_type="application/json",
        host="evil.example",
    )
    assert status == 403
    assert feedback_bytes(feedback_path) == original_bytes()


def test_wrong_port_host_post_rejected(server):
    port, feedback_path = server
    status, _ = request(
        port, "POST", "/api/feedback", json.dumps(FORGED_REVIEWS),
        origin=same_origin(port), content_type="application/json",
        host=f"127.0.0.1:{port + 1}",
    )
    assert status == 403
    assert feedback_bytes(feedback_path) == original_bytes()


def test_missing_host_post_rejected(server):
    port, feedback_path = server
    status, _ = request(
        port, "POST", "/api/feedback", json.dumps(FORGED_REVIEWS),
        origin=same_origin(port), content_type="application/json",
        skip_host=True,
    )
    assert status == 400
    assert feedback_bytes(feedback_path) == original_bytes()


# --- POST: existing validation still behaves the same ------------------------

def test_malformed_json_post_rejected_without_write(server):
    port, feedback_path = server
    status, _ = request(
        port, "POST", "/api/feedback", "{not json",
        origin=same_origin(port), content_type="application/json",
    )
    assert status == 500  # pre-existing behaviour, unchanged by this fix
    assert feedback_bytes(feedback_path) == original_bytes()


def test_json_without_reviews_key_rejected_without_write(server):
    port, feedback_path = server
    status, _ = request(
        port, "POST", "/api/feedback", json.dumps({"nope": True}),
        origin=same_origin(port), content_type="application/json",
    )
    assert status == 500  # pre-existing behaviour, unchanged by this fix
    assert feedback_bytes(feedback_path) == original_bytes()


# --- GET: DNS rebinding via Host ---------------------------------------------

def test_get_feedback_same_origin_returns_data(server):
    port, _ = server
    status, body = request(port, "GET", "/api/feedback")
    assert status == 200
    assert json.loads(body) == ORIGINAL_REVIEWS


def test_get_feedback_foreign_host_rejected(server):
    port, _ = server
    status, body = request(port, "GET", "/api/feedback", host="evil.example")
    assert status == 403
    assert b"original-review" not in body


def test_get_feedback_wrong_port_host_rejected(server):
    port, _ = server
    status, body = request(
        port, "GET", "/api/feedback", host=f"127.0.0.1:{port + 1}",
    )
    assert status == 403
    assert b"original-review" not in body


def test_get_root_same_origin_returns_viewer(server):
    port, _ = server
    status, body = request(port, "GET", "/")
    assert status == 200
    assert b"EMBEDDED_DATA" in body or b"html" in body.lower()


def test_get_root_foreign_host_rejected(server):
    port, _ = server
    status, _ = request(port, "GET", "/", host="evil.example")
    assert status == 403


def test_get_index_foreign_host_rejected(server):
    port, _ = server
    status, _ = request(port, "GET", "/index.html", host="evil.example")
    assert status == 403
