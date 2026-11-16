#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Xiaozhi AI (xzai.me) media CLI — video / image / tts / chat / models / status.

Dependency-free (stdlib only). Auth: XIAOZHI_API_KEY env var.
api.php endpoints use the `x-token` header; /v1/* endpoints use Bearer.
"""
import argparse
import json
import os
import sys
import time
import urllib.error
import urllib.request

BASE = os.environ.get("XIAOZHI_BASE_URL", "https://xzai.me").rstrip("/")
KEY = os.environ.get("XIAOZHI_API_KEY", "")

VIDEO_MODELS = {
    None: 10,                        # default = Seedance 2.0 Fast 10s
    "seedance-2.0-fast-15": 15,
    "seedance-2.0-mini": 15,
    "seedance-2.5": 30,
}
VIDEO_RATIOS = {"16:9", "9:16", "1:1", "3:4", "4:3"}
WIDE_RATIOS = VIDEO_RATIOS | {"21:9"}  # 2.5 / fast-15 also support 21:9
IMAGE_RATIOS = {"1:1", "16:9", "9:16", "3:4", "4:3", "2:3", "3:2"}
TTS_VOICES = {"Cherry", "Ethan", "Chelsie", "Nofish", "Jennifer", "Ryan", "Katerina"}


def die(msg, code=2):
    print("ERROR:", msg, file=sys.stderr)
    sys.exit(code)


def need_key():
    if not KEY:
        die(
            "XIAOZHI_API_KEY is not set. Setup (about 2 minutes):\n"
            "  1. Open https://xzai.me and register / log in\n"
            "  2. 个人中心 (avatar) -> API 接口\n"
            "  3. Copy your API key\n"
            "  4. Send it back to the agent, e.g. \"my key is xxx\"\n"
            "     The agent will save it for you, e.g.:\n"
            "       export XIAOZHI_API_KEY=\"your-key\"      # Linux / macOS\n"
            "       setx XIAOZHI_API_KEY \"your-key\"        # Windows (new terminals)\n"
            "Then re-run this command."
        )
    return KEY


def http_json(path, payload=None, bearer=False, timeout=60):
    url = path if path.startswith("http") else BASE + path
    if bearer:
        headers = {"Content-Type": "application/json",
                   "Authorization": "Bearer " + need_key()}
    else:
        headers = {"Content-Type": "application/json", "x-token": need_key()}
    data = json.dumps(payload or {}).encode()
    req = urllib.request.Request(url, data=data, headers=headers)
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return json.loads(r.read().decode())
    except urllib.error.HTTPError as e:
        body = e.read().decode(errors="replace")
        die("HTTP %s from %s\n%s" % (e.code, url, body[:500]))


def download(url, out):
    req = urllib.request.Request(url, headers={"User-Agent": "xiaozhi-skill/1.0"})
    with urllib.request.urlopen(req, timeout=300) as r, open(out, "wb") as f:
        f.write(r.read())
    return os.path.getsize(out)


def poll(path, field, task_id, out, interval=20, max_wait=1800, kind="task"):
    """Poll a getResult endpoint until done; download the artifact."""
    deadline = time.time() + max_wait
    while True:
        r = http_json(path, {field: task_id})
        d = r.get("data") or {}
        state = d.get("state")
        if state == 1:
            url = d.get("video_url") or (d.get("images") or [None])[0]
            if not url:
                die("Task %s finished but no artifact URL in response: %s" % (task_id, r))
            n = download(url, out)
            print("saved %s (%d bytes) -> %s" % (kind, n, out))
            if kind == "image":
                print("url:", url)
            else:
                print("url:", url, "(expires; local copy is the durable one)")
            return
        if state == 2:
            die("Task %s FAILED (credits auto-refunded)." % task_id)
        if state == -1:
            die("Task %s not found." % task_id)
        if time.time() > deadline:
            print("PENDING: still generating after %ss. Poll later with:" % max_wait)
            print("  python %s status %s" % (sys.argv[0], task_id))
            print("  (then download manually from the returned url)")
            sys.exit(3)
        print("state=0 generating... (%ds elapsed)" % int(time.time() - (deadline - max_wait)))
        time.sleep(interval)


def cmd_video(args):
    model = args.model
    if model not in VIDEO_MODELS:
        die("model must be one of: %s (got %r). Wrong names silently fall back to fast-10s upstream." %
            (", ".join(filter(None, VIDEO_MODELS)), model))
    need_dur = VIDEO_MODELS[model]
    if args.duration and args.duration != need_dur:
        die("model %s only supports duration=%d (got %d)" % (model, need_dur, args.duration))
    ratio = args.ratio
    if ratio not in (WIDE_RATIOS if (model in ("seedance-2.5", "seedance-2.0-fast-15")) else VIDEO_RATIOS):
        die("ratio %s not supported for model %s" % (ratio, model))
    payload = {"prompt": args.prompt, "platform": "seedance", "aspect_ratio": ratio}
    if model:
        payload["model"] = model
    if model == "seedance-2.0-mini":
        payload["duration"] = 15  # REQUIRED for mini, silently ignored otherwise
    if args.images:
        payload["images"] = args.images[:10]
    r = http_json("/api.php/video/submit", payload)
    vid = (r.get("data") or {}).get("video_id")
    if not vid:
        die("submit failed: %s" % r)
    print("submitted video_id=%s model=%s duration=%ds ratio=%s" %
          (vid, model or "fast(10s)", need_dur, ratio))
    poll("/api.php/video/getResult", "video_id", vid, args.out, kind="video",
         max_wait=40 * 60 if model in ("seedance-2.0-fast-15", "seedance-2.0-mini") else 15 * 60)


def cmd_image(args):
    if args.ratio not in IMAGE_RATIOS:
        die("ratio must be one of %s" % sorted(IMAGE_RATIOS))
    payload = {"message": args.prompt, "aspect_ratio": args.ratio, "is_share": 0}
    if args.style:
        payload["style_key"] = args.style
    if args.images:
        payload["images"] = args.images[:10]
    r = http_json("/api.php/draw_seedream/seedreamSubmit", payload)
    did = (r.get("data") or {}).get("draw_id")
    if not did:
        die("submit failed: %s" % r)
    print("submitted draw_id=%s ratio=%s" % (did, args.ratio))
    poll("/api.php/draw_seedream/getResult", "draw_id", did, args.out,
         kind="image", interval=8, max_wait=5 * 60)


def cmd_tts(args):
    text = args.text
    if not (1 <= len(text) <= 500):
        die("TTS accepts 1-500 characters per call (got %d). Split longer text." % len(text))
    voice = args.voice
    if voice not in TTS_VOICES:
        die("voice must be one of %s" % sorted(TTS_VOICES))
    r = http_json("/api.php/tts/text2audio", {"text": text, "voice": voice})
    d = r.get("data") or {}
    url = d.get("audio_url")
    if not url:
        die("tts failed: %s" % r)
    n = download(url, args.out)
    print("saved audio (%d bytes) -> %s (price=%s credits, chars=%s)" %
          (n, args.out, d.get("price"), d.get("characters")))
    print("NOTE: remote url expires in ~24h; local copy saved.")


def cmd_chat(args):
    messages = [{"role": "user", "content": args.prompt}]
    r = http_json("/v1/chat/completions", {"model": args.model, "messages": messages}, bearer=True, timeout=300)
    try:
        print(r["choices"][0]["message"]["content"] or
              "(empty content — see reasoning_content; usage=%s)" % r.get("usage"))
    except (KeyError, IndexError):
        die("unexpected response: %s" % json.dumps(r)[:500])


def cmd_models(_):
    req = urllib.request.Request(BASE + "/v1/models", headers={"Authorization": "Bearer " + need_key()})
    with urllib.request.urlopen(req, timeout=30) as r:
        d = json.loads(r.read().decode())
    for m in d.get("data", []):
        print(m.get("id"))


def cmd_status(args):
    r = http_json("/api.php/video/getResult", {"video_id": int(args.task_id)})
    print(json.dumps(r, ensure_ascii=False, indent=2))


def main():
    p = argparse.ArgumentParser(description="Xiaozhi AI media CLI")
    sub = p.add_subparsers(dest="cmd", required=True)

    v = sub.add_parser("video", help="generate a video (Seedance)")
    v.add_argument("prompt")
    v.add_argument("--model", default=None, help="omit=fast10s | seedance-2.0-fast-15 | seedance-2.0-mini | seedance-2.5")
    v.add_argument("--ratio", default="16:9")
    v.add_argument("--duration", type=int, default=None)
    v.add_argument("--images", nargs="*", help="reference image URLs (max 10)")
    v.add_argument("--out", default="output.mp4")
    v.set_defaults(fn=cmd_video)

    i = sub.add_parser("image", help="generate an image (Seedream)")
    i.add_argument("prompt")
    i.add_argument("--ratio", default="1:1")
    i.add_argument("--style", default=None)
    i.add_argument("--images", nargs="*", help="reference image URLs (max 10)")
    i.add_argument("--out", default="output.jpg")
    i.set_defaults(fn=cmd_image)

    t = sub.add_parser("tts", help="text to speech")
    t.add_argument("text")
    t.add_argument("--voice", default="Cherry")
    t.add_argument("--out", default="output.wav")
    t.set_defaults(fn=cmd_tts)

    c = sub.add_parser("chat", help="OpenAI-compatible chat")
    c.add_argument("prompt")
    c.add_argument("--model", default="glm-5.3-flash")
    c.set_defaults(fn=cmd_chat)

    m = sub.add_parser("models", help="list models")
    m.set_defaults(fn=cmd_models)

    s = sub.add_parser("status", help="check video task status")
    s.add_argument("task_id")
    s.set_defaults(fn=cmd_status)

    args = p.parse_args()
    args.fn(args)


if __name__ == "__main__":
    main()
