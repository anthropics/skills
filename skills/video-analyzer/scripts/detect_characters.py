#!/usr/bin/env python3
"""
detect_characters.py — Visual character clustering for the video-analyzer skill.

Usage:
    python3 detect_characters.py --frames-dir /tmp/video_work/frames \
                                  --output /tmp/video_work/characters.json \
                                  --manifest /tmp/video_work/manifest.json

Strategy:
  1. For each frame: extract dominant color regions from the top-half (character area)
  2. Build a color histogram fingerprint per frame
  3. Cluster frames by histogram similarity → each cluster = one recurring "character slot"
  4. Pick the most representative frame per cluster
  5. Output a characters.json with: count, clusters, representative_frame paths
"""

import argparse
import json
import os
import sys

import cv2
import numpy as np

parser = argparse.ArgumentParser()
parser.add_argument("--frames-dir", required=True)
parser.add_argument("--output", required=True)
parser.add_argument("--manifest", required=True)
parser.add_argument("--similarity-threshold", type=float, default=0.72,
                    help="Histogram correlation threshold (0-1). Higher = stricter.")
args = parser.parse_args()

# ── Load manifest ─────────────────────────────────────────────────────────────
with open(args.manifest) as f:
    manifest = json.load(f)

frame_paths = [e["path"] for e in manifest if os.path.exists(e["path"])]
if not frame_paths:
    print("No frames found.", file=sys.stderr)
    sys.exit(1)

# ── Compute HSV histogram fingerprint per frame ───────────────────────────────
def frame_fingerprint(path):
    img = cv2.imread(path)
    if img is None:
        return None
    h, w = img.shape[:2]
    # Focus on center 60% of image width, top 70% of height (character body area)
    roi = img[0:int(h * 0.70), int(w * 0.20):int(w * 0.80)]
    hsv = cv2.cvtColor(roi, cv2.COLOR_BGR2HSV)
    # 3-channel histogram: H(18 bins), S(8 bins), V(8 bins)
    hist = cv2.calcHist([hsv], [0, 1, 2], None, [18, 8, 8],
                        [0, 180, 0, 256, 0, 256])
    cv2.normalize(hist, hist)
    return hist.flatten()

print("Computing frame fingerprints…", flush=True)
fingerprints = {}
for p in frame_paths:
    fp = frame_fingerprint(p)
    if fp is not None:
        fingerprints[p] = fp

# ── Greedy clustering by histogram correlation ────────────────────────────────
clusters = []  # list of {representative, members: [paths], timestamps: [...]}

manifest_by_path = {e["path"]: e for e in manifest}

def hist_corr(a, b):
    # Reshape back to 3D for compareHist
    h1 = a.reshape(18, 8, 8).astype(np.float32)
    h2 = b.reshape(18, 8, 8).astype(np.float32)
    return cv2.compareHist(h1, h2, cv2.HISTCMP_CORREL)

print("Clustering frames into character groups…", flush=True)
threshold = args.similarity_threshold

for path in frame_paths:
    if path not in fingerprints:
        continue
    fp = fingerprints[path]
    matched = False
    for cluster in clusters:
        rep_fp = fingerprints[cluster["representative"]]
        score = hist_corr(fp, rep_fp)
        if score >= threshold:
            cluster["members"].append(path)
            cluster["timestamps"].append(
                manifest_by_path.get(path, {}).get("timestamp_formatted", "?"))
            matched = True
            break
    if not matched:
        clusters.append({
            "character_id": len(clusters) + 1,
            "representative": path,
            "representative_timestamp": manifest_by_path.get(path, {}).get("timestamp_formatted", "?"),
            "members": [path],
            "timestamps": [manifest_by_path.get(path, {}).get("timestamp_formatted", "?")],
        })

# Sort clusters by number of appearances (most frequent first)
clusters.sort(key=lambda c: len(c["members"]), reverse=True)
for i, c in enumerate(clusters):
    c["character_id"] = i + 1

# ── Output ────────────────────────────────────────────────────────────────────
result = {
    "character_count_detected": len(clusters),
    "characters": [
        {
            "character_id": c["character_id"],
            "appearances": len(c["members"]),
            "first_seen": c["timestamps"][0] if c["timestamps"] else "?",
            "last_seen": c["timestamps"][-1] if c["timestamps"] else "?",
            "representative_frame": c["representative"],
            "representative_timestamp": c["representative_timestamp"],
            "all_timestamps": c["timestamps"],
        }
        for c in clusters
    ]
}

with open(args.output, "w") as f:
    json.dump(result, f, indent=2)

print(f"\n✅ Detected {len(clusters)} distinct visual character(s).", flush=True)
for c in clusters:
    print(f"   Character {c['character_id']}: {len(c['members'])} frames "
          f"(first: {c['timestamps'][0] if c['timestamps'] else '?'})", flush=True)
