# Reference Frame Contract (Three.js) -- Calibration & Guardrails

Most production bugs in Three.js scenes are **reference-frame bugs**, not rendering bugs. If you lock a "contract" up front, you avoid weeks of symptom-chasing (floating models, inverted axes, broken animations, weird colors, hung state transitions).

## 1) The Contract (write these down for the project)

### Axes
- World axes: +X right, +Y up, +Z ??? (your gameplay forward)
- Camera conventions: do you treat camera forward as "player forward"?
- Per-asset forward: does this asset pack face `-Z`, `+Z`, or something else?
  - Result: a single `MODEL_FORWARD_OFFSET` (radians) or a per-asset override.

### Anchors ("what is ground?")
Define how each asset class is anchored relative to y=0:
- Characters: bottom at y=0 (`minY = 0`)
- Props: bottom at y=0 (`minY = 0`)
- Ground tiles/blocks: walkable top at y=0 (`maxY = 0`) is often the right choice

### Units / Scale
- What is 1 unit? (meters-ish, tile-sized, etc.)
- Define target heights in world units:
  - `HERO_HEIGHT`, `CHICK_HEIGHT`, etc.

### Color / Output
- Set and keep consistent:
  - `renderer.outputColorSpace = THREE.SRGBColorSpace`
- If you use atlas-textured GLTFs:
  - Keep `material.color` near white (tinting by multiplication often corrupts the look).

### Loading Environment
- GLTF must be served over HTTP (avoid `file://`), or loaders may fail silently / behave differently.

### State Transitions
- One state machine, one transition function, one-way latches for terminal events (`hasEnded`).

### UI Scaling
- Center via layout (flex/grid) and apply `scale()` only.
- Avoid mixing `translate()` + `scale()` unless you're very deliberate about `transform-origin`.

## 2) 60-Second Calibration Pass (do this before gameplay)

1) Add helpers:
   - `scene.add(new THREE.AxesHelper(2))`
   - `scene.add(new THREE.GridHelper(10, 10))`
   - Add a known ground datum at y=0 (plane or your ground tile)
2) Load one GLTF per class: character, chick, ground tile, a prop.
3) Visualize bounds + pivot:
   - `obj.add(new THREE.AxesHelper(0.5))`
   - `scene.add(new THREE.Box3Helper(new THREE.Box3().setFromObject(obj), 0xff00ff))`
4) Print animation clip names:
   - `console.log(gltf.animations.map(a => a.name))`
5) Confirm output color space:
   - `renderer.outputColorSpace = THREE.SRGBColorSpace`
6) Decide constants:
   - `MODEL_FORWARD_OFFSET` (and/or per-asset overrides)
   - Anchor mode per asset type (`minY` vs `maxY`)

### Forward Direction Check (Mesh Forward)
You want a deterministic answer to: "Which way is *forward* for this mesh?"

Three.js convention:
- An `Object3D`'s forward direction is its **local `-Z` axis**.

In the calibration scene, attach an arrow to the model root so you can see forward at a glance:

```js
const modelRoot = instanceRoot;

modelRoot.add(new THREE.AxesHelper(0.6));

// Visualize local forward (-Z) as a magenta arrow.
const localForward = new THREE.Vector3(0, 0, -1);
const arrow = new THREE.ArrowHelper(localForward, new THREE.Vector3(0, 1.2, 0), 1.2, 0xff00ff);
modelRoot.add(arrow);

// Log world-forward (the object's -Z axis in world coordinates).
const worldForward = new THREE.Vector3();
modelRoot.getWorldDirection(worldForward);
console.log('model world forward (-Z):', worldForward.toArray());
```

Lock the result as a constant:
- Prefer `yawOffset` per asset class (hero vs enemies), or one `MODEL_YAW_OFFSET` if the whole pack is consistent.
- Keep this separate from gameplay heading (don't "fix" movement vectors to compensate for wrong mesh forward).

## 3) Anchoring Pattern (stop "offset roulette")

Normalize imported scenes once, into an anchor wrapper. Then position the wrapper in world space.

```js
function normalizeToAnchor(root, { targetHeight, anchor = 'minY' }) {
  const box = new THREE.Box3().setFromObject(root);
  const size = box.getSize(new THREE.Vector3());
  if (size.y > 0) root.scale.setScalar(targetHeight / size.y);
  root.updateMatrixWorld(true);

  const box2 = new THREE.Box3().setFromObject(root);
  const y = anchor === 'maxY' ? -box2.max.y : -box2.min.y;
  root.position.y += y;
  root.updateMatrixWorld(true);
}
```

Rules:
- Use **one anchor rule per asset class**.
- Don't compensate by moving the entire world group or by mixing "surfaceY" computations with per-entity offsets.

## 4) Camera-Relative Movement Basis (avoid inverted WASD)

```js
const up = new THREE.Vector3(0, 1, 0);
const forward = new THREE.Vector3();
camera.getWorldDirection(forward);
forward.y = 0;
forward.normalize();

// Right-handed: right = forward x up
const right = new THREE.Vector3().crossVectors(forward, up).normalize();
```

If left/right is inverted:
- Check the cross product order first.
- If your camera points "backward" relative to gameplay forward, you may need `forward.negate()` -- fix the convention, not the key mapping.

## 5) GLTF Loading & Animation Reliability

### Animated instancing
If a model has bones/skin, use:
- `SkeletonUtils.clone(gltf.scene)` for instances
- `new THREE.AnimationMixer(instanceRoot)` per instance

### Clip selection
- Select clips by exact name (log them).
- Only use substring/heuristic matching as an explicit fallback strategy.

### Atlas tinting
If your pack uses atlas textures:
- Avoid `material.color.multiply(...)` tinting (can turn everything into flat tinted planes).
- Prefer emissive, lighting, or a carefully chosen single `material.color.setHex(...)` if the pack expects it.

## 6) Timeout "Hang" Guardrail

Symptoms: timer hits ~0.8s/0.0s and the game appears stuck.

Common causes:
- Multiple systems trigger end state (timer, slowmo, submit) without a latch.
- `timeLeft` goes negative and your UI/logic path assumes `> 0`.

Fix pattern:
- `timeLeft = Math.max(0, timeLeft - dt)`
- One-way `hasEnded` latch:
  - if `hasEnded` return early from timer/update
  - end transition sets `hasEnded = true` and runs exactly once

## 7) Quick Troubleshooting Map

- **Model floats / sinks** -- anchor contract missing (minY vs maxY mismatch) or offsets in too many places.
- **Forward/back inverted** -- asset pack forward differs; set `MODEL_FORWARD_OFFSET` after calibration.
- **Left/right inverted** -- wrong basis (`cross` order) or inconsistent forward convention.
- **Red/flat planes** -- color space not set OR atlas materials tinted incorrectly OR load failed and fallback geometry is showing.
- **Canvas not centered** -- transform-origin/translate+scale drift; center via layout and scale only.
