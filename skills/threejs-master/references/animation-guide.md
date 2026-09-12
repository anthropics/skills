# Animation Guide

Patterns for GLTF character animation: crossfading, safe selection, facing direction, and squash & stretch.

---

## Finding and Playing Animations

```javascript
// After loading GLTF
const mixer = new THREE.AnimationMixer(model);
const animations = gltf.animations;

// Find animation by name (partial match)
function findAnimation(name) {
    return animations.find(clip =>
        clip.name.toLowerCase().includes(name.toLowerCase())
    );
}

// Play an animation
function playAnimation(name, { loop = true, timeScale = 1 } = {}) {
    const clip = findAnimation(name);
    if (!clip) return null;

    const action = mixer.clipAction(clip);
    action.reset();
    action.setLoop(loop ? THREE.LoopRepeat : THREE.LoopOnce);
    action.clampWhenFinished = !loop; // Hold last frame if not looping
    action.timeScale = timeScale;
    action.play();

    return action;
}

// Usage
playAnimation('run');                          // Loop running
playAnimation('jump', { loop: false, timeScale: 2 }); // One-shot, fast
playAnimation('death', { loop: false });       // One-shot, hold last frame
```

---

## Crossfading Between Animations (WITH GUARD)

**CRITICAL**: The guard `if (currentAction === newAction)` prevents frame freezing when `switchAnimation` is called every frame (common in game loops).

```javascript
let currentAction = null;

function switchAnimation(name, { fadeTime = 0.1, ...options } = {}) {
    const clip = findAnimation(name);
    if (!clip) return;

    const newAction = mixer.clipAction(clip);

    // CRITICAL: Check if this action is already playing
    // Calling reset() on an already-playing action causes frame freezing!
    if (currentAction === newAction) {
        if (!newAction.isRunning()) {
            newAction.play();
        }
        return; // Don't reset or fade - it's already running
    }

    newAction.reset();
    newAction.setLoop(options.loop !== false ? THREE.LoopRepeat : THREE.LoopOnce);
    newAction.clampWhenFinished = !options.loop;
    newAction.timeScale = options.timeScale || 1;
    newAction.enabled = true;
    newAction.paused = false;

    if (currentAction) {
        currentAction.fadeOut(fadeTime);
    }

    newAction.fadeIn(fadeTime).play();
    currentAction = newAction;
}

// Usage in game loop - safe to call every frame
function updateEntity(entity, dt) {
    if (entity.isMoving) {
        switchAnimation('run'); // Won't reset if already running
    } else {
        switchAnimation('idle');
    }
}
```

---

## Animation Selection Pitfalls (CRITICAL)

GLTF models may have multiple animations. **Incorrect selection causes:**
- Sheep playing death animations instead of idle
- Wolves frozen (no animation match found)
- Characters stuck in T-pose

### Safe Animation Selection

```javascript
// WRONG - First animation might be death!
const action = mixer.clipAction(animations[0]);
action.play();

// WRONG - Partial match might grab wrong animation
const clip = animations.find(a => a.name.includes('idle'));
// "Death_Idle" matches "idle"!

// CORRECT - Explicit filtering with priority order
function selectSafeAnimation(animations, preferredTypes = ['idle', 'eat', 'graze']) {
    // First: filter OUT dangerous animations
    const safeAnims = animations.filter(a => {
        const name = a.name.toLowerCase();
        return !name.includes('death') &&
               !name.includes('die') &&
               !name.includes('dead');
    });

    // Second: find preferred animation from safe list
    for (const type of preferredTypes) {
        const match = safeAnims.find(a =>
            a.name.toLowerCase().includes(type)
        );
        if (match) return match;
    }

    // Third: use first safe animation
    if (safeAnims.length > 0) return safeAnims[0];

    // Last resort: use first animation with warning
    console.warn('No safe animation found, using:', animations[0]?.name);
    return animations[0];
}

// Usage for ambient entities (sheep, birds, etc.)
const clip = selectSafeAnimation(gltf.animations, ['idle', 'eat', 'graze', 'walk']);
mixer.clipAction(clip).play();
```

### Animation Matching for Game Entities

```javascript
function setEntityAnimation(entity, desiredName, options = {}) {
    const { loop = true, timeScale = 1 } = options;

    // Log available animations on first call (debugging)
    if (!entity._animsLogged) {
        console.log(`[${entity.type}] Available animations:`,
            Object.keys(entity.animations).join(', '));
        entity._animsLogged = true;
    }

    // Try exact match first
    let action = entity.animations[desiredName.toLowerCase()];

    // Try partial match
    if (!action) {
        const key = Object.keys(entity.animations).find(k =>
            k.toLowerCase().includes(desiredName.toLowerCase())
        );
        if (key) action = entity.animations[key];
    }

    // Try common alternatives
    if (!action) {
        const alternatives = {
            'run': ['walk', 'gallop', 'trot', 'move'],
            'attack': ['bite', 'punch', 'hit', 'strike'],
            'death': ['die', 'dead', 'defeat'],
            'idle': ['stand', 'breathe', 'wait']
        };

        const alts = alternatives[desiredName.toLowerCase()] || [];
        for (const alt of alts) {
            const key = Object.keys(entity.animations).find(k =>
                k.toLowerCase().includes(alt)
            );
            if (key) {
                action = entity.animations[key];
                break;
            }
        }
    }

    // Last resort: first non-death animation
    if (!action) {
        const safeKey = Object.keys(entity.animations).find(k => {
            const lower = k.toLowerCase();
            return !lower.includes('death') && !lower.includes('die');
        });
        if (safeKey) action = entity.animations[safeKey];
    }

    if (!action) {
        console.warn(`[${entity.type}] No animation found for: ${desiredName}`);
        return;
    }

    // Prevent redundant resets (causes freezing)
    if (entity.currentAction === action) {
        if (!action.isRunning()) action.play();
        return;
    }

    console.log(`[${entity.type}] Playing: ${action.getClip().name}`);

    if (entity.currentAction) {
        entity.currentAction.fadeOut(0.15);
    }

    action.reset();
    action.setLoop(loop ? THREE.LoopRepeat : THREE.LoopOnce, loop ? Infinity : 1);
    action.clampWhenFinished = !loop;
    action.timeScale = timeScale;
    action.enabled = true;
    action.paused = false;
    action.fadeIn(0.15);
    action.play();

    entity.currentAction = action;
}
```

---

## Facing Direction for Side-Scrollers

GLTF models typically face -Z (into the screen). For side-scrollers:

```javascript
function normalizeModel(model, targetHeight, faceDirection = 'right') {
    // ... scaling logic ...

    // Rotate to face correct direction
    // GLTF default: faces -Z
    // To face +X (right): rotate +90 around Y
    // To face -X (left): rotate -90 around Y

    if (faceDirection === 'right') {
        model.rotation.y = Math.PI / 2;  // Face +X
    } else if (faceDirection === 'left') {
        model.rotation.y = -Math.PI / 2; // Face -X
    }
    // 'none' or default: keep original facing

    return model;
}

// Usage
normalizeModel(playerModel, 2, 'right');  // Player runs right
normalizeModel(enemyModel, 2, 'left');    // Enemy approaches from right
```

---

## Squash & Stretch

For jump anticipation and landing impact:

```javascript
function setModelScale(model, sx, sy, sz) {
    model.scale.set(sx, sy, sz);
}

// Jump anticipation
function jumpAnticipation(model) {
    setModelScale(model, 1.15, 0.8, 1.15);  // Squash

    setTimeout(() => {
        setModelScale(model, 1, 1, 1);       // Restore
    }, 80);
}

// Landing impact
function landingSquash(model) {
    setModelScale(model, 1.2, 0.75, 1.2);   // Heavy squash

    setTimeout(() => {
        setModelScale(model, 0.95, 1.1, 0.95); // Overshoot
    }, 60);

    setTimeout(() => {
        setModelScale(model, 1, 1, 1);        // Settle
    }, 150);
}
```

---

## Best Practices

| Pattern | When to Use |
|---------|-------------|
| `switchAnimation` with guard | Any crossfade called in game loop |
| `selectSafeAnimation` | Ambient entities (animals, NPCs) |
| `setEntityAnimation` | Player/enemy with many animation states |
| Facing direction | Side-scrollers with GLTF models |
| Squash & stretch | Jump, land, any snappy motion |
