# Game Loop & State Management

Patterns for game loops, state machines, time scaling, and screen effects in Three.js games.

---

## Game Loop with State Machine

```javascript
const GameState = {
    LOADING: 'loading',
    MENU: 'menu',
    PLAYING: 'playing',
    PAUSED: 'paused',
    GAME_OVER: 'gameover'
};

const state = {
    current: GameState.LOADING,
    timeScale: 1.0,  // For slow-mo effects
    score: 0
};

const clock = new THREE.Clock();
const mixers = []; // All animation mixers

function gameLoop() {
    const dt = Math.min(clock.getDelta(), 0.1); // Cap delta for tab-away
    const scaledDt = dt * state.timeScale;

    // Always update animations (even in menu for idle anims)
    for (const mixer of mixers) {
        mixer.update(scaledDt);
    }

    switch (state.current) {
        case GameState.PLAYING:
            updatePlayer(scaledDt);
            updateObstacles(scaledDt);
            updateBackground(scaledDt);
            checkCollisions();
            updateScore(dt); // Real time, not scaled
            break;

        case GameState.PAUSED:
            // Render but don't update physics
            break;

        case GameState.MENU:
            // Light background animation
            updateBackground(dt * 0.3);
            break;
    }

    updateScreenEffects(dt);
    renderer.render(scene, camera);
}

renderer.setAnimationLoop(gameLoop);
```

**Key decisions**:
- `Math.min(clock.getDelta(), 0.1)` caps delta to prevent physics explosions after tab-away
- `scaledDt` for game logic, raw `dt` for real-time things (score, timers)
- Animations update in ALL states (menu idle animations still play)

---

## Time Scaling (Slow Motion)

```javascript
// Instant slow-mo
function triggerSlowMo(factor, duration) {
    state.timeScale = factor;

    setTimeout(() => {
        state.timeScale = 1.0;
    }, duration * 1000);
}

// Usage
triggerSlowMo(0.3, 0.2);  // 30% speed for 0.2 seconds

// Gradual return to normal (feels cinematic)
function triggerSlowMoSmooth(factor, holdTime, rampTime) {
    state.timeScale = factor;

    setTimeout(() => {
        const startTime = performance.now();
        const rampMs = rampTime * 1000;

        function ramp() {
            const elapsed = performance.now() - startTime;
            const t = Math.min(elapsed / rampMs, 1);
            state.timeScale = factor + (1 - factor) * t;

            if (t < 1) requestAnimationFrame(ramp);
        }
        ramp();
    }, holdTime * 1000);
}

// Usage: 0.15x for 0.2s, then ramp to 1x over 0.12s
triggerSlowMoSmooth(0.15, 0.2, 0.12);
```

---

## Screen Effects

### Camera Shake

```javascript
const cameraBasePos = { x: 2, y: 5, z: 16 };
let shakeIntensity = 0;
let shakeDuration = 0;

function shakeScreen(intensity, duration) {
    shakeIntensity = intensity;
    shakeDuration = duration;
}

function updateShake(dt) {
    if (shakeDuration > 0) {
        shakeDuration -= dt;
        const decay = shakeDuration / 0.3; // Assume 0.3s base duration
        const offset = shakeIntensity * decay;

        camera.position.x = cameraBasePos.x + (Math.random() - 0.5) * offset;
        camera.position.y = cameraBasePos.y + (Math.random() - 0.5) * offset;
    } else {
        camera.position.x = cameraBasePos.x;
        camera.position.y = cameraBasePos.y;
    }
}

// Usage
shakeScreen(0.5, 0.35); // Intensity 0.5 units, 0.35 seconds
```

### Screen Flash

```html
<div id="flash-overlay" style="
    position: absolute;
    top: 0; left: 0;
    width: 100%; height: 100%;
    pointer-events: none;
    opacity: 0;
    transition: opacity 0.08s;
"></div>
```

```javascript
function flashScreen(color, duration) {
    const overlay = document.getElementById('flash-overlay');
    overlay.style.backgroundColor = color;
    overlay.style.opacity = 0.3;

    setTimeout(() => {
        overlay.style.opacity = 0;
    }, duration * 1000);
}

// Usage
flashScreen('#4DEBFF', 0.15);  // Cyan flash for near-miss
flashScreen('#ffffff', 0.08);  // White flash for impact
```

### Zoom Pulse

```javascript
let zoomTarget = 1.0;
let zoomCurrent = 1.0;

function zoomPulse(scale, duration) {
    zoomTarget = scale;

    setTimeout(() => {
        zoomTarget = 1.0;
    }, duration * 500); // Half duration for in, half for out
}

function updateZoom(dt) {
    zoomCurrent += (zoomTarget - zoomCurrent) * dt * 10;
    camera.zoom = zoomCurrent;
    camera.updateProjectionMatrix();
}

// Usage
zoomPulse(1.02, 0.2);  // 2% zoom in, 0.2s total
```

### Floating Text Popup

For score popups, combo text, near-miss rewards — any brief feedback that floats up and fades out.
The CSS animation handles movement and opacity so JS only creates and removes the element.

```html
<style>
.floating-text {
    position: absolute;
    font-weight: bold;
    pointer-events: none;
    animation: floatUp 0.6s ease-out forwards;
}
@keyframes floatUp {
    0%   { opacity: 1; transform: translateY(0) scale(1); }
    100% { opacity: 0; transform: translateY(-40px) scale(1.2); }
}
</style>
```

```javascript
function showFloatingText(text, color, x = '50%', y = '35%') {
    const popup = document.createElement('div');
    popup.className = 'floating-text';
    popup.textContent = text;
    popup.style.color = color;
    popup.style.left = x;
    popup.style.top = y;
    popup.style.transform = 'translateX(-50%)';
    popup.style.fontSize = '1.4rem';
    popup.style.textShadow = `0 0 10px ${color}`;

    document.getElementById('ui').appendChild(popup);

    // Remove after animation completes to avoid DOM buildup
    setTimeout(() => popup.remove(), 600);
}

// Usage
showFloatingText('+15', '#4DEBFF');              // Score popup (cyan)
showFloatingText('CLOSE!', '#4DEBFF');           // Near-miss reward
showFloatingText('COMBO x3', '#FFD700', '50%', '25%'); // Combo at top
```

**Requires** a UI container in your HTML: `<div id="ui" style="position: absolute; inset: 0; pointer-events: none;"></div>`

---

## Parallax Background Layers

Different scroll speeds create depth:

```javascript
const PARALLAX = {
    clouds: 0.1,     // Very slow
    farTrees: 0.3,   // Slow
    nearTrees: 0.5,  // Medium
    crowd: 0.7,      // Faster
    ground: 1.0      // Base speed
};

const layers = {
    clouds: [],
    farTrees: [],
    nearTrees: [],
    crowd: []
};

function updateParallax(dt, baseSpeed) {
    for (const [layerName, objects] of Object.entries(layers)) {
        const speed = baseSpeed * PARALLAX[layerName] * dt;

        for (const obj of objects) {
            obj.position.x -= speed;

            // Wrap when off-screen
            if (obj.position.x < -30) {
                obj.position.x += 60;
                obj.position.z = -5 - Math.random() * 10;
            }
        }
    }
}
```

---

## Object Pooling

For spawning/despawning obstacles efficiently:

```javascript
class ObjectPool {
    constructor(createFn, initialSize = 10) {
        this.createFn = createFn;
        this.pool = [];
        this.active = [];

        for (let i = 0; i < initialSize; i++) {
            const obj = createFn();
            obj.visible = false;
            this.pool.push(obj);
        }
    }

    spawn(x, y, z) {
        let obj = this.pool.pop();

        if (!obj) {
            obj = this.createFn();
        }

        obj.position.set(x, y, z);
        obj.visible = true;
        this.active.push(obj);

        return obj;
    }

    despawn(obj) {
        obj.visible = false;
        const idx = this.active.indexOf(obj);
        if (idx !== -1) this.active.splice(idx, 1);
        this.pool.push(obj);
    }

    updateAll(callback) {
        // Iterate backwards for safe removal
        for (let i = this.active.length - 1; i >= 0; i--) {
            const shouldDespawn = callback(this.active[i]);
            if (shouldDespawn) {
                this.despawn(this.active[i]);
            }
        }
    }
}

// Usage
const obstaclePool = new ObjectPool(() => createObstacle(), 15);

obstaclePool.spawn(12, 0, 0);

obstaclePool.updateAll((obstacle) => {
    obstacle.position.x -= scrollSpeed * dt;
    return obstacle.position.x < -14; // Return true to despawn
});
```

---

## Fixed Game Camera (Not OrbitControls)

For side-scrollers and fixed-view games:

```javascript
function setupGameCamera() {
    const camera = new THREE.PerspectiveCamera(45, 960/540, 0.1, 100);
    camera.position.set(2, 5, 16);
    camera.lookAt(2, 1, 0);
    return camera;
}

// Cinematic variant
function setupCinematicCamera() {
    const camera = new THREE.PerspectiveCamera(50, 960/540, 0.1, 100);
    camera.position.set(0, 8, 14);
    camera.lookAt(2, 1, 0);
    camera.rotation.z = 0.03; // Slight Dutch angle
    return camera;
}
```

---

## Near-Miss Detection

```javascript
function checkNearMiss(player, obstacle, threshold = 0.8) {
    if (obstacle.position.x > player.position.x) return false;
    if (obstacle.passed) return false;

    obstacle.passed = true;

    const verticalGap = player.position.y - obstacle.height;

    if (verticalGap > 0 && verticalGap < threshold) {
        triggerNearMissReward();
        return true;
    }

    return false;
}

function triggerNearMissReward() {
    state.score += 15;
    flashScreen('#4DEBFF', 0.15);
    triggerSlowMo(0.5, 0.15);
    showFloatingText('CLOSE!', '#4DEBFF');
}
```

---

## Anti-Patterns

- **Creating objects in the game loop** -- Use object pooling instead
- **Mixing real time and game time** -- Score/timers use raw `dt`, physics uses `scaledDt`
- **Forgetting to clean up mixers** -- Remove from mixers array when removing entity from scene
- **No delta cap** -- Always `Math.min(clock.getDelta(), 0.1)` to prevent explosion after tab-away
