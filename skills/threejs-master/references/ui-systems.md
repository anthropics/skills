# UI Systems

HTML overlay approach for HUD, menus, health bars, floating text, and loading screens in Three.js games.

---

## Approach: HTML Over Canvas

The recommended pattern for game UI in Three.js is **HTML elements positioned absolutely over the canvas**. This gives you full CSS power (fonts, flexbox, animations) without fighting WebGL text rendering.

```html
<style>
    #game-container {
        position: relative;
        width: 100vw;
        height: 100vh;
        overflow: hidden;
    }
    canvas {
        display: block;
    }
    #ui {
        position: absolute;
        top: 0; left: 0;
        width: 100%; height: 100%;
        pointer-events: none; /* Let clicks pass through to canvas */
    }
    #ui > * {
        pointer-events: auto; /* Re-enable for interactive UI elements */
    }
</style>

<div id="game-container">
    <!-- Three.js canvas goes here (appended by renderer) -->
    <div id="ui">
        <!-- All UI elements go here -->
    </div>
</div>
```

---

## HUD (Score, Lives, Timer)

```html
<div id="hud" style="
    position: absolute; top: 20px; left: 20px; right: 20px;
    display: flex; justify-content: space-between; align-items: flex-start;
    font-family: 'Courier New', monospace;
    color: white; font-size: 18px;
    text-shadow: 0 0 4px rgba(0,0,0,0.8);
    pointer-events: none;
">
    <div id="score">Score: 0</div>
    <div id="timer">60.0</div>
    <div id="lives">Lives: 3</div>
</div>
```

```javascript
function updateHUD() {
    document.getElementById('score').textContent = `Score: ${state.score}`;
    document.getElementById('timer').textContent = state.timeLeft.toFixed(1);
    document.getElementById('lives').textContent = `Lives: ${'❤️'.repeat(state.lives)}`;
}
```

---

## Health / Progress Bars

```html
<div id="health-bar-container" style="
    position: absolute; bottom: 30px; left: 50%;
    transform: translateX(-50%);
    width: 200px; height: 16px;
    background: rgba(0,0,0,0.6);
    border: 1px solid rgba(255,255,255,0.3);
    border-radius: 8px; overflow: hidden;
">
    <div id="health-bar-fill" style="
        width: 100%; height: 100%;
        background: linear-gradient(90deg, #ff4444, #ff8800);
        transition: width 0.3s ease;
        border-radius: 8px;
    "></div>
</div>
```

```javascript
function updateHealthBar(current, max) {
    const pct = Math.max(0, Math.min(100, (current / max) * 100));
    const fill = document.getElementById('health-bar-fill');
    fill.style.width = pct + '%';

    // Color changes based on health
    if (pct > 60) {
        fill.style.background = 'linear-gradient(90deg, #44ff44, #88ff00)';
    } else if (pct > 30) {
        fill.style.background = 'linear-gradient(90deg, #ffaa00, #ff8800)';
    } else {
        fill.style.background = 'linear-gradient(90deg, #ff4444, #ff0000)';
    }
}
```

---

## Floating Damage / Text Popups

```html
<style>
.floating-text {
    position: absolute;
    font-weight: bold;
    pointer-events: none;
    animation: floatUp 0.6s ease-out forwards;
    font-family: 'Courier New', monospace;
}
@keyframes floatUp {
    0% { opacity: 1; transform: translateY(0) scale(1); }
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

    setTimeout(() => popup.remove(), 600);
}

// 3D-to-screen coordinate conversion for floating text above objects
function worldToScreen(position, camera) {
    const vector = position.clone();
    vector.project(camera);

    return {
        x: ((vector.x + 1) / 2) * window.innerWidth,
        y: ((-vector.y + 1) / 2) * window.innerHeight
    };
}

function showDamageNumber(amount, worldPosition) {
    const screen = worldToScreen(worldPosition, camera);
    showFloatingText(
        `-${amount}`,
        '#ff4444',
        screen.x + 'px',
        screen.y + 'px'
    );
}
```

---

## Menu Screens (Start, Pause, Game Over)

```html
<div id="menu-overlay" style="
    position: absolute; top: 0; left: 0;
    width: 100%; height: 100%;
    display: flex; flex-direction: column;
    align-items: center; justify-content: center;
    background: rgba(0,0,0,0.7);
    backdrop-filter: blur(4px);
    transition: opacity 0.3s;
">
    <h1 id="menu-title" style="
        color: white; font-size: 3rem;
        font-family: 'Courier New', monospace;
        margin-bottom: 2rem;
        text-shadow: 0 0 20px rgba(255,255,255,0.3);
    ">GAME TITLE</h1>

    <div id="menu-buttons" style="
        display: flex; flex-direction: column; gap: 12px;
    ">
        <!-- Buttons inserted by JS -->
    </div>
</div>
```

```javascript
function showMenu(title, buttons) {
    const overlay = document.getElementById('menu-overlay');
    const titleEl = document.getElementById('menu-title');
    const buttonsEl = document.getElementById('menu-buttons');

    titleEl.textContent = title;
    buttonsEl.innerHTML = '';

    buttons.forEach(({ label, onClick }) => {
        const btn = document.createElement('button');
        btn.textContent = label;
        btn.style.cssText = `
            padding: 12px 32px; font-size: 1.1rem;
            background: rgba(255,255,255,0.1);
            border: 1px solid rgba(255,255,255,0.3);
            color: white; cursor: pointer;
            border-radius: 8px;
            font-family: 'Courier New', monospace;
            transition: background 0.2s;
        `;
        btn.addEventListener('mouseenter', () => {
            btn.style.background = 'rgba(255,255,255,0.2)';
        });
        btn.addEventListener('mouseleave', () => {
            btn.style.background = 'rgba(255,255,255,0.1)';
        });
        btn.addEventListener('click', onClick);
        buttonsEl.appendChild(btn);
    });

    overlay.style.display = 'flex';
    overlay.style.opacity = '1';
}

function hideMenu() {
    const overlay = document.getElementById('menu-overlay');
    overlay.style.opacity = '0';
    setTimeout(() => { overlay.style.display = 'none'; }, 300);
}

// Usage
showMenu('GAME OVER', [
    { label: 'Retry', onClick: () => { hideMenu(); restartGame(); } },
    { label: 'Main Menu', onClick: () => { hideMenu(); goToMainMenu(); } }
]);

showMenu('PAUSED', [
    { label: 'Resume', onClick: () => { hideMenu(); resumeGame(); } },
    { label: 'Quit', onClick: () => { hideMenu(); goToMainMenu(); } }
]);
```

---

## Loading Screen with Progress

```html
<div id="loading-screen" style="
    position: absolute; top: 0; left: 0;
    width: 100%; height: 100%;
    display: flex; flex-direction: column;
    align-items: center; justify-content: center;
    background: #111;
    transition: opacity 0.5s;
    z-index: 100;
">
    <div style="color: white; font-size: 1.2rem; margin-bottom: 20px;
                font-family: 'Courier New', monospace;">Loading...</div>
    <div style="width: 200px; height: 4px; background: rgba(255,255,255,0.1);
                border-radius: 2px; overflow: hidden;">
        <div id="loading-bar" style="
            width: 0%; height: 100%;
            background: white;
            transition: width 0.3s ease;
        "></div>
    </div>
    <div id="loading-status" style="
        color: rgba(255,255,255,0.5); font-size: 0.8rem;
        margin-top: 10px; font-family: 'Courier New', monospace;
    "></div>
</div>
```

```javascript
function updateLoadingProgress(loaded, total, currentItem = '') {
    const pct = (loaded / total) * 100;
    document.getElementById('loading-bar').style.width = pct + '%';
    document.getElementById('loading-status').textContent = currentItem;
}

function hideLoadingScreen() {
    const screen = document.getElementById('loading-screen');
    screen.style.opacity = '0';
    setTimeout(() => { screen.style.display = 'none'; }, 500);
}

// Usage with batch loading
async function loadAllAssets() {
    const assets = [
        { name: 'Player', path: 'models/player.glb' },
        { name: 'Enemy', path: 'models/enemy.glb' },
        { name: 'Level', path: 'models/level.glb' }
    ];

    for (let i = 0; i < assets.length; i++) {
        updateLoadingProgress(i, assets.length, assets[i].name);
        await loadModel(assets[i].path);
    }

    updateLoadingProgress(assets.length, assets.length, 'Ready!');
    hideLoadingScreen();
}
```

---

## Minimap

```html
<div id="minimap" style="
    position: absolute; top: 20px; right: 20px;
    width: 150px; height: 150px;
    background: rgba(0,0,0,0.6);
    border: 1px solid rgba(255,255,255,0.3);
    border-radius: 8px; overflow: hidden;
">
    <canvas id="minimap-canvas" width="150" height="150"></canvas>
</div>
```

```javascript
const minimapCanvas = document.getElementById('minimap-canvas');
const minimapCtx = minimapCanvas.getContext('2d');
const minimapScale = 3; // 1 world unit = 3 minimap pixels
const minimapCenter = 75; // Half of canvas size

function updateMinimap() {
    minimapCtx.clearRect(0, 0, 150, 150);

    // Background
    minimapCtx.fillStyle = 'rgba(20, 30, 40, 0.8)';
    minimapCtx.fillRect(0, 0, 150, 150);

    // Draw objects relative to player
    const px = player.position.x;
    const pz = player.position.z;

    // Draw enemies as red dots
    for (const enemy of enemies) {
        const dx = (enemy.position.x - px) * minimapScale + minimapCenter;
        const dz = (enemy.position.z - pz) * minimapScale + minimapCenter;

        if (dx >= 0 && dx <= 150 && dz >= 0 && dz <= 150) {
            minimapCtx.fillStyle = '#ff4444';
            minimapCtx.beginPath();
            minimapCtx.arc(dx, dz, 3, 0, Math.PI * 2);
            minimapCtx.fill();
        }
    }

    // Player at center (always)
    minimapCtx.fillStyle = '#44ff44';
    minimapCtx.beginPath();
    minimapCtx.arc(minimapCenter, minimapCenter, 4, 0, Math.PI * 2);
    minimapCtx.fill();
}
```

---

## Best Practices

| Pattern | When to Use |
|---------|-------------|
| HTML overlay HUD | Score, timer, lives -- always visible |
| Health bars | Player/enemy HP visualization |
| Floating text | Damage numbers, "+1 coin", "COMBO!" |
| Menu overlay | Start, pause, game over screens |
| Loading screen | Asset preloading with progress |
| `pointer-events: none` | On UI container, `auto` on interactive children |
| `worldToScreen` | Position HTML elements above 3D objects |
