# Input Handling

Keyboard, gamepad, touch, and pointer lock patterns for Three.js games.

---

## Keyboard State Tracking

Track which keys are currently held (not just single presses):

```javascript
const keys = {};

window.addEventListener('keydown', (e) => {
    keys[e.code] = true;
});

window.addEventListener('keyup', (e) => {
    keys[e.code] = false;
});

// Usage in game loop
function updatePlayer(dt) {
    if (keys['KeyW'] || keys['ArrowUp']) moveForward(dt);
    if (keys['KeyS'] || keys['ArrowDown']) moveBackward(dt);
    if (keys['KeyA'] || keys['ArrowLeft']) moveLeft(dt);
    if (keys['KeyD'] || keys['ArrowRight']) moveRight(dt);
    if (keys['Space']) jump();
}
```

---

## Input Action Mapping

Abstract physical inputs into game actions. This lets you support keyboard + gamepad + touch with the same game logic:

```javascript
class InputManager {
    constructor() {
        this.actions = {};
        this.bindings = new Map();
        this.keys = {};
        this.gamepadAxes = { leftX: 0, leftY: 0, rightX: 0, rightY: 0 };

        window.addEventListener('keydown', (e) => { this.keys[e.code] = true; });
        window.addEventListener('keyup', (e) => { this.keys[e.code] = false; });
    }

    // Define an action with its key bindings
    bind(action, ...keyCodes) {
        this.bindings.set(action, keyCodes);
    }

    // Check if an action is active
    isActive(action) {
        const codes = this.bindings.get(action);
        if (!codes) return false;
        return codes.some(code => this.keys[code]);
    }

    // Get movement vector (normalized)
    getMovement() {
        let x = 0, z = 0;

        if (this.isActive('moveLeft'))  x -= 1;
        if (this.isActive('moveRight')) x += 1;
        if (this.isActive('moveUp'))    z -= 1;
        if (this.isActive('moveDown'))  z += 1;

        // Also add gamepad input
        x += this.gamepadAxes.leftX;
        z += this.gamepadAxes.leftY;

        // Normalize to prevent diagonal speed boost
        const len = Math.sqrt(x * x + z * z);
        if (len > 1) {
            x /= len;
            z /= len;
        }

        return { x, z };
    }

    // Call once per frame to poll gamepad
    updateGamepad() {
        const gamepads = navigator.getGamepads();
        const gp = gamepads[0];
        if (!gp) return;

        // Apply deadzone
        const deadzone = 0.15;
        const applyDeadzone = (v) => Math.abs(v) < deadzone ? 0 : v;

        this.gamepadAxes.leftX = applyDeadzone(gp.axes[0]);
        this.gamepadAxes.leftY = applyDeadzone(gp.axes[1]);
        this.gamepadAxes.rightX = applyDeadzone(gp.axes[2]);
        this.gamepadAxes.rightY = applyDeadzone(gp.axes[3]);

        // Map gamepad buttons to actions
        if (gp.buttons[0]?.pressed) this.keys['_gamepadA'] = true;
        else this.keys['_gamepadA'] = false;
        if (gp.buttons[1]?.pressed) this.keys['_gamepadB'] = true;
        else this.keys['_gamepadB'] = false;
    }
}

// Setup
const input = new InputManager();
input.bind('moveUp',    'KeyW', 'ArrowUp');
input.bind('moveDown',  'KeyS', 'ArrowDown');
input.bind('moveLeft',  'KeyA', 'ArrowLeft');
input.bind('moveRight', 'KeyD', 'ArrowRight');
input.bind('jump',      'Space', '_gamepadA');
input.bind('attack',    'KeyE', '_gamepadB');

// In game loop
function update(dt) {
    input.updateGamepad();

    const move = input.getMovement();
    player.position.x += move.x * speed * dt;
    player.position.z += move.z * speed * dt;

    if (input.isActive('jump')) jump();
}
```

---

## Gamepad API

```javascript
// Check for gamepad connection
window.addEventListener('gamepadconnected', (e) => {
    console.log('Gamepad connected:', e.gamepad.id);
});

window.addEventListener('gamepaddisconnected', (e) => {
    console.log('Gamepad disconnected:', e.gamepad.id);
});

// Poll gamepad state (must be called every frame)
function readGamepad() {
    const gamepads = navigator.getGamepads();
    const gp = gamepads[0];
    if (!gp) return null;

    return {
        // Sticks (axes)
        leftStick:  { x: gp.axes[0], y: gp.axes[1] },
        rightStick: { x: gp.axes[2], y: gp.axes[3] },

        // Face buttons
        a: gp.buttons[0]?.pressed,
        b: gp.buttons[1]?.pressed,
        x: gp.buttons[2]?.pressed,
        y: gp.buttons[3]?.pressed,

        // Shoulder
        lb: gp.buttons[4]?.pressed,
        rb: gp.buttons[5]?.pressed,
        lt: gp.buttons[6]?.value || 0,  // Analog trigger
        rt: gp.buttons[7]?.value || 0,

        // Special
        start: gp.buttons[9]?.pressed,
        dpadUp: gp.buttons[12]?.pressed,
        dpadDown: gp.buttons[13]?.pressed,
        dpadLeft: gp.buttons[14]?.pressed,
        dpadRight: gp.buttons[15]?.pressed
    };
}
```

---

## Touch Controls (Virtual Joystick)

```javascript
class VirtualJoystick {
    constructor(container) {
        this.x = 0;
        this.y = 0;
        this.active = false;
        this.touchId = null;
        this.center = { x: 0, y: 0 };
        this.maxRadius = 50;

        // Create DOM elements
        this.base = document.createElement('div');
        this.base.style.cssText = `
            position: absolute; bottom: 80px; left: 80px;
            width: 120px; height: 120px; border-radius: 50%;
            background: rgba(255,255,255,0.15); border: 2px solid rgba(255,255,255,0.3);
            touch-action: none;
        `;

        this.stick = document.createElement('div');
        this.stick.style.cssText = `
            position: absolute; top: 50%; left: 50%;
            width: 50px; height: 50px; border-radius: 50%;
            background: rgba(255,255,255,0.5);
            transform: translate(-50%, -50%);
            transition: none;
        `;

        this.base.appendChild(this.stick);
        container.appendChild(this.base);

        this.base.addEventListener('touchstart', (e) => this._onStart(e), { passive: false });
        window.addEventListener('touchmove', (e) => this._onMove(e), { passive: false });
        window.addEventListener('touchend', (e) => this._onEnd(e));
    }

    _onStart(e) {
        e.preventDefault();
        const touch = e.changedTouches[0];
        this.touchId = touch.identifier;
        this.active = true;
        const rect = this.base.getBoundingClientRect();
        this.center = { x: rect.left + rect.width / 2, y: rect.top + rect.height / 2 };
    }

    _onMove(e) {
        if (!this.active) return;
        for (const touch of e.changedTouches) {
            if (touch.identifier !== this.touchId) continue;
            e.preventDefault();

            let dx = touch.clientX - this.center.x;
            let dy = touch.clientY - this.center.y;
            const dist = Math.sqrt(dx * dx + dy * dy);

            if (dist > this.maxRadius) {
                dx = (dx / dist) * this.maxRadius;
                dy = (dy / dist) * this.maxRadius;
            }

            this.x = dx / this.maxRadius;  // -1 to 1
            this.y = dy / this.maxRadius;   // -1 to 1

            this.stick.style.transform = `translate(calc(-50% + ${dx}px), calc(-50% + ${dy}px))`;
        }
    }

    _onEnd(e) {
        for (const touch of e.changedTouches) {
            if (touch.identifier !== this.touchId) continue;
            this.active = false;
            this.x = 0;
            this.y = 0;
            this.stick.style.transform = 'translate(-50%, -50%)';
        }
    }
}

// Usage
const joystick = new VirtualJoystick(document.body);

function update(dt) {
    if (joystick.active) {
        player.position.x += joystick.x * speed * dt;
        player.position.z += joystick.y * speed * dt;
    }
}
```

---

## Touch Action Buttons

```javascript
function createTouchButton(label, x, y, onPress, onRelease) {
    const btn = document.createElement('div');
    btn.textContent = label;
    btn.style.cssText = `
        position: absolute; bottom: ${y}px; right: ${x}px;
        width: 60px; height: 60px; border-radius: 50%;
        background: rgba(255,255,255,0.2); border: 2px solid rgba(255,255,255,0.4);
        display: flex; align-items: center; justify-content: center;
        color: white; font-size: 14px; font-weight: bold;
        touch-action: none; user-select: none;
    `;

    btn.addEventListener('touchstart', (e) => { e.preventDefault(); onPress(); });
    btn.addEventListener('touchend', () => onRelease?.());

    document.body.appendChild(btn);
    return btn;
}

// Usage
createTouchButton('A', 80, 80, () => jump(), () => {});
createTouchButton('B', 160, 100, () => attack(), () => {});
```

---

## Pointer Lock (FPS Controls)

```javascript
const canvas = renderer.domElement;

canvas.addEventListener('click', () => {
    canvas.requestPointerLock();
});

let yaw = 0;
let pitch = 0;
const sensitivity = 0.002;

document.addEventListener('mousemove', (e) => {
    if (document.pointerLockElement !== canvas) return;

    yaw -= e.movementX * sensitivity;
    pitch -= e.movementY * sensitivity;

    // Clamp pitch to prevent camera flip
    pitch = Math.max(-Math.PI / 2 + 0.01, Math.min(Math.PI / 2 - 0.01, pitch));

    // Apply to camera
    camera.rotation.order = 'YXZ';
    camera.rotation.y = yaw;
    camera.rotation.x = pitch;
});

document.addEventListener('pointerlockchange', () => {
    const locked = document.pointerLockElement === canvas;
    console.log('Pointer lock:', locked ? 'active' : 'released');
});
```

---

## Preventing Default Browser Behavior

```javascript
// Prevent spacebar from scrolling the page
window.addEventListener('keydown', (e) => {
    if (['Space', 'ArrowUp', 'ArrowDown', 'ArrowLeft', 'ArrowRight'].includes(e.code)) {
        e.preventDefault();
    }
});

// Prevent context menu on right-click (for right-click game actions)
canvas.addEventListener('contextmenu', (e) => e.preventDefault());
```

---

## Best Practices

| Practice | Why |
|----------|-----|
| Use `e.code` not `e.key` | `code` is layout-independent (AZERTY keyboards work) |
| Apply deadzone to gamepad | Sticks drift slightly when idle |
| Normalize diagonal movement | Prevents sqrt(2) speed boost |
| Abstract to action map | Same logic works for keyboard + gamepad + touch |
| `preventDefault` game keys | Stop spacebar scroll, arrow key scroll |
| Poll gamepad every frame | Gamepad API doesn't fire events |
