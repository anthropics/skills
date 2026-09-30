# Audio Guide

Three.js audio system patterns: positional 3D sound, music, SFX pools, and volume management.

---

## Audio Setup

Three.js has a built-in audio system based on the Web Audio API. The key components:

- **AudioListener** -- Attached to camera, acts as the "ears" in 3D space
- **Audio** -- Non-positional sound (music, UI sounds, narration)
- **PositionalAudio** -- 3D spatialized sound (footsteps, gunshots, ambient)

```javascript
import * as THREE from 'three';

// Create listener and attach to camera (do this ONCE)
const listener = new THREE.AudioListener();
camera.add(listener);
```

---

## Non-Positional Audio (Music / UI)

Plays at the same volume regardless of camera position:

```javascript
const music = new THREE.Audio(listener);
const audioLoader = new THREE.AudioLoader();

audioLoader.load('sounds/music.mp3', (buffer) => {
    music.setBuffer(buffer);
    music.setLoop(true);
    music.setVolume(0.5);
    music.play();
});

// Controls
music.pause();
music.play();
music.stop();
music.setVolume(0.3);
```

---

## Positional Audio (3D SFX)

Volume and panning change based on distance and direction from the listener:

```javascript
// Attach positional audio to a 3D object
const sound = new THREE.PositionalAudio(listener);

audioLoader.load('sounds/engine.mp3', (buffer) => {
    sound.setBuffer(buffer);
    sound.setLoop(true);
    sound.setRefDistance(5);      // Distance at which volume is full
    sound.setMaxDistance(50);     // Beyond this, sound is silent
    sound.setRolloffFactor(1);   // How quickly volume drops off
    sound.play();
});

// Add to a scene object (e.g., a car)
car.add(sound);

// The sound follows the car in 3D space automatically
```

---

## SFX Pool Pattern

Pre-load sounds and play from a pool to avoid loading delays and allow overlapping:

```javascript
class SFXManager {
    constructor(listener) {
        this.listener = listener;
        this.loader = new THREE.AudioLoader();
        this.buffers = new Map();
        this.pools = new Map();
    }

    // Pre-load a sound effect
    async load(name, url) {
        return new Promise((resolve, reject) => {
            this.loader.load(url, (buffer) => {
                this.buffers.set(name, buffer);
                resolve();
            }, undefined, reject);
        });
    }

    // Pre-load multiple sounds
    async loadAll(manifest) {
        const promises = manifest.map(({ name, url }) => this.load(name, url));
        await Promise.all(promises);
    }

    // Play a non-positional sound (allows overlapping)
    play(name, { volume = 1, playbackRate = 1 } = {}) {
        const buffer = this.buffers.get(name);
        if (!buffer) {
            console.warn(`SFX not loaded: ${name}`);
            return;
        }

        const sound = new THREE.Audio(this.listener);
        sound.setBuffer(buffer);
        sound.setVolume(volume);
        sound.playbackRate = playbackRate;

        // Auto-cleanup when done
        sound.onEnded = () => {
            sound.disconnect();
        };

        sound.play();
        return sound;
    }

    // Play a positional sound at a location
    playAt(name, position, { volume = 1, refDistance = 5 } = {}) {
        const buffer = this.buffers.get(name);
        if (!buffer) return;

        const sound = new THREE.PositionalAudio(this.listener);
        sound.setBuffer(buffer);
        sound.setVolume(volume);
        sound.setRefDistance(refDistance);

        // Create a temporary object at the position
        const obj = new THREE.Object3D();
        obj.position.copy(position);
        obj.add(sound);
        scene.add(obj);

        sound.onEnded = () => {
            sound.disconnect();
            scene.remove(obj);
        };

        sound.play();
        return sound;
    }
}

// Setup
const sfx = new SFXManager(listener);

await sfx.loadAll([
    { name: 'jump', url: 'sounds/jump.mp3' },
    { name: 'coin', url: 'sounds/coin.mp3' },
    { name: 'hit', url: 'sounds/hit.mp3' },
    { name: 'explosion', url: 'sounds/explosion.mp3' }
]);

// Usage
sfx.play('jump');
sfx.play('coin', { volume: 0.7 });
sfx.play('hit', { volume: 0.5, playbackRate: 1.2 });
sfx.playAt('explosion', enemy.position, { volume: 1, refDistance: 10 });
```

---

## Music Crossfade

Smoothly transition between music tracks:

```javascript
class MusicManager {
    constructor(listener) {
        this.listener = listener;
        this.loader = new THREE.AudioLoader();
        this.current = null;
        this.buffers = new Map();
    }

    async load(name, url) {
        return new Promise((resolve, reject) => {
            this.loader.load(url, (buffer) => {
                this.buffers.set(name, buffer);
                resolve();
            }, undefined, reject);
        });
    }

    crossfadeTo(name, duration = 2) {
        const buffer = this.buffers.get(name);
        if (!buffer) return;

        const newTrack = new THREE.Audio(this.listener);
        newTrack.setBuffer(buffer);
        newTrack.setLoop(true);
        newTrack.setVolume(0);
        newTrack.play();

        const targetVolume = 0.5;
        const fadeStep = targetVolume / (duration * 60); // ~60fps

        const oldTrack = this.current;
        this.current = newTrack;

        let frame = 0;
        const totalFrames = duration * 60;

        function fade() {
            frame++;
            const t = frame / totalFrames;

            // Fade in new track
            newTrack.setVolume(Math.min(targetVolume, t * targetVolume));

            // Fade out old track
            if (oldTrack && oldTrack.isPlaying) {
                oldTrack.setVolume(Math.max(0, targetVolume * (1 - t)));
            }

            if (frame >= totalFrames) {
                if (oldTrack) {
                    oldTrack.stop();
                    oldTrack.disconnect();
                }
                return;
            }

            requestAnimationFrame(fade);
        }

        fade();
    }

    stop() {
        if (this.current && this.current.isPlaying) {
            this.current.stop();
        }
    }
}

// Usage
const music = new MusicManager(listener);
await music.load('menu', 'music/menu-theme.mp3');
await music.load('gameplay', 'music/gameplay.mp3');
await music.load('boss', 'music/boss-fight.mp3');

music.crossfadeTo('menu');
// Later...
music.crossfadeTo('gameplay', 3); // 3-second crossfade
```

---

## Mute / Volume Controls

```javascript
// Global mute via AudioListener
listener.setMasterVolume(0);  // Mute everything
listener.setMasterVolume(1);  // Restore

// Category volumes
const volumeSettings = {
    master: 1.0,
    music: 0.5,
    sfx: 0.8,
    muted: false
};

function setMasterVolume(v) {
    volumeSettings.master = v;
    listener.setMasterVolume(volumeSettings.muted ? 0 : v);
}

function toggleMute() {
    volumeSettings.muted = !volumeSettings.muted;
    listener.setMasterVolume(volumeSettings.muted ? 0 : volumeSettings.master);
}
```

---

## Audio Resume on User Interaction

Browsers block autoplay. You must resume the AudioContext after a user gesture:

```javascript
// Resume audio context on first click/touch
function resumeAudio() {
    if (listener.context.state === 'suspended') {
        listener.context.resume();
    }
}

document.addEventListener('click', resumeAudio, { once: true });
document.addEventListener('touchstart', resumeAudio, { once: true });
document.addEventListener('keydown', resumeAudio, { once: true });
```

---

## Best Practices

| Practice | Why |
|----------|-----|
| Attach AudioListener to camera | "Ears" follow the player naturally |
| Pre-load all SFX at startup | Avoid loading delays during gameplay |
| Use Audio for music/UI | Non-positional, consistent volume |
| Use PositionalAudio for world SFX | 3D spatialization, feels immersive |
| Resume AudioContext on interaction | Required by browser autoplay policy |
| Cleanup sounds when done | `disconnect()` after one-shots to prevent memory leaks |
