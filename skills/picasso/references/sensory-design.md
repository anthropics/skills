# Sensory Design Reference

## Table of Contents
1. UI Sound Design
2. Haptic Feedback
3. Multi-Sensory Integration

---

## 1. UI Sound Design

### Why Sound
Sound provides confirmation that an action occurred, draws attention to important state changes, and adds personality to the interface. It is underused on the web but highly effective when applied with restraint.

### Sourcing Sounds
- **Kenney.nl** -- free CC0 game/UI sound packs. High quality, no attribution required.
- **Freesound.org** -- filter by CC0 license for attribution-free use. Verify license on each clip.
- **Tone.js synthesis** -- generate procedural sounds at runtime. No files to load. Good for simple tones, chimes, and click sounds. Use `Tone.Synth`, `Tone.MembraneSynth`, or `Tone.NoiseSynth` for UI feedback.
- **Self-recorded** -- record short foley sounds and export as WAV/MP3 at 44.1kHz mono.

For inline embedding, convert sounds to base64 data URIs to avoid CORS issues and runtime fetching. Each sound becomes a self-contained TypeScript module.

```typescript
// sounds/click-soft.ts
export const clickSoftSound = "data:audio/wav;base64,UklGR...";
```

### The useSound Hook (Production-Ready)

This hook handles AudioContext lifecycle (including the browser autoplay policy that blocks AudioContext until a user gesture), caches decoded buffers so each sound is fetched and decoded only once, and exposes volume control via a GainNode.

```typescript
// hooks/use-sound.ts
import { useCallback, useEffect, useRef } from "react";

// Shared AudioContext singleton -- one per page avoids resource waste.
let sharedCtx: AudioContext | null = null;
const bufferCache = new Map<string, AudioBuffer>();

function getAudioContext(): AudioContext {
  if (!sharedCtx) {
    sharedCtx = new AudioContext();
  }
  return sharedCtx;
}

// Resume AudioContext on first user gesture (required by Chrome, Safari, Firefox).
// Call this once at app root.
export function initAudioOnGesture(): void {
  const resume = () => {
    const ctx = getAudioContext();
    if (ctx.state === "suspended") {
      ctx.resume();
    }
  };
  const events = ["click", "touchstart", "keydown"] as const;
  events.forEach((e) => document.addEventListener(e, resume, { once: false }));
}

interface UseSoundOptions {
  volume?: number; // 0 to 1, default 0.4
  /** For sound sprites: start offset in seconds */
  offset?: number;
  /** For sound sprites: duration in seconds */
  duration?: number;
}

export function useSound(src: string, options: UseSoundOptions = {}) {
  const { volume = 0.4, offset, duration } = options;
  const gainRef = useRef<GainNode | null>(null);

  const play = useCallback(async () => {
    const ctx = getAudioContext();

    // Resume if suspended (covers edge cases where gesture init missed)
    if (ctx.state === "suspended") {
      await ctx.resume();
    }

    // Fetch + decode only on first play, then cache
    let buffer = bufferCache.get(src);
    if (!buffer) {
      const response = await fetch(src);
      const arrayBuf = await response.arrayBuffer();
      buffer = await ctx.decodeAudioData(arrayBuf);
      bufferCache.set(src, buffer);
    }

    // GainNode for volume control
    const gain = ctx.createGain();
    gain.gain.value = volume;
    gain.connect(ctx.destination);
    gainRef.current = gain;

    const source = ctx.createBufferSource();
    source.buffer = buffer;
    source.connect(gain);

    if (offset !== undefined && duration !== undefined) {
      source.start(0, offset, duration);
    } else {
      source.start(0);
    }
  }, [src, volume, offset, duration]);

  const setVolume = useCallback(
    (v: number) => {
      if (gainRef.current) {
        gainRef.current.gain.value = Math.max(0, Math.min(1, v));
      }
    },
    []
  );

  return { play, setVolume } as const;
}
```

### App Root Setup

```tsx
// app/layout.tsx or app entry
import { initAudioOnGesture } from "@/hooks/use-sound";

// Call once on mount
useEffect(() => {
  initAudioOnGesture();
}, []);
```

### Basic Usage

```tsx
import { useSound } from "@/hooks/use-sound";
import { clickSoftSound } from "@/sounds/click-soft";

function SaveButton() {
  const { play } = useSound(clickSoftSound, { volume: 0.3 });
  return (
    <button onClick={() => { play(); handleSave(); }}>
      Save
    </button>
  );
}
```

### Sound Sprite Pattern

Pack multiple short sounds into a single audio file to reduce HTTP requests and simplify asset management. Reference each sound by its offset and duration within the file.

```typescript
// sounds/ui-sprite.ts
export const uiSprite = "data:audio/wav;base64,UklGR...";

// Offsets in seconds within the sprite file
export const SPRITE_MAP = {
  click:   { offset: 0.0,  duration: 0.08 },
  success: { offset: 0.1,  duration: 0.15 },
  error:   { offset: 0.3,  duration: 0.12 },
  toggle:  { offset: 0.5,  duration: 0.06 },
  whoosh:  { offset: 0.6,  duration: 0.20 },
} as const;
```

```tsx
import { useSound } from "@/hooks/use-sound";
import { uiSprite, SPRITE_MAP } from "@/sounds/ui-sprite";

function ToggleSwitch({ checked, onChange }: ToggleProps) {
  const { play } = useSound(uiSprite, {
    volume: 0.35,
    offset: SPRITE_MAP.toggle.offset,
    duration: SPRITE_MAP.toggle.duration,
  });

  return (
    <button
      role="switch"
      aria-checked={checked}
      onClick={() => { play(); onChange(!checked); }}
    />
  );
}
```

### When to Use Sound
- **Button clicks**: soft, short click sound (50-100ms)
- **Success actions**: pleasant confirmation tone
- **Notifications**: attention-getting but not alarming chime
- **Errors**: subtle alert, not a harsh buzz
- **Toggle switches**: satisfying mechanical click
- **Transitions**: whoosh or swipe sound for page changes

### Rules
- Always provide a sound toggle in the UI (respect user preference)
- Keep sounds under 200ms for UI interactions
- Use the Web Audio API, not `<audio>` elements (lower latency)
- Sound volume should be subtle by default (0.3-0.5 of max)
- Never auto-play sounds on page load
- Gate behind a user preference stored in localStorage or app settings
- Pre-decode buffers when possible; never decode on every play

---

## 2. Haptic Feedback

### The Vibration API (Android, some desktop browsers)

```typescript
// utils/haptics.ts
export function hapticTap() {
  navigator.vibrate?.(10);
}

export function hapticSuccess() {
  navigator.vibrate?.([10, 50, 10]);
}

export function hapticError() {
  navigator.vibrate?.(30);
}

export function hapticWarning() {
  navigator.vibrate?.([10, 30, 10, 30, 10]);
}
```

### iOS Haptic Considerations

The Vibration API is not supported on iOS Safari. For web apps, iOS has no standard haptic API. Strategies for iOS haptic feedback:

1. **Native bridge (Capacitor/React Native)** -- If the app runs in a native wrapper, call `UIImpactFeedbackGenerator` through the bridge. This provides the best haptics on iOS with three intensity levels: `.light`, `.medium`, `.heavy`.

```typescript
// For Capacitor-based apps
import { Haptics, ImpactStyle } from "@capacitor/haptics";

export async function hapticTapIOS() {
  await Haptics.impact({ style: ImpactStyle.Light });
}

export async function hapticSuccessIOS() {
  await Haptics.notification({ type: "success" });
}
```

2. **Graceful degradation** -- For pure web apps on iOS, accept that haptics are unavailable. Never show broken behavior. Wrap all haptic calls behind a safe helper:

```typescript
export function haptic(pattern: number | number[]) {
  if (typeof navigator !== "undefined" && "vibrate" in navigator) {
    navigator.vibrate(pattern);
  }
  // On iOS Safari this is a no-op. The visual and audio
  // feedback channels carry the interaction.
}
```

### When to Use Haptics
- **Button press confirmation**: 10ms pulse on touch
- **Toggle switch**: 10ms pulse on state change
- **Destructive action confirmation**: 30ms pulse before confirmation dialog
- **Pull-to-refresh threshold**: 10ms pulse when the threshold is reached
- **Drag and drop**: 10ms pulse on pickup and drop

### Rules
- Gate behind feature detection (`'vibrate' in navigator` or Capacitor availability)
- Respect `prefers-reduced-motion` by disabling haptics when motion is reduced
- Keep durations very short (10-30ms for taps, never longer than 100ms)
- Do not use haptics for every interaction, only pivotal moments
- Test on real hardware; emulators do not produce haptic feedback

---

## 3. Multi-Sensory Integration

The strongest UI moments combine visual, auditory, and haptic feedback simultaneously. This triple feedback creates a moment of certainty that a single visual change cannot match. Reserve it for milestone moments: order placed, task completed, level achieved, payment confirmed.

### Integration Principles
1. **Synchronize channels** -- sound, haptic, and animation should fire at the same instant. Do not stagger them.
2. **Match intensity** -- a subtle visual pulse pairs with a quiet click and a light tap. A big celebration pairs with a brighter chime and stronger vibration.
3. **Degrade gracefully** -- if sound is muted, the visual and haptic still work. If haptics are unavailable, sound and visual carry it. Each channel must stand on its own.
4. **Respect preferences** -- check `prefers-reduced-motion`, sound toggle state, and haptic toggle state independently.

### Complete Example: Task Completion Feedback

```tsx
import { useCallback } from "react";
import { motion, AnimatePresence } from "framer-motion";
import { useSound } from "@/hooks/use-sound";
import { uiSprite, SPRITE_MAP } from "@/sounds/ui-sprite";
import { hapticSuccess, haptic } from "@/utils/haptics";
import { CheckIcon } from "lucide-react";

interface TaskCompleteButtonProps {
  completed: boolean;
  onComplete: () => void;
  soundEnabled?: boolean;
}

export function TaskCompleteButton({
  completed,
  onComplete,
  soundEnabled = true,
}: TaskCompleteButtonProps) {
  const { play } = useSound(uiSprite, {
    volume: 0.4,
    offset: SPRITE_MAP.success.offset,
    duration: SPRITE_MAP.success.duration,
  });

  const prefersReducedMotion =
    typeof window !== "undefined" &&
    window.matchMedia("(prefers-reduced-motion: reduce)").matches;

  const handleComplete = useCallback(() => {
    if (completed) return;

    // Fire all three channels simultaneously
    onComplete();
    if (soundEnabled) play();
    hapticSuccess();
  }, [completed, onComplete, soundEnabled, play]);

  return (
    <button
      onClick={handleComplete}
      className="relative flex items-center gap-2 rounded-lg bg-zinc-900
                 px-4 py-2 text-sm font-medium text-white
                 transition-colors hover:bg-zinc-800
                 disabled:opacity-50"
      disabled={completed}
    >
      <AnimatePresence mode="wait">
        {completed ? (
          <motion.span
            key="done"
            initial={prefersReducedMotion ? {} : { scale: 0, opacity: 0 }}
            animate={{ scale: 1, opacity: 1 }}
            transition={{ type: "spring", stiffness: 500, damping: 25 }}
            className="flex items-center gap-2 text-emerald-400"
          >
            <CheckIcon className="h-4 w-4" />
            Done
          </motion.span>
        ) : (
          <motion.span
            key="complete"
            exit={prefersReducedMotion ? {} : { scale: 0.8, opacity: 0 }}
            transition={{ duration: 0.1 }}
          >
            Mark Complete
          </motion.span>
        )}
      </AnimatePresence>
    </button>
  );
}
```

### Timeline of a Multi-Sensory Moment

| Time | Visual | Sound | Haptic |
|------|--------|-------|--------|
| 0ms | Button state changes, checkmark scales in with spring animation | Success chime begins (100-150ms clip) | Double-pulse fires: 10ms on, 50ms gap, 10ms on |
| 150ms | Spring animation settles, color transition to emerald completes | Sound fades out naturally | Haptic complete |
| 300ms | Final resting state | Silent | Idle |

All three channels start at t=0 and resolve independently. The user perceives them as a single unified moment.
