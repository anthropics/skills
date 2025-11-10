# Remotion Best Practices

Advanced patterns, optimization techniques, and best practices for creating production-ready Remotion videos.

## 1. Project Structure

### Recommended Directory Layout

```
my-video-project/
├── src/
│   ├── Root.tsx                 # Composition registry
│   ├── compositions/            # Video compositions
│   │   ├── Intro.tsx
│   │   ├── Main.tsx
│   │   └── Outro.tsx
│   ├── components/              # Reusable components
│   │   ├── AnimatedText.tsx
│   │   ├── Logo.tsx
│   │   └── Transition.tsx
│   ├── utils/                   # Helper functions
│   │   ├── animations.ts
│   │   └── colors.ts
│   ├── hooks/                   # Custom hooks
│   │   └── useAnimatedValue.ts
│   └── types/                   # TypeScript types
│       └── index.ts
├── public/                      # Static assets
│   ├── images/
│   ├── fonts/
│   └── audio/
└── remotion.config.ts
```

### Organize by Feature

For larger projects, organize by feature rather than type:

```
src/
├── Root.tsx
├── features/
│   ├── intro/
│   │   ├── IntroComposition.tsx
│   │   ├── IntroTitle.tsx
│   │   └── IntroBackground.tsx
│   ├── main/
│   │   ├── MainComposition.tsx
│   │   └── components/
│   └── outro/
│       └── OutroComposition.tsx
└── shared/
    ├── components/
    └── utils/
```

---

## 2. Component Design

### Keep Components Pure and Deterministic

**DO:**
```typescript
export const AnimatedBox: React.FC = () => {
  const frame = useCurrentFrame();
  const opacity = interpolate(frame, [0, 30], [0, 1]);

  return <div style={{ opacity }}>Content</div>;
};
```

**DON'T:**
```typescript
// ❌ Non-deterministic! Will produce different results each render
export const AnimatedBox: React.FC = () => {
  const opacity = Math.random(); // Never use Math.random()
  const timestamp = Date.now();  // Never use Date.now()

  return <div style={{ opacity }}>Content</div>;
};
```

### Make Components Reusable

**Good: Configurable component**
```typescript
interface AnimatedTextProps {
  text: string;
  from?: number;
  durationInFrames?: number;
  color?: string;
}

export const AnimatedText: React.FC<AnimatedTextProps> = ({
  text,
  from = 0,
  durationInFrames = 30,
  color = 'black',
}) => {
  const frame = useCurrentFrame();
  const localFrame = frame - from;

  const opacity = interpolate(localFrame, [0, durationInFrames], [0, 1], {
    extrapolateRight: 'clamp',
  });

  return <div style={{ opacity, color }}>{text}</div>;
};
```

### Use TypeScript

**Always define prop types:**
```typescript
interface VideoProps {
  title: string;
  subtitle: string;
  duration: number;
  backgroundColor: string;
}

export const MyVideo: React.FC<VideoProps> = ({
  title,
  subtitle,
  duration,
  backgroundColor,
}) => {
  // Component logic
};
```

**Define and export types:**
```typescript
// types/index.ts
export interface AnimationConfig {
  duration: number;
  delay: number;
  easing: (t: number) => number;
}

export type ColorPalette = {
  primary: string;
  secondary: string;
  background: string;
};
```

---

## 3. Performance Optimization

### Avoid Heavy Computations Per Frame

**DON'T:**
```typescript
// ❌ Recalculates on every frame
export const HeavyComponent: React.FC = () => {
  const frame = useCurrentFrame();

  // Heavy computation runs every frame!
  const complexData = Array.from({ length: 10000 }).map((_, i) => {
    return Math.sin(i) * Math.cos(i) * Math.tan(i);
  });

  return <div>{complexData[frame]}</div>;
};
```

**DO:**
```typescript
// ✅ Memoize expensive computations
import { useMemo } from 'react';

export const OptimizedComponent: React.FC = () => {
  const frame = useCurrentFrame();

  // Only computed once
  const complexData = useMemo(() => {
    return Array.from({ length: 10000 }).map((_, i) => {
      return Math.sin(i) * Math.cos(i) * Math.tan(i);
    });
  }, []);

  return <div>{complexData[frame]}</div>;
};
```

### Use React.memo for Static Components

```typescript
interface StaticLogoProps {
  size: number;
}

export const StaticLogo: React.FC<StaticLogoProps> = React.memo(({ size }) => {
  return <img src="logo.png" width={size} height={size} />;
});
```

### Lazy Load Heavy Assets

```typescript
import { delayRender, continueRender } from 'remotion';
import { useState, useEffect } from 'react';

export const HeavyAssetComponent: React.FC = () => {
  const [handle] = useState(() => delayRender());
  const [data, setData] = useState<any>(null);

  useEffect(() => {
    // Load heavy asset
    import('./heavy-data.json').then((module) => {
      setData(module.default);
      continueRender(handle);
    });
  }, [handle]);

  if (!data) return null;

  return <div>{/* Render with data */}</div>;
};
```

---

## 4. Animation Patterns

### Create Reusable Animation Utilities

```typescript
// utils/animations.ts
import { interpolate, spring } from 'remotion';
import type { SpringConfig } from 'remotion';

export const fadeIn = (frame: number, duration: number = 30) => {
  return interpolate(frame, [0, duration], [0, 1], {
    extrapolateRight: 'clamp',
  });
};

export const slideInFromLeft = (frame: number, distance: number = 100) => {
  return interpolate(frame, [0, 30], [-distance, 0], {
    extrapolateRight: 'clamp',
  });
};

export const scaleUp = (
  frame: number,
  fps: number,
  config?: SpringConfig
) => {
  return spring({
    frame,
    fps,
    from: 0,
    to: 1,
    config,
  });
};

export const rotate360 = (frame: number, duration: number = 60) => {
  return interpolate(frame, [0, duration], [0, 360]);
};

// Usage:
const opacity = fadeIn(frame);
const x = slideInFromLeft(frame);
const scale = scaleUp(frame, fps);
```

### Compose Animations

```typescript
interface MultiAnimatedBoxProps {
  delay?: number;
}

export const MultiAnimatedBox: React.FC<MultiAnimatedBoxProps> = ({
  delay = 0,
}) => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();
  const localFrame = Math.max(0, frame - delay);

  const opacity = fadeIn(localFrame);
  const scale = scaleUp(localFrame, fps);
  const x = slideInFromLeft(localFrame);
  const rotation = rotate360(localFrame, 120);

  return (
    <div
      style={{
        opacity,
        transform: `translateX(${x}px) scale(${scale}) rotate(${rotation}deg)`,
      }}
    >
      Content
    </div>
  );
};
```

### Stagger Animations Effectively

```typescript
interface StaggeredListProps {
  items: string[];
  staggerDelay?: number;
}

export const StaggeredList: React.FC<StaggeredListProps> = ({
  items,
  staggerDelay = 5,
}) => {
  return (
    <div>
      {items.map((item, index) => (
        <Sequence key={index} from={index * staggerDelay}>
          <AnimatedListItem text={item} />
        </Sequence>
      ))}
    </div>
  );
};
```

---

## 5. Responsive Design

### Use Video Config for Responsive Layouts

```typescript
export const ResponsiveComponent: React.FC = () => {
  const { width, height } = useVideoConfig();

  const fontSize = width < 1000 ? 32 : 64;
  const padding = width * 0.05; // 5% of width

  return (
    <div style={{ fontSize, padding }}>
      Responsive text
    </div>
  );
};
```

### Create Layout Components

```typescript
interface CenteredProps {
  children: React.ReactNode;
}

export const Centered: React.FC<CenteredProps> = ({ children }) => {
  return (
    <AbsoluteFill
      style={{
        display: 'flex',
        justifyContent: 'center',
        alignItems: 'center',
      }}
    >
      {children}
    </AbsoluteFill>
  );
};

// Usage:
<Centered>
  <h1>Centered Title</h1>
</Centered>
```

---

## 6. Working with Data

### Separate Data from Presentation

```typescript
// data/videoData.ts
export interface VideoData {
  title: string;
  scenes: SceneData[];
}

export interface SceneData {
  text: string;
  duration: number;
  background: string;
}

// compositions/DataDrivenVideo.tsx
export const DataDrivenVideo: React.FC<{ data: VideoData }> = ({ data }) => {
  let currentFrame = 0;

  return (
    <AbsoluteFill>
      {data.scenes.map((scene, i) => {
        const sequence = (
          <Sequence key={i} from={currentFrame} durationInFrames={scene.duration}>
            <Scene {...scene} />
          </Sequence>
        );
        currentFrame += scene.duration;
        return sequence;
      })}
    </AbsoluteFill>
  );
};
```

### Use Default Props for Dynamic Data

```typescript
// Root.tsx
<Composition
  id="DynamicVideo"
  component={DataDrivenVideo}
  durationInFrames={300}
  fps={30}
  width={1920}
  height={1080}
  defaultProps={{
    data: {
      title: "My Video",
      scenes: [
        { text: "Scene 1", duration: 100, background: "blue" },
        { text: "Scene 2", duration: 100, background: "red" },
        { text: "Scene 3", duration: 100, background: "green" },
      ],
    },
  }}
/>
```

---

## 7. Audio & Video Synchronization

### Sync Animations to Audio Beats

```typescript
import { Audio, useCurrentFrame } from 'remotion';

export const MusicSyncedVideo: React.FC = () => {
  const frame = useCurrentFrame();
  const fps = 30;

  // Beat occurs every 0.5 seconds at 120 BPM
  const beatsPerSecond = 2;
  const framesPerBeat = fps / beatsPerSecond;

  // Check if current frame is on a beat
  const isOnBeat = frame % framesPerBeat < 2;

  const scale = isOnBeat ? 1.2 : 1;

  return (
    <AbsoluteFill>
      <Audio src="music.mp3" />
      <div
        style={{
          transform: `scale(${scale})`,
          transition: 'transform 0.1s',
        }}
      >
        Beat reactive element
      </div>
    </AbsoluteFill>
  );
};
```

### Dynamic Volume Control

```typescript
export const FadeOutAudio: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade out audio over last 30 frames
  const volume = interpolate(frame, [270, 300], [1, 0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  return <Audio src="music.mp3" volume={volume} />;
};
```

---

## 8. Testing & Debugging

### Use Console Logging with Frame Numbers

```typescript
export const DebugComponent: React.FC = () => {
  const frame = useCurrentFrame();

  // Log specific frames
  if (frame === 0 || frame === 30 || frame === 60) {
    console.log(`Frame ${frame}:`, { /* debug info */ });
  }

  return <div>Content</div>;
};
```

### Create Debug Overlays

```typescript
export const DebugOverlay: React.FC = () => {
  const frame = useCurrentFrame();
  const config = useVideoConfig();

  if (process.env.NODE_ENV !== 'development') {
    return null;
  }

  return (
    <div
      style={{
        position: 'absolute',
        top: 10,
        left: 10,
        background: 'rgba(0,0,0,0.7)',
        color: 'white',
        padding: 10,
        fontFamily: 'monospace',
        fontSize: 12,
      }}
    >
      <div>Frame: {frame}</div>
      <div>Time: {(frame / config.fps).toFixed(2)}s</div>
      <div>FPS: {config.fps}</div>
    </div>
  );
};
```

### Test at Different Frame Rates

```typescript
// Create compositions for different frame rates
<Composition
  id="MyVideo-30fps"
  component={MyVideo}
  durationInFrames={150}
  fps={30}
  width={1920}
  height={1080}
/>
<Composition
  id="MyVideo-60fps"
  component={MyVideo}
  durationInFrames={300}
  fps={60}
  width={1920}
  height={1080}
/>
```

---

## 9. Code Organization

### Create Custom Hooks

```typescript
// hooks/useAnimatedValue.ts
import { useCurrentFrame, useVideoConfig, spring } from 'remotion';

export const useAnimatedValue = (
  delay: number = 0,
  config?: SpringConfig
) => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  return spring({
    frame: Math.max(0, frame - delay),
    fps,
    config,
  });
};

// Usage:
const scale = useAnimatedValue(30);
```

### Extract Complex Logic

```typescript
// utils/particleSystem.ts
export interface Particle {
  x: number;
  y: number;
  vx: number;
  vy: number;
}

export const createParticles = (count: number, seed: string): Particle[] => {
  return Array.from({ length: count }).map((_, i) => ({
    x: random(`${seed}-x-${i}`) * 1920,
    y: random(`${seed}-y-${i}`) * 1080,
    vx: (random(`${seed}-vx-${i}`) - 0.5) * 10,
    vy: (random(`${seed}-vy-${i}`) - 0.5) * 10,
  }));
};

export const updateParticle = (particle: Particle, frame: number): Particle => {
  return {
    ...particle,
    x: particle.x + particle.vx * frame,
    y: particle.y + particle.vy * frame,
  };
};
```

---

## 10. Rendering & Deployment

### Optimize Render Settings

```bash
# High quality for final output
npx remotion render MyVideo output.mp4 \
  --codec=h264 \
  --quality=90 \
  --concurrency=4

# Fast preview render
npx remotion render MyVideo preview.mp4 \
  --codec=h264 \
  --quality=50 \
  --scale=0.5 \
  --concurrency=8
```

### CI/CD Integration

```yaml
# .github/workflows/render.yml
name: Render Video
on: [push]
jobs:
  render:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      - uses: actions/setup-node@v2
        with:
          node-version: '18'
      - run: npm ci
      - run: npx remotion render MyVideo output.mp4
      - uses: actions/upload-artifact@v2
        with:
          name: video
          path: output.mp4
```

### Environment-Specific Rendering

```typescript
import { getRemotionEnvironment } from 'remotion';

export const MyVideo: React.FC = () => {
  const env = getRemotionEnvironment();
  const isRendering = env === 'rendering';

  // Disable expensive effects during preview
  const enableParticles = isRendering;

  return (
    <AbsoluteFill>
      {enableParticles && <ParticleSystem />}
    </AbsoluteFill>
  );
};
```

---

## Common Pitfalls to Avoid

1. **Using non-deterministic functions**: Never use `Math.random()`, `Date.now()`, or `Math.random()`
2. **Heavy computations per frame**: Memoize expensive calculations
3. **Not using Remotion components**: Always use `<Video>`, `<Audio>`, `<Img>` instead of HTML equivalents
4. **Forgetting to clamp interpolations**: Use `extrapolateRight: 'clamp'` to avoid values beyond range
5. **Not testing at target frame rate**: Always test at the FPS you'll render at
6. **Hardcoding dimensions**: Use `useVideoConfig()` for responsive designs
7. **Not handling async data**: Use `delayRender()` and `continueRender()` for async operations
8. **Ignoring performance**: Monitor render times and optimize slow frames

---

## Checklist for Production Videos

- [ ] All animations are deterministic
- [ ] No usage of `Math.random()` or `Date.now()`
- [ ] TypeScript types defined for all props
- [ ] Components are pure and reusable
- [ ] Heavy computations are memoized
- [ ] Responsive design using `useVideoConfig()`
- [ ] Proper error handling for async operations
- [ ] Tested at target frame rate and resolution
- [ ] Audio synchronized correctly
- [ ] Debug code removed
- [ ] Optimized render settings chosen
- [ ] License compliance verified

---

For more advanced topics, consult the official Remotion documentation at https://remotion.dev/docs
