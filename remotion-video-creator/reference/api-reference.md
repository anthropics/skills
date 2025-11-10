# Remotion API Reference

Complete API reference for Remotion's core functions, hooks, and components.

## Hooks

### useCurrentFrame()

Returns the current frame number (0-indexed).

```typescript
import { useCurrentFrame } from 'remotion';

const frame = useCurrentFrame();
// Frame 0 = first frame
// Frame 1 = second frame, etc.
```

**Returns**: `number`

**Usage**: Essential for creating animations. Use this value with `interpolate()` or `spring()`.

---

### useVideoConfig()

Returns the video configuration.

```typescript
import { useVideoConfig } from 'remotion';

const { width, height, fps, durationInFrames, id, defaultProps } = useVideoConfig();
```

**Returns**: `VideoConfig`
```typescript
interface VideoConfig {
  width: number;              // Video width in pixels
  height: number;             // Video height in pixels
  fps: number;                // Frames per second
  durationInFrames: number;   // Total duration in frames
  id: string;                 // Composition ID
  defaultProps: object;       // Props passed to composition
}
```

**Usage**: Access composition metadata for responsive layouts and calculations.

---

## Animation Functions

### interpolate()

Maps an input value to an output range.

```typescript
import { interpolate } from 'remotion';

const value = interpolate(
  input: number,
  inputRange: [number, number] | [number, number, ...number[]],
  outputRange: [number, number] | [number, number, ...number[]],
  options?: InterpolateOptions
);
```

**Parameters**:
- `input`: The value to interpolate (typically `frame`)
- `inputRange`: Array of input values (e.g., `[0, 30]`)
- `outputRange`: Array of output values (e.g., `[0, 1]`)
- `options`: Optional configuration

**Options**:
```typescript
interface InterpolateOptions {
  extrapolateLeft?: 'extend' | 'clamp' | 'identity';
  extrapolateRight?: 'extend' | 'clamp' | 'identity';
  easing?: (t: number) => number;
}
```

**Examples**:
```typescript
// Basic fade in
const opacity = interpolate(frame, [0, 30], [0, 1]);

// Multiple keyframes
const scale = interpolate(frame, [0, 30, 60], [0, 1, 0.5]);

// With easing
const smooth = interpolate(frame, [0, 30], [0, 100], {
  easing: Easing.bezier(0.8, 0.22, 0.96, 0.65),
});

// Clamped
const clamped = interpolate(frame, [0, 30], [0, 1], {
  extrapolateRight: 'clamp',
});
```

---

### spring()

Creates a physics-based spring animation.

```typescript
import { spring } from 'remotion';

const value = spring({
  frame: number,
  fps: number,
  config?: SpringConfig,
  from?: number,
  to?: number,
  durationInFrames?: number,
  delay?: number,
});
```

**Parameters**:
```typescript
interface SpringConfig {
  damping?: number;      // Default: 10
  stiffness?: number;    // Default: 100
  mass?: number;         // Default: 1
  overshootClamping?: boolean;  // Default: false
}
```

**Returns**: `number` (typically 0 to 1)

**Examples**:
```typescript
// Basic spring
const progress = spring({
  frame,
  fps,
});

// Custom config
const bouncy = spring({
  frame,
  fps,
  config: {
    damping: 12,
    stiffness: 200,
    mass: 0.5,
  },
});

// Spring from/to specific values
const scale = spring({
  frame,
  fps,
  from: 0,
  to: 2,
});

// Delayed spring
const delayed = spring({
  frame,
  fps,
  delay: 30, // Start after 30 frames
});
```

---

### Easing

Easing functions for interpolation.

```typescript
import { Easing } from 'remotion';
```

**Available Functions**:
- `Easing.linear` - No easing
- `Easing.ease` - Ease in and out
- `Easing.in(fn)` - Ease in
- `Easing.out(fn)` - Ease out
- `Easing.inOut(fn)` - Ease in and out

**Base Functions**:
- `Easing.quad` - Quadratic
- `Easing.cubic` - Cubic
- `Easing.poly(n)` - Polynomial
- `Easing.sin` - Sinusoidal
- `Easing.exp` - Exponential
- `Easing.circle` - Circular
- `Easing.back(s)` - Back
- `Easing.bounce` - Bounce
- `Easing.elastic(s)` - Elastic

**Custom Bezier**:
```typescript
Easing.bezier(x1, y1, x2, y2)
```

**Examples**:
```typescript
// Ease out quad
interpolate(frame, [0, 30], [0, 100], {
  easing: Easing.out(Easing.quad),
});

// Bounce
interpolate(frame, [0, 30], [0, 100], {
  easing: Easing.bounce,
});

// Custom bezier
interpolate(frame, [0, 30], [0, 100], {
  easing: Easing.bezier(0.8, 0.22, 0.96, 0.65),
});
```

---

## Components

### Composition

Registers a video composition.

```typescript
import { Composition } from 'remotion';

<Composition
  id={string}
  component={React.ComponentType<any>}
  durationInFrames={number}
  fps={number}
  width={number}
  height={number}
  defaultProps?: object
  schema?: ZodType
/>
```

**Props**:
- `id`: Unique identifier (required)
- `component`: React component to render (required)
- `durationInFrames`: Video length in frames (required)
- `fps`: Frames per second (required)
- `width`: Video width in pixels (required)
- `height`: Video height in pixels (required)
- `defaultProps`: Default props for component (optional)
- `schema`: Zod schema for prop validation (optional)

**Example**:
```typescript
<Composition
  id="MyVideo"
  component={MyVideo}
  durationInFrames={150}
  fps={30}
  width={1920}
  height={1080}
  defaultProps={{ title: "Hello World" }}
/>
```

---

### Sequence

Time-shifts its children.

```typescript
import { Sequence } from 'remotion';

<Sequence
  from={number}
  durationInFrames?: number
  name?: string
  layout?: 'absolute-fill' | 'none'
>
  {children}
</Sequence>
```

**Props**:
- `from`: Frame to start at (required)
- `durationInFrames`: How long to display (optional)
- `name`: Name for debugging (optional)
- `layout`: Layout style (default: 'absolute-fill')

**Examples**:
```typescript
// Start at frame 30
<Sequence from={30}>
  <MyComponent />
</Sequence>

// Start at frame 30, last 60 frames
<Sequence from={30} durationInFrames={60}>
  <MyComponent />
</Sequence>

// Nested sequences
<Sequence from={30}>
  <Sequence from={20}>
    <MyComponent /> {/* Starts at frame 50 */}
  </Sequence>
</Sequence>
```

---

### Series

Plays sequences back-to-back.

```typescript
import { Series } from 'remotion';

<Series>
  <Series.Sequence durationInFrames={60}>
    <Scene1 />
  </Series.Sequence>
  <Series.Sequence durationInFrames={90}>
    <Scene2 />
  </Series.Sequence>
</Series>
```

**Props for Series.Sequence**:
- `durationInFrames`: Duration of this sequence (required)
- `layout`: Layout style (optional)

**Note**: Sequences automatically start where the previous one ended.

---

### AbsoluteFill

Fills the entire frame with absolute positioning.

```typescript
import { AbsoluteFill } from 'remotion';

<AbsoluteFill style={{ backgroundColor: 'red' }}>
  <h1>Centered content</h1>
</AbsoluteFill>
```

**Props**: Standard React `div` props

**Equivalent CSS**:
```css
position: absolute;
top: 0;
left: 0;
right: 0;
bottom: 0;
display: flex;
justify-content: center;
align-items: center;
```

---

### Video

Renders a video file.

```typescript
import { Video } from 'remotion';

<Video
  src={string | StaticFile}
  volume?: number | ((frame: number) => number)
  playbackRate?: number
  startFrom?: number
  endAt?: number
  muted?: boolean
  style?: React.CSSProperties
/>
```

**Props**:
- `src`: Video file path or imported file (required)
- `volume`: Volume level 0-1 or function (default: 1)
- `playbackRate`: Playback speed multiplier (default: 1)
- `startFrom`: Frame to start from (optional)
- `endAt`: Frame to end at (optional)
- `muted`: Mute audio (default: false)

**Examples**:
```typescript
// Basic video
<Video src="video.mp4" />

// Start from frame 30
<Video src="video.mp4" startFrom={30} />

// Dynamic volume
<Video
  src="video.mp4"
  volume={(f) => interpolate(f, [0, 30], [0, 1])}
/>

// Import and use
import videoFile from './video.mp4';
<Video src={videoFile} />
```

---

### Audio

Renders an audio file.

```typescript
import { Audio } from 'remotion';

<Audio
  src={string | StaticFile}
  volume?: number | ((frame: number) => number)
  playbackRate?: number
  startFrom?: number
  endAt?: number
  muted?: boolean
/>
```

**Props**: Same as `<Video>` but without visual props.

**Examples**:
```typescript
// Basic audio
<Audio src="music.mp3" />

// Fade in audio
<Audio
  src="music.mp3"
  volume={(f) => interpolate(f, [0, 30], [0, 1], {
    extrapolateRight: 'clamp',
  })}
/>
```

---

### Img

Renders an image.

```typescript
import { Img } from 'remotion';

<Img
  src={string | StaticFile}
  style?: React.CSSProperties
  className?: string
/>
```

**Why use `<Img>` instead of `<img>`?**
- Ensures image is loaded before rendering
- Better error handling
- Works correctly in serverless environments

**Example**:
```typescript
import logo from './logo.png';

<Img src={logo} style={{ width: 200, height: 200 }} />
```

---

## Utility Functions

### continueRender() / delayRender()

Handle asynchronous operations during rendering.

```typescript
import { continueRender, delayRender } from 'remotion';

const MyComponent = () => {
  const [handle] = useState(() => delayRender());
  const [data, setData] = useState(null);

  useEffect(() => {
    fetchData().then((result) => {
      setData(result);
      continueRender(handle);
    });
  }, [handle]);

  if (!data) return null;
  return <div>{data.text}</div>;
};
```

**Usage**: Tell Remotion to wait for async operations before rendering.

---

### getRemotionEnvironment()

Detects the current Remotion environment.

```typescript
import { getRemotionEnvironment } from 'remotion';

const env = getRemotionEnvironment();
// Returns: 'player-development' | 'player-production' | 'rendering' | 'preview' | null
```

**Usage**: Conditionally render or optimize based on environment.

---

### random()

Deterministic random number generator.

```typescript
import { random } from 'remotion';

const value = random(seed: string | number | null);
```

**Returns**: `number` between 0 and 1

**Important**: Always use `random()` instead of `Math.random()` to ensure deterministic rendering.

**Example**:
```typescript
const x = random('x-pos') * 1920;
const y = random('y-pos') * 1080;
const color = random('color') > 0.5 ? 'red' : 'blue';
```

---

### noise2D() / noise3D() / noise4D()

Simplex noise functions.

```typescript
import { noise2D, noise3D, noise4D } from 'remotion';

const value2D = noise2D(seed: string, x: number, y: number);
const value3D = noise3D(seed: string, x: number, y: number, z: number);
const value4D = noise4D(seed: string, x: number, y: number, z: number, w: number);
```

**Returns**: `number` between -1 and 1

**Usage**: Create smooth, organic animations.

**Example**:
```typescript
const frame = useCurrentFrame();
const { width, height } = useVideoConfig();

// Animated noise
const noiseValue = noise3D('movement', frame / 20, 0, 0);
const x = width / 2 + noiseValue * 200;

// Perlin noise texture
const dots = Array.from({ length: 100 }).map((_, i) => {
  const nx = (i % 10) / 10;
  const ny = Math.floor(i / 10) / 10;
  const noise = noise2D('dots', nx * 5, ny * 5);
  const opacity = (noise + 1) / 2; // Normalize to 0-1

  return <div key={i} style={{ opacity }} />;
});
```

---

## CLI Commands

### render

Render a composition to video.

```bash
npx remotion render [composition-id] [output-file]
```

**Options**:
- `--codec`: Video codec (h264, h265, vp8, vp9, prores)
- `--quality`: Quality level (0-100)
- `--concurrency`: Number of threads
- `--image-format`: Image format (png, jpeg)
- `--scale`: Scale factor
- `--overwrite`: Overwrite existing file

**Examples**:
```bash
# Basic render
npx remotion render MyVideo out.mp4

# High quality
npx remotion render MyVideo out.mp4 --quality=100

# H.265 codec
npx remotion render MyVideo out.mp4 --codec=h265

# PNG sequence
npx remotion render MyVideo out/frame.png --sequence
```

---

### still

Render a single frame as an image.

```bash
npx remotion still [composition-id] [output-file]
```

**Options**:
- `--frame`: Frame number to render (default: 0)
- `--scale`: Scale factor

**Example**:
```bash
npx remotion still MyVideo thumbnail.png --frame=30
```

---

### preview

Start the development server.

```bash
npx remotion preview
```

**Options**:
- `--port`: Port number (default: 3000)
- `--webpack-poll`: Enable webpack polling

---

### upgrade

Upgrade Remotion packages.

```bash
npx remotion upgrade
```

Automatically updates all Remotion packages to the latest version.

---

## Type Definitions

### Component Props

```typescript
import { FC } from 'react';

interface MyVideoProps {
  title: string;
  duration: number;
}

export const MyVideo: FC<MyVideoProps> = ({ title, duration }) => {
  // Component logic
};
```

### Video Config Types

```typescript
type VideoConfig = {
  width: number;
  height: number;
  fps: number;
  durationInFrames: number;
  id: string;
  defaultProps: Record<string, unknown>;
};
```

---

## Best Practices

1. **Always use Remotion components**: Use `<Video>`, `<Audio>`, `<Img>` instead of HTML equivalents
2. **Deterministic rendering**: Never use `Math.random()` or `Date.now()` - use `random()` instead
3. **Frame-based calculations**: Always base animations on `useCurrentFrame()`
4. **Type safety**: Use TypeScript for props and configs
5. **Pure components**: Ensure same frame always produces same output
6. **Optimize performance**: Avoid heavy computations per frame

For more details, visit https://remotion.dev/docs
