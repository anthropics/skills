# Remotion Core Concepts

This document covers the fundamental concepts you need to understand when working with Remotion.

## 1. Compositions

A **Composition** is a video that can be rendered. It combines a React component with video metadata.

### Composition Properties

```typescript
<Composition
  id="MyVideo"           // Unique identifier (used for rendering)
  component={MyVideo}    // React component to render
  durationInFrames={150} // Length in frames
  fps={30}               // Frames per second
  width={1920}           // Video width in pixels
  height={1080}          // Video height in pixels
  defaultProps={{}}      // Props passed to component
/>
```

### Key Points
- The `id` must be unique and contain only letters, numbers, and hyphens
- `durationInFrames` determines how long the video will be (e.g., 150 frames at 30fps = 5 seconds)
- Multiple compositions can exist in one project
- Each composition can have different dimensions and frame rates

### Example
```typescript
// src/Root.tsx
import { Composition } from 'remotion';
import { IntroVideo } from './IntroVideo';
import { OutroVideo } from './OutroVideo';

export const RemotionRoot: React.FC = () => {
  return (
    <>
      <Composition
        id="Intro"
        component={IntroVideo}
        durationInFrames={90}
        fps={30}
        width={1920}
        height={1080}
      />
      <Composition
        id="Outro"
        component={OutroVideo}
        durationInFrames={60}
        fps={30}
        width={1920}
        height={1080}
      />
    </>
  );
};
```

## 2. Frames and Time

Remotion uses **frame-based timing** rather than time-based timing.

### Understanding Frames
- A frame is a single image in the video
- The `useCurrentFrame()` hook returns the current frame number (0-indexed)
- Frame rate (fps) determines how many frames per second

### Calculating Time
```typescript
// Convert frames to seconds
const seconds = frame / fps;

// Convert seconds to frames
const frame = seconds * fps;

// Example: At 30fps
// Frame 0 = 0 seconds
// Frame 30 = 1 second
// Frame 90 = 3 seconds
```

### Example
```typescript
import { useCurrentFrame, useVideoConfig } from 'remotion';

export const MyComponent: React.FC = () => {
  const frame = useCurrentFrame(); // Current frame number
  const { fps } = useVideoConfig(); // Get fps

  const seconds = frame / fps;

  return <div>Current time: {seconds.toFixed(2)}s</div>;
};
```

## 3. Sequences

A **Sequence** is a component that time-shifts its children.

### Basic Usage
```typescript
import { Sequence } from 'remotion';

<Sequence from={30}>
  <Scene1 />
</Sequence>
```

In this example:
- `Scene1` starts at frame 30 (1 second at 30fps)
- When `Scene1` calls `useCurrentFrame()`, it gets 0 at frame 30

### Sequence with Duration
```typescript
<Sequence from={30} durationInFrames={60}>
  <Scene1 />
</Sequence>
```

- `Scene1` appears from frame 30 to frame 90
- After frame 90, the component unmounts

### Nested Sequences
Sequences can be nested, and their timings cascade:

```typescript
<Sequence from={30}>
  <Sequence from={20}>
    <Scene1 />
  </Sequence>
</Sequence>
```

`Scene1` starts at frame 50 (30 + 20)

### Practical Example
```typescript
export const MyVideo: React.FC = () => {
  return (
    <AbsoluteFill>
      {/* Title appears from frame 0-60 */}
      <Sequence from={0} durationInFrames={60}>
        <Title text="Welcome" />
      </Sequence>

      {/* Content appears from frame 60-150 */}
      <Sequence from={60} durationInFrames={90}>
        <Content />
      </Sequence>

      {/* Footer appears from frame 150-180 */}
      <Sequence from={150}>
        <Footer />
      </Sequence>
    </AbsoluteFill>
  );
};
```

## 4. Interpolation

**Interpolation** maps values from one range to another, essential for animations.

### Basic Interpolate
```typescript
import { interpolate } from 'remotion';

const value = interpolate(
  input,           // Input value (usually frame)
  [inputMin, inputMax],   // Input range
  [outputMin, outputMax]  // Output range
);
```

### Examples

**Fade In (0 to 1)**
```typescript
const opacity = interpolate(frame, [0, 30], [0, 1]);
// Frame 0: opacity = 0
// Frame 15: opacity = 0.5
// Frame 30: opacity = 1
```

**Slide In (from left)**
```typescript
const translateX = interpolate(frame, [0, 30], [-100, 0]);
// Frame 0: translateX = -100px (off screen)
// Frame 30: translateX = 0px (in position)
```

**Rotation**
```typescript
const rotation = interpolate(frame, [0, 60], [0, 360]);
// Complete 360° rotation over 60 frames
```

### Extrapolation Options
Control what happens outside the input range:

```typescript
interpolate(frame, [0, 30], [0, 1], {
  extrapolateLeft: 'clamp',    // Values < 0 stay at 0
  extrapolateRight: 'clamp',   // Values > 30 stay at 1
});
```

Options:
- `'extend'` - Continue the interpolation (default)
- `'clamp'` - Stay at the boundary value
- `'identity'` - Return the input value

### Easing Functions
Add easing for more natural animations:

```typescript
import { Easing } from 'remotion';

const value = interpolate(frame, [0, 30], [0, 1], {
  easing: Easing.bezier(0.8, 0.22, 0.96, 0.65),
  extrapolateRight: 'clamp',
});
```

Common easings:
- `Easing.linear` - Constant speed
- `Easing.ease` - Slow start and end
- `Easing.in(Easing.quad)` - Slow start
- `Easing.out(Easing.quad)` - Slow end
- `Easing.inOut(Easing.quad)` - Slow start and end

## 5. Spring Animations

**Spring animations** create natural, physics-based motion.

### Basic Spring
```typescript
import { spring, useVideoConfig } from 'remotion';

const { fps } = useVideoConfig();
const progress = spring({
  frame,
  fps,
  config: {
    damping: 100,
    stiffness: 200,
    mass: 0.5,
  },
});
```

### Spring Parameters

**damping** (default: 10)
- Controls how quickly the spring settles
- Higher = settles faster (less bouncy)
- Lower = more oscillation (more bouncy)

**stiffness** (default: 100)
- Controls the spring tension
- Higher = faster animation
- Lower = slower animation

**mass** (default: 1)
- Controls the object weight
- Higher = slower, more momentum
- Lower = faster, less momentum

### Spring Presets
```typescript
// Gentle bounce
config: {
  damping: 200,
  stiffness: 90,
  mass: 1.2,
}

// Snappy response
config: {
  damping: 100,
  stiffness: 200,
  mass: 0.5,
}

// Smooth ease
config: {
  damping: 100,
  stiffness: 100,
  mass: 1,
}
```

### Scaling Values
Spring animates from 0 to 1 by default. Scale to your desired range:

```typescript
const scale = spring({ frame, fps }) * 2; // 0 to 2

// Or use interpolate
const scale = interpolate(
  spring({ frame, fps }),
  [0, 1],
  [0.5, 1.5]
);
```

### Delayed Spring
```typescript
const progress = spring({
  frame: frame - 30, // Start 30 frames later
  fps,
});
```

## 6. Video Configuration

Access video metadata using `useVideoConfig()`:

```typescript
import { useVideoConfig } from 'remotion';

export const MyComponent: React.FC = () => {
  const { width, height, fps, durationInFrames } = useVideoConfig();

  return (
    <div>
      <p>Video: {width}x{height}</p>
      <p>FPS: {fps}</p>
      <p>Duration: {durationInFrames} frames</p>
      <p>Length: {durationInFrames / fps} seconds</p>
    </div>
  );
};
```

This is useful for:
- Creating responsive layouts
- Calculating timing
- Adapting animations to video duration
- Building reusable components

## 7. Layout Components

### AbsoluteFill
Fills the entire video frame with absolute positioning:

```typescript
import { AbsoluteFill } from 'remotion';

<AbsoluteFill style={{ backgroundColor: 'blue' }}>
  <h1>Centered content</h1>
</AbsoluteFill>
```

Equivalent to:
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

### Series
Play sequences back-to-back:

```typescript
import { Series } from 'remotion';

<Series>
  <Series.Sequence durationInFrames={60}>
    <Scene1 />
  </Series.Sequence>
  <Series.Sequence durationInFrames={90}>
    <Scene2 />
  </Series.Sequence>
  <Series.Sequence durationInFrames={60}>
    <Scene3 />
  </Series.Sequence>
</Series>
```

This automatically sequences them:
- Scene1: frames 0-60
- Scene2: frames 60-150
- Scene3: frames 150-210

## 8. Media Components

### Video
```typescript
import { Video } from 'remotion';

<Video src="video.mp4" />
```

### Audio
```typescript
import { Audio } from 'remotion';

<Audio src="audio.mp3" />
```

### Img
```typescript
import { Img } from 'remotion';

<Img src="image.png" />
```

**Important**: Always use Remotion's media components instead of HTML elements. They handle timing and loading correctly.

## 9. Common Patterns

### Conditional Rendering by Frame
```typescript
const frame = useCurrentFrame();

return (
  <AbsoluteFill>
    {frame < 60 && <IntroScene />}
    {frame >= 60 && frame < 120 && <MainScene />}
    {frame >= 120 && <OutroScene />}
  </AbsoluteFill>
);
```

### Loop Animations
```typescript
const loopDuration = 60; // Loop every 60 frames
const loopedFrame = frame % loopDuration;

const rotation = interpolate(loopedFrame, [0, loopDuration], [0, 360]);
```

### Stagger Animations
```typescript
{items.map((item, i) => {
  const delay = i * 10; // 10 frames between each
  const itemFrame = Math.max(0, frame - delay);
  const opacity = interpolate(itemFrame, [0, 20], [0, 1], {
    extrapolateRight: 'clamp',
  });

  return (
    <div key={i} style={{ opacity }}>
      {item}
    </div>
  );
})}
```

### Combining Animations
```typescript
const opacity = interpolate(frame, [0, 30], [0, 1]);
const scale = spring({ frame, fps });
const rotation = interpolate(frame, [0, 60], [0, 180]);

return (
  <div
    style={{
      opacity,
      transform: `scale(${scale}) rotate(${rotation}deg)`,
    }}
  >
    Content
  </div>
);
```

## Summary

The core Remotion workflow:
1. **Define Compositions** - Register videos with metadata
2. **Use Frames** - Build animations based on current frame
3. **Organize with Sequences** - Time-shift content
4. **Animate with interpolate/spring** - Create smooth motion
5. **Access Config** - Get video dimensions and settings
6. **Layout with Components** - Use AbsoluteFill and Series
7. **Combine Patterns** - Mix techniques for complex animations

Master these concepts and you can create any video programmatically with Remotion!
