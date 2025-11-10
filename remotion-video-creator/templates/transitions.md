# Transition Templates

Ready-to-use transition effects for switching between scenes in Remotion videos.

## 1. Fade Transition

Simple fade in/out transition.

```typescript
import { useCurrentFrame, interpolate, AbsoluteFill } from 'remotion';

interface FadeTransitionProps {
  durationInFrames: number;
  children: React.ReactNode;
}

export const FadeTransition: React.FC<FadeTransitionProps> = ({
  durationInFrames,
  children,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [0, durationInFrames / 4, (durationInFrames * 3) / 4, durationInFrames],
    [0, 1, 1, 0]
  );

  return (
    <AbsoluteFill style={{ opacity }}>
      {children}
    </AbsoluteFill>
  );
};

// Usage:
// <Sequence from={0} durationInFrames={60}>
//   <FadeTransition durationInFrames={60}>
//     <Scene1 />
//   </FadeTransition>
// </Sequence>
```

---

## 2. Slide Transition

Slides content in from one direction and out to another.

```typescript
import { useCurrentFrame, interpolate, AbsoluteFill, useVideoConfig } from 'remotion';

type Direction = 'left' | 'right' | 'top' | 'bottom';

interface SlideTransitionProps {
  durationInFrames: number;
  direction: Direction;
  children: React.ReactNode;
}

export const SlideTransition: React.FC<SlideTransitionProps> = ({
  durationInFrames,
  direction,
  children,
}) => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();

  const getTransform = () => {
    const enterDuration = durationInFrames / 3;
    const exitStart = (durationInFrames * 2) / 3;

    switch (direction) {
      case 'left':
        return `translateX(${interpolate(
          frame,
          [0, enterDuration, exitStart, durationInFrames],
          [-width, 0, 0, width]
        )}px)`;
      case 'right':
        return `translateX(${interpolate(
          frame,
          [0, enterDuration, exitStart, durationInFrames],
          [width, 0, 0, -width]
        )}px)`;
      case 'top':
        return `translateY(${interpolate(
          frame,
          [0, enterDuration, exitStart, durationInFrames],
          [-height, 0, 0, height]
        )}px)`;
      case 'bottom':
        return `translateY(${interpolate(
          frame,
          [0, enterDuration, exitStart, durationInFrames],
          [height, 0, 0, -height]
        )}px)`;
    }
  };

  return (
    <AbsoluteFill style={{ transform: getTransform() }}>
      {children}
    </AbsoluteFill>
  );
};
```

---

## 3. Wipe Transition

Wipe from one scene to another.

```typescript
import { useCurrentFrame, interpolate, AbsoluteFill } from 'remotion';

interface WipeTransitionProps {
  from: React.ReactNode;
  to: React.ReactNode;
  durationInFrames: number;
  direction?: 'left' | 'right' | 'top' | 'bottom';
}

export const WipeTransition: React.FC<WipeTransitionProps> = ({
  from,
  to,
  durationInFrames,
  direction = 'right',
}) => {
  const frame = useCurrentFrame();

  const progress = interpolate(frame, [0, durationInFrames], [0, 100], {
    extrapolateRight: 'clamp',
  });

  const getClipPath = () => {
    switch (direction) {
      case 'right':
        return `inset(0 ${100 - progress}% 0 0)`;
      case 'left':
        return `inset(0 0 0 ${100 - progress}%)`;
      case 'bottom':
        return `inset(0 0 ${100 - progress}% 0)`;
      case 'top':
        return `inset(${100 - progress}% 0 0 0)`;
    }
  };

  return (
    <>
      <AbsoluteFill>{from}</AbsoluteFill>
      <AbsoluteFill style={{ clipPath: getClipPath() }}>
        {to}
      </AbsoluteFill>
    </>
  );
};
```

---

## 4. Zoom Transition

Zoom in/out transition effect.

```typescript
import { useCurrentFrame, interpolate, AbsoluteFill } from 'remotion';

interface ZoomTransitionProps {
  from: React.ReactNode;
  to: React.ReactNode;
  durationInFrames: number;
}

export const ZoomTransition: React.FC<ZoomTransitionProps> = ({
  from,
  to,
  durationInFrames,
}) => {
  const frame = useCurrentFrame();

  const scaleOut = interpolate(
    frame,
    [0, durationInFrames / 2],
    [1, 2],
    { extrapolateRight: 'clamp' }
  );

  const opacityOut = interpolate(
    frame,
    [0, durationInFrames / 2],
    [1, 0],
    { extrapolateRight: 'clamp' }
  );

  const scaleIn = interpolate(
    frame,
    [durationInFrames / 2, durationInFrames],
    [0.5, 1],
    { extrapolateLeft: 'clamp' }
  );

  const opacityIn = interpolate(
    frame,
    [durationInFrames / 2, durationInFrames],
    [0, 1],
    { extrapolateLeft: 'clamp' }
  );

  return (
    <>
      <AbsoluteFill
        style={{
          transform: `scale(${scaleOut})`,
          opacity: opacityOut,
        }}
      >
        {from}
      </AbsoluteFill>
      <AbsoluteFill
        style={{
          transform: `scale(${scaleIn})`,
          opacity: opacityIn,
        }}
      >
        {to}
      </AbsoluteFill>
    </>
  );
};
```

---

## 5. Rotate Transition

3D rotation transition.

```typescript
import { useCurrentFrame, interpolate, AbsoluteFill } from 'remotion';

interface RotateTransitionProps {
  from: React.ReactNode;
  to: React.ReactNode;
  durationInFrames: number;
  axis?: 'x' | 'y';
}

export const RotateTransition: React.FC<RotateTransitionProps> = ({
  from,
  to,
  durationInFrames,
  axis = 'y',
}) => {
  const frame = useCurrentFrame();

  const rotation = interpolate(frame, [0, durationInFrames], [0, 180]);

  const showFrom = frame < durationInFrames / 2;

  return (
    <AbsoluteFill style={{ perspective: 1000 }}>
      <AbsoluteFill
        style={{
          transform: `rotate${axis.toUpperCase()}(${rotation}deg)`,
          backfaceVisibility: 'hidden',
          opacity: showFrom ? 1 : 0,
        }}
      >
        {from}
      </AbsoluteFill>
      <AbsoluteFill
        style={{
          transform: `rotate${axis.toUpperCase()}(${rotation - 180}deg)`,
          backfaceVisibility: 'hidden',
          opacity: showFrom ? 0 : 1,
        }}
      >
        {to}
      </AbsoluteFill>
    </AbsoluteFill>
  );
};
```

---

## 6. Circle Wipe

Circular reveal transition.

```typescript
import { useCurrentFrame, interpolate, AbsoluteFill, useVideoConfig } from 'remotion';

interface CircleWipeProps {
  from: React.ReactNode;
  to: React.ReactNode;
  durationInFrames: number;
  reverse?: boolean;
}

export const CircleWipe: React.FC<CircleWipeProps> = ({
  from,
  to,
  durationInFrames,
  reverse = false,
}) => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();

  const maxRadius = Math.sqrt(width ** 2 + height ** 2);

  const radius = interpolate(
    frame,
    [0, durationInFrames],
    reverse ? [maxRadius, 0] : [0, maxRadius],
    { extrapolateRight: 'clamp' }
  );

  return (
    <>
      <AbsoluteFill>{from}</AbsoluteFill>
      <AbsoluteFill>
        <svg width={width} height={height}>
          <defs>
            <mask id="circle-mask">
              <rect width={width} height={height} fill="white" />
              <circle
                cx={width / 2}
                cy={height / 2}
                r={radius}
                fill={reverse ? 'white' : 'black'}
              />
            </mask>
          </defs>
          <foreignObject
            width={width}
            height={height}
            mask="url(#circle-mask)"
          >
            <div style={{ width, height }}>{reverse ? from : to}</div>
          </foreignObject>
        </svg>
      </AbsoluteFill>
    </>
  );
};
```

---

## 7. Pixelate Transition

Pixelation effect transition.

```typescript
import { useCurrentFrame, interpolate, AbsoluteFill } from 'remotion';

interface PixelateTransitionProps {
  from: React.ReactNode;
  to: React.ReactNode;
  durationInFrames: number;
}

export const PixelateTransition: React.FC<PixelateTransitionProps> = ({
  from,
  to,
  durationInFrames,
}) => {
  const frame = useCurrentFrame();

  const pixelSize = interpolate(
    frame,
    [0, durationInFrames / 2, durationInFrames],
    [1, 50, 1]
  );

  const opacity = interpolate(
    frame,
    [0, durationInFrames / 2, durationInFrames],
    [1, 0, 1]
  );

  const showFrom = frame < durationInFrames / 2;

  return (
    <AbsoluteFill
      style={{
        imageRendering: pixelSize > 10 ? 'pixelated' : 'auto',
        filter: `contrast(${100 + pixelSize}%)`,
      }}
    >
      <AbsoluteFill style={{ opacity: showFrom ? opacity : 0 }}>
        {from}
      </AbsoluteFill>
      <AbsoluteFill style={{ opacity: showFrom ? 0 : opacity }}>
        {to}
      </AbsoluteFill>
    </AbsoluteFill>
  );
};
```

---

## 8. Blur Transition

Gaussian blur transition.

```typescript
import { useCurrentFrame, interpolate, AbsoluteFill } from 'remotion';

interface BlurTransitionProps {
  from: React.ReactNode;
  to: React.ReactNode;
  durationInFrames: number;
}

export const BlurTransition: React.FC<BlurTransitionProps> = ({
  from,
  to,
  durationInFrames,
}) => {
  const frame = useCurrentFrame();

  const blurAmount = interpolate(
    frame,
    [0, durationInFrames / 2, durationInFrames],
    [0, 30, 0]
  );

  const fromOpacity = interpolate(
    frame,
    [0, durationInFrames / 2],
    [1, 0],
    { extrapolateRight: 'clamp' }
  );

  const toOpacity = interpolate(
    frame,
    [durationInFrames / 2, durationInFrames],
    [0, 1],
    { extrapolateLeft: 'clamp' }
  );

  return (
    <>
      <AbsoluteFill
        style={{
          filter: `blur(${blurAmount}px)`,
          opacity: fromOpacity,
        }}
      >
        {from}
      </AbsoluteFill>
      <AbsoluteFill
        style={{
          filter: `blur(${blurAmount}px)`,
          opacity: toOpacity,
        }}
      >
        {to}
      </AbsoluteFill>
    </>
  );
};
```

---

## 9. Glitch Transition

Glitch effect transition.

```typescript
import { useCurrentFrame, random, AbsoluteFill, useVideoConfig } from 'remotion';

interface GlitchTransitionProps {
  from: React.ReactNode;
  to: React.ReactNode;
  durationInFrames: number;
}

export const GlitchTransition: React.FC<GlitchTransitionProps> = ({
  from,
  to,
  durationInFrames,
}) => {
  const frame = useCurrentFrame();
  const { width } = useVideoConfig();

  const showFrom = frame < durationInFrames / 2;
  const isGlitching =
    frame > durationInFrames / 3 && frame < (durationInFrames * 2) / 3;

  const offsetX = isGlitching
    ? (random(`glitch-x-${Math.floor(frame / 2)}`) - 0.5) * 50
    : 0;

  const offsetY = isGlitching
    ? (random(`glitch-y-${Math.floor(frame / 2)}`) - 0.5) * 20
    : 0;

  return (
    <AbsoluteFill>
      {isGlitching ? (
        <>
          {/* RGB split effect */}
          <AbsoluteFill
            style={{
              mixBlendMode: 'screen',
              transform: `translate(${offsetX - 5}px, ${offsetY}px)`,
              opacity: 0.8,
            }}
          >
            <div style={{ filter: 'hue-rotate(0deg)' }}>
              {showFrom ? from : to}
            </div>
          </AbsoluteFill>
          <AbsoluteFill
            style={{
              mixBlendMode: 'screen',
              transform: `translate(${offsetX}px, ${offsetY}px)`,
              opacity: 0.8,
            }}
          >
            <div style={{ filter: 'hue-rotate(120deg)' }}>
              {showFrom ? from : to}
            </div>
          </AbsoluteFill>
          <AbsoluteFill
            style={{
              mixBlendMode: 'screen',
              transform: `translate(${offsetX + 5}px, ${offsetY}px)`,
              opacity: 0.8,
            }}
          >
            <div style={{ filter: 'hue-rotate(240deg)' }}>
              {showFrom ? from : to}
            </div>
          </AbsoluteFill>
        </>
      ) : (
        <AbsoluteFill>{showFrom ? from : to}</AbsoluteFill>
      )}
    </AbsoluteFill>
  );
};
```

---

## 10. Curtain Transition

Curtain opening/closing effect.

```typescript
import { useCurrentFrame, interpolate, AbsoluteFill, useVideoConfig } from 'remotion';

interface CurtainTransitionProps {
  from: React.ReactNode;
  to: React.ReactNode;
  durationInFrames: number;
}

export const CurtainTransition: React.FC<CurtainTransitionProps> = ({
  from,
  to,
  durationInFrames,
}) => {
  const frame = useCurrentFrame();
  const { width } = useVideoConfig();

  const curtainProgress = interpolate(
    frame,
    [0, durationInFrames],
    [0, width / 2],
    { extrapolateRight: 'clamp' }
  );

  return (
    <>
      <AbsoluteFill>{to}</AbsoluteFill>
      <AbsoluteFill>
        {/* Left curtain */}
        <div
          style={{
            position: 'absolute',
            left: 0,
            top: 0,
            width: width / 2 - curtainProgress,
            height: '100%',
            overflow: 'hidden',
          }}
        >
          <div style={{ width, height: '100%' }}>{from}</div>
        </div>
        {/* Right curtain */}
        <div
          style={{
            position: 'absolute',
            right: 0,
            top: 0,
            width: width / 2 - curtainProgress,
            height: '100%',
            overflow: 'hidden',
          }}
        >
          <div
            style={{
              width,
              height: '100%',
              transform: `translateX(-${width / 2 + curtainProgress}px)`,
            }}
          >
            {from}
          </div>
        </div>
      </AbsoluteFill>
    </>
  );
};
```

---

## Complete Example: Multi-Scene Video with Transitions

```typescript
import { Composition, Sequence, AbsoluteFill } from 'remotion';
import {
  FadeTransition,
  SlideTransition,
  ZoomTransition,
} from './Transitions';

const Scene1: React.FC = () => (
  <AbsoluteFill style={{ backgroundColor: '#3498db', justifyContent: 'center', alignItems: 'center' }}>
    <h1 style={{ color: 'white', fontSize: 100 }}>Scene 1</h1>
  </AbsoluteFill>
);

const Scene2: React.FC = () => (
  <AbsoluteFill style={{ backgroundColor: '#e74c3c', justifyContent: 'center', alignItems: 'center' }}>
    <h1 style={{ color: 'white', fontSize: 100 }}>Scene 2</h1>
  </AbsoluteFill>
);

const Scene3: React.FC = () => (
  <AbsoluteFill style={{ backgroundColor: '#2ecc71', justifyContent: 'center', alignItems: 'center' }}>
    <h1 style={{ color: 'white', fontSize: 100 }}>Scene 3</h1>
  </AbsoluteFill>
);

export const MultiSceneVideo: React.FC = () => {
  return (
    <AbsoluteFill>
      {/* Scene 1 with fade transition */}
      <Sequence from={0} durationInFrames={90}>
        <FadeTransition durationInFrames={90}>
          <Scene1 />
        </FadeTransition>
      </Sequence>

      {/* Scene 2 with slide transition */}
      <Sequence from={90} durationInFrames={90}>
        <SlideTransition durationInFrames={90} direction="left">
          <Scene2 />
        </SlideTransition>
      </Sequence>

      {/* Scene 3 with zoom transition */}
      <Sequence from={180} durationInFrames={90}>
        <FadeTransition durationInFrames={90}>
          <Scene3 />
        </FadeTransition>
      </Sequence>
    </AbsoluteFill>
  );
};

// Register composition
<Composition
  id="MultiSceneVideo"
  component={MultiSceneVideo}
  durationInFrames={270}
  fps={30}
  width={1920}
  height={1080}
/>
```

---

## Tips for Using Transitions

1. **Timing**: Keep transitions between 15-45 frames (0.5-1.5 seconds at 30fps)
2. **Consistency**: Use similar transitions throughout for cohesive feel
3. **Context**: Match transition style to content mood
4. **Performance**: Complex transitions may slow rendering
5. **Subtlety**: Sometimes a simple fade is best
6. **Testing**: Preview transitions at target frame rate

These transition templates provide professional scene changes. Mix, customize, and combine with your content for polished videos!
