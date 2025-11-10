# Graphic Animation Templates

Ready-to-use graphic and shape animation patterns for Remotion videos.

## 1. Animated Circle

Circle that grows and fades in.

```typescript
import { useCurrentFrame, interpolate, spring, useVideoConfig, AbsoluteFill } from 'remotion';

interface AnimatedCircleProps {
  color?: string;
  delay?: number;
}

export const AnimatedCircle: React.FC<AnimatedCircleProps> = ({
  color = '#3498db',
  delay = 0,
}) => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();
  const localFrame = Math.max(0, frame - delay);

  const scale = spring({
    frame: localFrame,
    fps,
    config: {
      damping: 20,
      stiffness: 100,
    },
  });

  const opacity = interpolate(localFrame, [0, 15], [0, 1], {
    extrapolateRight: 'clamp',
  });

  return (
    <AbsoluteFill
      style={{
        justifyContent: 'center',
        alignItems: 'center',
      }}
    >
      <div
        style={{
          width: 200,
          height: 200,
          borderRadius: '50%',
          backgroundColor: color,
          transform: `scale(${scale})`,
          opacity,
        }}
      />
    </AbsoluteFill>
  );
};
```

---

## 2. Rotating Square

Square that rotates continuously.

```typescript
import { useCurrentFrame, interpolate, AbsoluteFill } from 'remotion';

interface RotatingSquareProps {
  size?: number;
  color?: string;
  speed?: number;
}

export const RotatingSquare: React.FC<RotatingSquareProps> = ({
  size = 200,
  color = '#e74c3c',
  speed = 1,
}) => {
  const frame = useCurrentFrame();

  const rotation = interpolate(frame, [0, 60], [0, 360 * speed]);

  return (
    <AbsoluteFill
      style={{
        justifyContent: 'center',
        alignItems: 'center',
      }}
    >
      <div
        style={{
          width: size,
          height: size,
          backgroundColor: color,
          transform: `rotate(${rotation}deg)`,
        }}
      />
    </AbsoluteFill>
  );
};
```

---

## 3. Morphing Shapes

Shape that morphs between different forms.

```typescript
import { useCurrentFrame, interpolate, AbsoluteFill } from 'remotion';

export const MorphingShape: React.FC = () => {
  const frame = useCurrentFrame();

  // Morph between 0% (square) and 50% (circle)
  const borderRadius = interpolate(frame, [0, 30, 60, 90], [0, 50, 0, 50], {
    extrapolateRight: 'clamp',
  });

  // Change size
  const size = interpolate(frame, [0, 30, 60, 90], [100, 200, 100, 200], {
    extrapolateRight: 'clamp',
  });

  // Change color
  const hue = interpolate(frame, [0, 90], [0, 360]);

  return (
    <AbsoluteFill
      style={{
        justifyContent: 'center',
        alignItems: 'center',
        backgroundColor: '#1a1a1a',
      }}
    >
      <div
        style={{
          width: size,
          height: size,
          backgroundColor: `hsl(${hue}, 70%, 50%)`,
          borderRadius: `${borderRadius}%`,
          transition: 'all 0.1s ease',
        }}
      />
    </AbsoluteFill>
  );
};
```

---

## 4. Particle System

Animated particles floating around.

```typescript
import { useCurrentFrame, random, AbsoluteFill, useVideoConfig } from 'remotion';

interface Particle {
  x: number;
  y: number;
  vx: number;
  vy: number;
  size: number;
  color: string;
}

interface ParticleSystemProps {
  count?: number;
}

export const ParticleSystem: React.FC<ParticleSystemProps> = ({
  count = 50,
}) => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();

  const particles: Particle[] = Array.from({ length: count }).map((_, i) => ({
    x: random(`x-${i}`) * width,
    y: random(`y-${i}`) * height,
    vx: (random(`vx-${i}`) - 0.5) * 2,
    vy: (random(`vy-${i}`) - 0.5) * 2,
    size: random(`size-${i}`) * 10 + 5,
    color: `hsl(${random(`color-${i}`) * 360}, 70%, 60%)`,
  }));

  return (
    <AbsoluteFill style={{ backgroundColor: '#000' }}>
      {particles.map((particle, i) => {
        const x = particle.x + particle.vx * frame;
        const y = particle.y + particle.vy * frame;

        // Wrap around screen
        const wrappedX = ((x % width) + width) % width;
        const wrappedY = ((y % height) + height) % height;

        return (
          <div
            key={i}
            style={{
              position: 'absolute',
              left: wrappedX,
              top: wrappedY,
              width: particle.size,
              height: particle.size,
              borderRadius: '50%',
              backgroundColor: particle.color,
              opacity: 0.8,
            }}
          />
        );
      })}
    </AbsoluteFill>
  );
};
```

---

## 5. Wave Animation

Animated sine wave pattern.

```typescript
import { useCurrentFrame, AbsoluteFill, useVideoConfig } from 'remotion';

interface WaveAnimationProps {
  amplitude?: number;
  frequency?: number;
  speed?: number;
  color?: string;
}

export const WaveAnimation: React.FC<WaveAnimationProps> = ({
  amplitude = 100,
  frequency = 0.02,
  speed = 0.1,
  color = '#3498db',
}) => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();

  const points = Array.from({ length: 100 }).map((_, i) => {
    const x = (i / 100) * width;
    const y =
      height / 2 +
      Math.sin((i * frequency + frame * speed)) * amplitude;
    return { x, y };
  });

  const pathData = points
    .map((p, i) => `${i === 0 ? 'M' : 'L'} ${p.x} ${p.y}`)
    .join(' ');

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a1a' }}>
      <svg width={width} height={height}>
        <path
          d={pathData}
          stroke={color}
          strokeWidth={4}
          fill="none"
          strokeLinecap="round"
        />
      </svg>
    </AbsoluteFill>
  );
};
```

---

## 6. Progress Bar

Animated progress bar filling up.

```typescript
import { useCurrentFrame, interpolate, AbsoluteFill } from 'remotion';

interface ProgressBarProps {
  label?: string;
  duration?: number;
  color?: string;
}

export const ProgressBar: React.FC<ProgressBarProps> = ({
  label = 'Loading...',
  duration = 60,
  color = '#2ecc71',
}) => {
  const frame = useCurrentFrame();

  const progress = interpolate(frame, [0, duration], [0, 100], {
    extrapolateRight: 'clamp',
  });

  return (
    <AbsoluteFill
      style={{
        justifyContent: 'center',
        alignItems: 'center',
        backgroundColor: '#1a1a1a',
      }}
    >
      <div style={{ width: 600 }}>
        <div style={{ color: '#fff', marginBottom: 10, fontSize: 24 }}>
          {label}
        </div>
        <div
          style={{
            width: '100%',
            height: 40,
            backgroundColor: '#333',
            borderRadius: 20,
            overflow: 'hidden',
          }}
        >
          <div
            style={{
              width: `${progress}%`,
              height: '100%',
              backgroundColor: color,
              transition: 'width 0.1s',
              display: 'flex',
              justifyContent: 'center',
              alignItems: 'center',
              color: '#fff',
              fontWeight: 'bold',
            }}
          >
            {Math.round(progress)}%
          </div>
        </div>
      </div>
    </AbsoluteFill>
  );
};
```

---

## 7. Circular Progress

Animated circular progress indicator.

```typescript
import { useCurrentFrame, interpolate, AbsoluteFill } from 'remotion';

interface CircularProgressProps {
  size?: number;
  strokeWidth?: number;
  duration?: number;
  color?: string;
}

export const CircularProgress: React.FC<CircularProgressProps> = ({
  size = 200,
  strokeWidth = 20,
  duration = 90,
  color = '#9b59b6',
}) => {
  const frame = useCurrentFrame();

  const progress = interpolate(frame, [0, duration], [0, 1], {
    extrapolateRight: 'clamp',
  });

  const radius = (size - strokeWidth) / 2;
  const circumference = radius * 2 * Math.PI;
  const offset = circumference - progress * circumference;

  return (
    <AbsoluteFill
      style={{
        justifyContent: 'center',
        alignItems: 'center',
        backgroundColor: '#1a1a1a',
      }}
    >
      <svg width={size} height={size}>
        {/* Background circle */}
        <circle
          cx={size / 2}
          cy={size / 2}
          r={radius}
          stroke="#333"
          strokeWidth={strokeWidth}
          fill="none"
        />
        {/* Progress circle */}
        <circle
          cx={size / 2}
          cy={size / 2}
          r={radius}
          stroke={color}
          strokeWidth={strokeWidth}
          fill="none"
          strokeDasharray={circumference}
          strokeDashoffset={offset}
          transform={`rotate(-90 ${size / 2} ${size / 2})`}
          strokeLinecap="round"
        />
        {/* Percentage text */}
        <text
          x={size / 2}
          y={size / 2}
          textAnchor="middle"
          dy="0.3em"
          fontSize={40}
          fill="#fff"
          fontWeight="bold"
        >
          {Math.round(progress * 100)}%
        </text>
      </svg>
    </AbsoluteFill>
  );
};
```

---

## 8. Ripple Effect

Expanding ripples from center.

```typescript
import { useCurrentFrame, interpolate, AbsoluteFill, useVideoConfig } from 'remotion';

interface RippleEffectProps {
  rippleCount?: number;
  color?: string;
}

export const RippleEffect: React.FC<RippleEffectProps> = ({
  rippleCount = 3,
  color = '#3498db',
}) => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();

  return (
    <AbsoluteFill
      style={{
        justifyContent: 'center',
        alignItems: 'center',
        backgroundColor: '#1a1a1a',
      }}
    >
      {Array.from({ length: rippleCount }).map((_, i) => {
        const delay = i * 20;
        const localFrame = Math.max(0, frame - delay);

        const scale = interpolate(localFrame, [0, 60], [0, 3], {
          extrapolateRight: 'clamp',
        });

        const opacity = interpolate(localFrame, [0, 20, 60], [0, 0.8, 0], {
          extrapolateRight: 'clamp',
        });

        return (
          <div
            key={i}
            style={{
              position: 'absolute',
              width: 200,
              height: 200,
              borderRadius: '50%',
              border: `4px solid ${color}`,
              transform: `scale(${scale})`,
              opacity,
            }}
          />
        );
      })}
    </AbsoluteFill>
  );
};
```

---

## 9. Spiral Animation

Animated spiral pattern.

```typescript
import { useCurrentFrame, AbsoluteFill, useVideoConfig } from 'remotion';

export const SpiralAnimation: React.FC = () => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();

  const centerX = width / 2;
  const centerY = height / 2;
  const points = 100;

  return (
    <AbsoluteFill style={{ backgroundColor: '#000' }}>
      {Array.from({ length: points }).map((_, i) => {
        const angle = (i / points) * Math.PI * 4 + frame * 0.05;
        const radius = (i / points) * 300;

        const x = centerX + Math.cos(angle) * radius;
        const y = centerY + Math.sin(angle) * radius;

        const hue = (i / points) * 360;

        return (
          <div
            key={i}
            style={{
              position: 'absolute',
              left: x,
              top: y,
              width: 10,
              height: 10,
              borderRadius: '50%',
              backgroundColor: `hsl(${hue}, 70%, 60%)`,
            }}
          />
        );
      })}
    </AbsoluteFill>
  );
};
```

---

## 10. Grid Animation

Animated grid of tiles.

```typescript
import { useCurrentFrame, interpolate, spring, useVideoConfig, AbsoluteFill } from 'remotion';

interface GridAnimationProps {
  rows?: number;
  cols?: number;
}

export const GridAnimation: React.FC<GridAnimationProps> = ({
  rows = 8,
  cols = 12,
}) => {
  const frame = useCurrentFrame();
  const { width, height, fps } = useVideoConfig();

  const tileWidth = width / cols;
  const tileHeight = height / rows;

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a1a' }}>
      {Array.from({ length: rows * cols }).map((_, index) => {
        const row = Math.floor(index / cols);
        const col = index % cols;

        // Stagger animation based on position
        const delay = (row + col) * 2;
        const localFrame = Math.max(0, frame - delay);

        const scale = spring({
          frame: localFrame,
          fps,
          config: {
            damping: 20,
            stiffness: 100,
          },
        });

        const opacity = interpolate(localFrame, [0, 15], [0, 1], {
          extrapolateRight: 'clamp',
        });

        const hue = ((row + col) / (rows + cols)) * 360;

        return (
          <div
            key={index}
            style={{
              position: 'absolute',
              left: col * tileWidth,
              top: row * tileHeight,
              width: tileWidth,
              height: tileHeight,
              display: 'flex',
              justifyContent: 'center',
              alignItems: 'center',
              padding: 5,
            }}
          >
            <div
              style={{
                width: '100%',
                height: '100%',
                backgroundColor: `hsl(${hue}, 60%, 50%)`,
                transform: `scale(${scale})`,
                opacity,
                borderRadius: 5,
              }}
            />
          </div>
        );
      })}
    </AbsoluteFill>
  );
};
```

---

## 11. DNA Helix

Rotating DNA helix animation.

```typescript
import { useCurrentFrame, AbsoluteFill, useVideoConfig } from 'remotion';

export const DNAHelix: React.FC = () => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();

  const centerX = width / 2;
  const centerY = height / 2;
  const points = 30;

  return (
    <AbsoluteFill style={{ backgroundColor: '#000' }}>
      <svg width={width} height={height}>
        {Array.from({ length: points }).map((_, i) => {
          const y = (i / points) * height;
          const angle = (i / points) * Math.PI * 4 + frame * 0.05;

          const x1 = centerX + Math.cos(angle) * 150;
          const x2 = centerX - Math.cos(angle) * 150;

          const z1 = Math.sin(angle);
          const z2 = -Math.sin(angle);

          return (
            <g key={i}>
              {/* Left strand */}
              <circle
                cx={x1}
                cy={y}
                r={8}
                fill={z1 > 0 ? '#3498db' : '#2980b9'}
                opacity={0.8}
              />
              {/* Right strand */}
              <circle
                cx={x2}
                cy={y}
                r={8}
                fill={z2 > 0 ? '#e74c3c' : '#c0392b'}
                opacity={0.8}
              />
              {/* Connection line */}
              {Math.abs(z1) < 0.3 && (
                <line
                  x1={x1}
                  y1={y}
                  x2={x2}
                  y2={y}
                  stroke="#95a5a6"
                  strokeWidth={2}
                  opacity={0.5}
                />
              )}
            </g>
          );
        })}
      </svg>
    </AbsoluteFill>
  );
};
```

---

## 12. Bouncing Ball

Physics-based bouncing ball.

```typescript
import { useCurrentFrame, AbsoluteFill, useVideoConfig } from 'remotion';

export const BouncingBall: React.FC = () => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();

  const gravity = 0.5;
  const initialVelocity = -15;
  const damping = 0.8;

  let y = 0;
  let velocity = initialVelocity;
  let currentFrame = frame;

  while (currentFrame > 0) {
    velocity += gravity;
    y += velocity;

    if (y >= height - 100) {
      y = height - 100;
      velocity = -velocity * damping;
    }

    currentFrame--;
  }

  const x = (frame * 5) % width;

  return (
    <AbsoluteFill style={{ backgroundColor: '#ecf0f1' }}>
      {/* Ground */}
      <div
        style={{
          position: 'absolute',
          bottom: 0,
          width: '100%',
          height: 50,
          backgroundColor: '#34495e',
        }}
      />
      {/* Ball */}
      <div
        style={{
          position: 'absolute',
          left: x,
          top: y,
          width: 50,
          height: 50,
          borderRadius: '50%',
          backgroundColor: '#e74c3c',
          boxShadow: '0 10px 30px rgba(0,0,0,0.3)',
        }}
      />
    </AbsoluteFill>
  );
};
```

---

## Usage Example

Combine graphic animations in a showcase:

```typescript
import { Composition, Sequence, AbsoluteFill } from 'remotion';
import {
  AnimatedCircle,
  ParticleSystem,
  WaveAnimation,
  GridAnimation,
} from './GraphicAnimations';

export const GraphicShowcase: React.FC = () => {
  return (
    <AbsoluteFill>
      <Sequence from={0} durationInFrames={60}>
        <AnimatedCircle color="#3498db" />
      </Sequence>

      <Sequence from={60} durationInFrames={90}>
        <ParticleSystem count={100} />
      </Sequence>

      <Sequence from={150} durationInFrames={90}>
        <WaveAnimation amplitude={150} />
      </Sequence>

      <Sequence from={240} durationInFrames={120}>
        <GridAnimation rows={6} cols={10} />
      </Sequence>
    </AbsoluteFill>
  );
};
```

These templates provide a foundation for creating stunning graphic animations. Customize colors, sizes, speeds, and combine with text for complete compositions!
