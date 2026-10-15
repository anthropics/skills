/**
 * Type definitions for ml5.js
 * ml5.js is a high-level interface for TensorFlow.js
 */

declare module 'ml5' {
  export interface HandposeOptions {
    flipHorizontal?: boolean;
    maxContinuousChecks?: number;
    detectionConfidence?: number;
    scoreThreshold?: number;
    iouThreshold?: number;
  }

  export interface HandposePrediction {
    landmarks: number[][];
    handedness?: 'Left' | 'Right';
    handInViewConfidence?: number;
    boundingBox?: {
      topLeft: [number, number];
      bottomRight: [number, number];
    };
  }

  export interface HandposeModel {
    predict(): Promise<HandposePrediction[]>;
  }

  export function handpose(
    videoOrCanvas: HTMLVideoElement | HTMLCanvasElement,
    options?: HandposeOptions
  ): Promise<HandposeModel>;

  const ml5: {
    handpose: typeof handpose;
  };

  export default ml5;
}
