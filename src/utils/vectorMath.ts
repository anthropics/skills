/**
 * Advanced 3D Vector Mathematics for Biomechanical Analysis
 * Based on classical mechanics and piano pedagogy research
 */

export interface Vector3D {
  x: number;
  y: number;
  z: number;
}

export interface Point3D extends Vector3D {}

/**
 * Exponential Moving Average Filter
 * Reduces jitter while maintaining responsiveness
 */
export class EMAFilter {
  private prevValue: number | null = null;
  private alpha: number;

  /**
   * @param alpha - Smoothing factor (0-1). Higher = more responsive, lower = smoother
   * Default 0.7 balances latency and stability for hand tracking
   */
  constructor(alpha = 0.7) {
    this.alpha = Math.max(0, Math.min(1, alpha));
  }

  filter(value: number): number {
    if (this.prevValue === null) {
      this.prevValue = value;
      return value;
    }
    this.prevValue = this.alpha * value + (1 - this.alpha) * this.prevValue;
    return this.prevValue;
  }

  reset(): void {
    this.prevValue = null;
  }
}

/**
 * Multi-dimensional EMA filter for landmark coordinates
 */
export class LandmarkFilter {
  private xFilter: EMAFilter;
  private yFilter: EMAFilter;
  private zFilter: EMAFilter;

  constructor(alpha = 0.7) {
    this.xFilter = new EMAFilter(alpha);
    this.yFilter = new EMAFilter(alpha);
    this.zFilter = new EMAFilter(alpha);
  }

  filter(point: number[]): number[] {
    return [
      this.xFilter.filter(point[0]),
      this.yFilter.filter(point[1]),
      this.zFilter.filter(point[2] || 0),
    ];
  }

  reset(): void {
    this.xFilter.reset();
    this.yFilter.reset();
    this.zFilter.reset();
  }
}

/**
 * Calculate 3D angle between three points using dot product
 * Returns angle in degrees at vertex point p2
 *
 * Mathematical foundation:
 * cos(θ) = (v1 · v2) / (|v1| |v2|)
 * where v1 = p1 - p2, v2 = p3 - p2
 *
 * @param p1 - First point (e.g., MCP joint)
 * @param p2 - Vertex point (e.g., PIP joint - where angle is measured)
 * @param p3 - Third point (e.g., DIP joint)
 * @returns Angle in degrees (0-180)
 */
export function calculate3DAngle(p1: number[], p2: number[], p3: number[]): number {
  // Vector from p2 to p1
  const v1x = p1[0] - p2[0];
  const v1y = p1[1] - p2[1];
  const v1z = (p1[2] || 0) - (p2[2] || 0);

  // Vector from p2 to p3
  const v2x = p3[0] - p2[0];
  const v2y = p3[1] - p2[1];
  const v2z = (p3[2] || 0) - (p2[2] || 0);

  // Dot product
  const dot = v1x * v2x + v1y * v2y + v1z * v2z;

  // Magnitudes
  const mag1 = Math.sqrt(v1x * v1x + v1y * v1y + v1z * v1z);
  const mag2 = Math.sqrt(v2x * v2x + v2y * v2y + v2z * v2z);

  // Prevent division by zero
  if (mag1 * mag2 === 0) return 0;

  // Clamp to prevent floating point errors in acos
  const cosine = Math.max(-1, Math.min(1, dot / (mag1 * mag2)));

  // Return in degrees
  return Math.acos(cosine) * (180 / Math.PI);
}

/**
 * Calculate Euclidean distance between two 3D points
 */
export function distance3D(p1: number[], p2: number[]): number {
  const dx = p1[0] - p2[0];
  const dy = p1[1] - p2[1];
  const dz = (p1[2] || 0) - (p2[2] || 0);
  return Math.sqrt(dx * dx + dy * dy + dz * dz);
}

/**
 * Calculate palm width for normalization
 * Uses the distance from wrist (0) to middle finger MCP (9)
 *
 * This "palm unit" makes all measurements scale-invariant
 * (works regardless of distance from camera)
 */
export function calculatePalmWidth(landmarks: number[][]): number {
  const wrist = landmarks[0];
  const middleMCP = landmarks[9];
  return distance3D(wrist, middleMCP);
}

/**
 * Normalize a distance measurement by palm width
 * Returns a dimensionless ratio (units of "palm widths")
 *
 * Example: If finger tip is 1.5 palm widths away from wrist,
 * this returns 1.5 regardless of camera distance
 */
export function normalizeDistance(rawDistance: number, palmWidth: number): number {
  if (palmWidth === 0) return 0;
  return rawDistance / palmWidth;
}

/**
 * Calculate cross product of two 3D vectors
 * Used for detecting hyperextension (finger collapse)
 *
 * Returns a vector perpendicular to both input vectors
 */
export function crossProduct(v1: Vector3D, v2: Vector3D): Vector3D {
  return {
    x: v1.y * v2.z - v1.z * v2.y,
    y: v1.z * v2.x - v1.x * v2.z,
    z: v1.x * v2.y - v1.y * v2.x,
  };
}

/**
 * Calculate magnitude (length) of a 3D vector
 */
export function magnitude(v: Vector3D): number {
  return Math.sqrt(v.x * v.x + v.y * v.y + v.z * v.z);
}

/**
 * Detect if a finger joint is hyperextended (collapsed backward)
 * Uses cross product to determine if joint bends in wrong direction
 *
 * @returns true if joint is hyperextended (dangerous)
 */
export function isHyperextended(p1: number[], p2: number[], p3: number[], p4: number[]): boolean {
  // Calculate two consecutive bone vectors
  const bone1: Vector3D = {
    x: p2[0] - p1[0],
    y: p2[1] - p1[1],
    z: (p2[2] || 0) - (p1[2] || 0),
  };

  const bone2: Vector3D = {
    x: p3[0] - p2[0],
    y: p3[1] - p2[1],
    z: (p3[2] || 0) - (p2[2] || 0),
  };

  const bone3: Vector3D = {
    x: p4[0] - p3[0],
    y: p4[1] - p3[1],
    z: (p4[2] || 0) - (p3[2] || 0),
  };

  // Calculate normal vectors at each joint
  const normal1 = crossProduct(bone1, bone2);
  const normal2 = crossProduct(bone2, bone3);

  // If normals point in opposite directions, joint is collapsed
  const dotProduct = normal1.x * normal2.x + normal1.y * normal2.y + normal1.z * normal2.z;

  return dotProduct < 0;
}

/**
 * Linear interpolation between two values
 */
export function lerp(a: number, b: number, t: number): number {
  return a + (b - a) * Math.max(0, Math.min(1, t));
}

/**
 * Map value from one range to another
 */
export function mapRange(
  value: number,
  inMin: number,
  inMax: number,
  outMin: number,
  outMax: number
): number {
  return outMin + ((value - inMin) * (outMax - outMin)) / (inMax - inMin);
}
