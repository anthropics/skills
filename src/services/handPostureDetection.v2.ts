/* eslint-disable max-lines */
/**
 * Advanced Hand Posture Detection Service - Version 2.0
 * Implements biomechanically accurate analysis using 3D vector mathematics
 *
 * Based on:
 * - Classical piano pedagogy (Leschetizky, Taubman methods)
 * - Biomechanical research on repetitive strain injury (RSI) prevention
 * - MediaPipe Hands 21-landmark model
 */

import {
  calculate3DAngle,
  distance3D,
  calculatePalmWidth,
  normalizeDistance,
  isHyperextended,
  LandmarkFilter,
} from '../utils/vectorMath';

export interface HandLandmarks {
  keypoints: number[][]; // Array of [x, y, z] coordinates for each hand landmark
  handedness: 'Left' | 'Right';
  confidence: number;
}

export interface PostureAnalysis {
  isCorrect: boolean;
  score: number; // 0-100
  issues: PostureIssue[];
  recommendations: string[];
  metrics: PostureMetrics;
}

export interface PostureMetrics {
  // Finger curvature angles (degrees) - indexed by finger
  fingerAngles: {
    thumb: number[];
    index: number[];
    middle: number[];
    ring: number[];
    pinky: number[];
  };
  // Wrist metrics
  wristHeight: number; // Normalized units
  wristAngle: number; // Degrees
  // Palm metrics
  palmArch: number; // Normalized units
  handSpan: number; // Normalized units
  // Overall biomechanics
  palmWidth: number; // Base unit for normalization
  hyperextensionDetected: boolean;
}

export interface PostureIssue {
  type: 'wrist' | 'fingers' | 'palm' | 'thumb' | 'hyperextension';
  severity: 'low' | 'medium' | 'high' | 'critical';
  message: string;
  suggestedFix: string;
  affectedFingers?: string[]; // e.g., ['index', 'middle']
}

/**
 * Hand landmark indices (MediaPipe Hands standard)
 * https://google.github.io/mediapipe/solutions/hands.html
 */
export const LANDMARK_INDICES = {
  WRIST: 0,
  THUMB_CMC: 1,
  THUMB_MCP: 2,
  THUMB_IP: 3,
  THUMB_TIP: 4,
  INDEX_MCP: 5,
  INDEX_PIP: 6,
  INDEX_DIP: 7,
  INDEX_TIP: 8,
  MIDDLE_MCP: 9,
  MIDDLE_PIP: 10,
  MIDDLE_DIP: 11,
  MIDDLE_TIP: 12,
  RING_MCP: 13,
  RING_PIP: 14,
  RING_DIP: 15,
  RING_TIP: 16,
  PINKY_MCP: 17,
  PINKY_PIP: 18,
  PINKY_DIP: 19,
  PINKY_TIP: 20,
} as const;

/**
 * Biomechanically validated thresholds for posture analysis
 * Based on ergonomic research and piano pedagogy literature
 */
export const POSTURE_THRESHOLDS = {
  // Finger curvature (degrees at PIP joint)
  FINGER_FLAT: 160, // Above this = flat finger (poor technique)
  FINGER_IDEAL_MIN: 100, // Minimum for good curvature
  FINGER_IDEAL_MAX: 140, // Maximum for good curvature
  FINGER_TENSE: 70, // Below this = excessive tension

  // Wrist alignment
  WRIST_LOW_THRESHOLD: -0.15, // Normalized units (wrist below knuckles)
  WRIST_HIGH_THRESHOLD: 0.25, // Normalized units (wrist too elevated)

  // Palm arch
  PALM_COLLAPSED: 0.5, // Palm too flat
  PALM_IDEAL: 0.7, // Good arch

  // Thumb position
  THUMB_TUCKED: 0.6, // Too close to fingers
  THUMB_EXTENDED: 1.9, // Too far from fingers
} as const;

/**
 * Advanced Hand Posture Analyzer with 3D Vector Math
 */
export class HandPostureAnalyzerV2 {
  private static landmarkFilters: Map<number, LandmarkFilter> = new Map();

  /**
   * Initialize filters for smoothing (call once per hand tracking session)
   */
  static initializeFilters(alpha = 0.7): void {
    this.landmarkFilters.clear();
    for (let i = 0; i < 21; i++) {
      this.landmarkFilters.set(i, new LandmarkFilter(alpha));
    }
  }

  /**
   * Reset all filters (call when hand tracking is lost)
   */
  static resetFilters(): void {
    this.landmarkFilters.forEach(filter => filter.reset());
  }

  /**
   * Apply EMA filtering to landmarks to reduce jitter
   */
  static filterLandmarks(landmarks: number[][]): number[][] {
    return landmarks.map((point, index) => {
      const filter = this.landmarkFilters.get(index);
      return filter ? filter.filter(point) : point;
    });
  }

  /**
   * Main analysis function - analyzes complete hand posture
   */
  static analyzePosture(landmarks: HandLandmarks): PostureAnalysis {
    // Apply smoothing filter
    const filteredKeypoints = this.filterLandmarks(landmarks.keypoints);

    // Calculate base measurement for normalization
    const palmWidth = calculatePalmWidth(filteredKeypoints);

    // Calculate detailed metrics
    const metrics = this.calculateMetrics(filteredKeypoints, palmWidth);

    // Detect issues
    const issues: PostureIssue[] = [];
    let score = 100;

    // Analyze wrist
    const wristAnalysis = this.analyzeWrist(filteredKeypoints, palmWidth, metrics);
    if (!wristAnalysis.isCorrect) {
      issues.push(wristAnalysis.issue!);
      score -= wristAnalysis.penalty;
    }

    // Analyze finger curvature
    const fingerAnalysis = this.analyzeFingerCurvature(filteredKeypoints, metrics);
    if (!fingerAnalysis.isCorrect) {
      issues.push(...fingerAnalysis.issues);
      score -= fingerAnalysis.penalty;
    }

    // Analyze palm position
    const palmAnalysis = this.analyzePalmPosition(filteredKeypoints, palmWidth, metrics);
    if (!palmAnalysis.isCorrect) {
      issues.push(palmAnalysis.issue!);
      score -= palmAnalysis.penalty;
    }

    // Analyze thumb
    const thumbAnalysis = this.analyzeThumbPosition(filteredKeypoints, palmWidth, metrics);
    if (!thumbAnalysis.isCorrect) {
      issues.push(thumbAnalysis.issue!);
      score -= thumbAnalysis.penalty;
    }

    // Check for hyperextension (critical issue)
    if (metrics.hyperextensionDetected) {
      issues.push({
        type: 'hyperextension',
        severity: 'critical',
        message: 'Hiperextensão detectada - RISCO DE LESÃO',
        suggestedFix:
          'Pare imediatamente. Relaxe completamente as mãos. Consulte um professor de piano para corrigir a técnica antes de continuar.',
        affectedFingers: this.detectHyperextendedFingers(filteredKeypoints),
      });
      score = Math.min(score, 30); // Cap score at 30 if hyperextension detected
    }

    // Generate recommendations
    const recommendations = this.generateRecommendations(issues, metrics);

    return {
      isCorrect: issues.length === 0,
      score: Math.max(0, Math.min(100, score)),
      issues,
      recommendations,
      metrics,
    };
  }

  /**
   * Calculate comprehensive metrics about hand posture
   */
  private static calculateMetrics(keypoints: number[][], palmWidth: number): PostureMetrics {
    const { WRIST, INDEX_MCP, MIDDLE_MCP, RING_MCP, PINKY_MCP } = LANDMARK_INDICES;

    // Calculate finger angles
    const fingerAngles = {
      thumb: this.calculateFingerAngles(keypoints, 1), // Thumb (different structure)
      index: this.calculateFingerAngles(keypoints, 5), // Index
      middle: this.calculateFingerAngles(keypoints, 9), // Middle
      ring: this.calculateFingerAngles(keypoints, 13), // Ring
      pinky: this.calculateFingerAngles(keypoints, 17), // Pinky
    };

    // Wrist height relative to knuckles (normalized)
    const mcpY =
      (keypoints[INDEX_MCP][1] +
        keypoints[MIDDLE_MCP][1] +
        keypoints[RING_MCP][1] +
        keypoints[PINKY_MCP][1]) /
      4;
    const wristHeight = normalizeDistance(keypoints[WRIST][1] - mcpY, palmWidth);

    // Wrist angle (alignment with forearm)
    // Approximated using wrist and middle MCP
    const wristAngle = calculate3DAngle(
      keypoints[INDEX_MCP],
      keypoints[WRIST],
      keypoints[MIDDLE_MCP]
    );

    // Palm arch (distance from wrist to midpoint of knuckles)
    const palmCenterX = (keypoints[INDEX_MCP][0] + keypoints[PINKY_MCP][0]) / 2;
    const palmCenterY = (keypoints[INDEX_MCP][1] + keypoints[PINKY_MCP][1]) / 2;
    const palmCenterZ = ((keypoints[INDEX_MCP][2] || 0) + (keypoints[PINKY_MCP][2] || 0)) / 2;
    const palmCenter = [palmCenterX, palmCenterY, palmCenterZ];
    const palmArch = normalizeDistance(distance3D(keypoints[WRIST], palmCenter), palmWidth);

    // Hand span (index to pinky MCP distance)
    const handSpan = normalizeDistance(
      distance3D(keypoints[INDEX_MCP], keypoints[PINKY_MCP]),
      palmWidth
    );

    // Hyperextension detection
    const hyperextensionDetected = this.detectHyperextension(keypoints);

    return {
      fingerAngles,
      wristHeight,
      wristAngle,
      palmArch,
      handSpan,
      palmWidth,
      hyperextensionDetected,
    };
  }

  /**
   * Calculate angles at each joint for a finger
   * @param baseIndex - MCP joint index (5 for index, 9 for middle, etc.)
   */
  private static calculateFingerAngles(keypoints: number[][], baseIndex: number): number[] {
    const angles: number[] = [];

    // For regular fingers (not thumb): calculate MCP, PIP, DIP angles
    if (baseIndex >= 5) {
      // PIP angle (most important for posture)
      const pipAngle = calculate3DAngle(
        keypoints[baseIndex], // MCP
        keypoints[baseIndex + 1], // PIP
        keypoints[baseIndex + 2] // DIP
      );
      angles.push(pipAngle);

      // DIP angle
      const dipAngle = calculate3DAngle(
        keypoints[baseIndex + 1], // PIP
        keypoints[baseIndex + 2], // DIP
        keypoints[baseIndex + 3] // TIP
      );
      angles.push(dipAngle);
    } else {
      // Thumb has different structure (no middle phalanx)
      const thumbAngle = calculate3DAngle(
        keypoints[baseIndex], // CMC
        keypoints[baseIndex + 1], // MCP
        keypoints[baseIndex + 2] // IP
      );
      angles.push(thumbAngle);
    }

    return angles;
  }

  /**
   * Detect hyperextension in any finger
   */
  private static detectHyperextension(keypoints: number[][]): boolean {
    const fingers = [
      [5, 6, 7, 8], // Index
      [9, 10, 11, 12], // Middle
      [13, 14, 15, 16], // Ring
      [17, 18, 19, 20], // Pinky
    ];

    for (const finger of fingers) {
      if (
        isHyperextended(
          keypoints[finger[0]],
          keypoints[finger[1]],
          keypoints[finger[2]],
          keypoints[finger[3]]
        )
      ) {
        return true;
      }
    }

    return false;
  }

  /**
   * Identify which fingers are hyperextended
   */
  private static detectHyperextendedFingers(keypoints: number[][]): string[] {
    const affected: string[] = [];
    const fingers: [string, number[]][] = [
      ['Indicador', [5, 6, 7, 8]],
      ['Médio', [9, 10, 11, 12]],
      ['Anelar', [13, 14, 15, 16]],
      ['Mínimo', [17, 18, 19, 20]],
    ];

    for (const [name, indices] of fingers) {
      if (
        isHyperextended(
          keypoints[indices[0]],
          keypoints[indices[1]],
          keypoints[indices[2]],
          keypoints[indices[3]]
        )
      ) {
        affected.push(name);
      }
    }

    return affected;
  }

  /**
   * Analyze wrist position and alignment
   */
  private static analyzeWrist(
    _keypoints: number[][],
    _palmWidth: number,
    metrics: PostureMetrics
  ): { isCorrect: boolean; issue?: PostureIssue; penalty: number } {
    const { wristHeight } = metrics;

    if (wristHeight < POSTURE_THRESHOLDS.WRIST_LOW_THRESHOLD) {
      return {
        isCorrect: false,
        penalty: 30,
        issue: {
          type: 'wrist',
          severity: 'high',
          message: 'Pulso muito baixo - Risco de lesão no túnel do carpo',
          suggestedFix:
            'Eleve o pulso até o nível dos dedos. Imagine uma linha reta do cotovelo até as pontas dos dedos. Use um apoio de pulso se necessário durante o treino inicial.',
        },
      };
    }

    if (wristHeight > POSTURE_THRESHOLDS.WRIST_HIGH_THRESHOLD) {
      return {
        isCorrect: false,
        penalty: 15,
        issue: {
          type: 'wrist',
          severity: 'medium',
          message: 'Pulso muito alto - Tensão desnecessária',
          suggestedFix:
            'Abaixe levemente o pulso. Mantenha-o relaxado e fluido, permitindo movimentos naturais. Evite rigidez.',
        },
      };
    }

    return { isCorrect: true, penalty: 0 };
  }

  /**
   * Analyze finger curvature across all fingers
   */
  private static analyzeFingerCurvature(
    _keypoints: number[][],
    metrics: PostureMetrics
  ): { isCorrect: boolean; issues: PostureIssue[]; penalty: number } {
    const issues: PostureIssue[] = [];
    let penalty = 0;

    const fingers: [string, keyof typeof metrics.fingerAngles][] = [
      ['Indicador', 'index'],
      ['Médio', 'middle'],
      ['Anelar', 'ring'],
      ['Mínimo', 'pinky'],
    ];

    const affectedFlat: string[] = [];
    const affectedTense: string[] = [];

    for (const [name, key] of fingers) {
      const angles = metrics.fingerAngles[key];
      const pipAngle = angles[0]; // Primary joint for analysis

      if (pipAngle > POSTURE_THRESHOLDS.FINGER_FLAT) {
        affectedFlat.push(name);
      } else if (pipAngle < POSTURE_THRESHOLDS.FINGER_TENSE) {
        affectedTense.push(name);
      }
    }

    if (affectedFlat.length > 0) {
      issues.push({
        type: 'fingers',
        severity: 'high',
        message: `Dedos muito retos: ${affectedFlat.join(', ')}`,
        suggestedFix:
          'Curve os dedos naturalmente, como se estivesse segurando uma bola de tênis. A curvatura deve ser relaxada, não forçada. Pratique exercícios de Hanon com foco em manter a forma.',
        affectedFingers: affectedFlat,
      });
      penalty += affectedFlat.length * 6;
    }

    if (affectedTense.length > 0) {
      issues.push({
        type: 'fingers',
        severity: 'medium',
        message: `Dedos muito curvados (tensão): ${affectedTense.join(', ')}`,
        suggestedFix:
          'Relaxe os dedos. A curvatura ideal é natural, não forçada. Faça exercícios de soltura: deixe as mãos pendentes, sacudindo-as levemente antes de tocar.',
        affectedFingers: affectedTense,
      });
      penalty += affectedTense.length * 4;
    }

    return {
      isCorrect: issues.length === 0,
      issues,
      penalty,
    };
  }

  /**
   * Analyze palm arch and position
   */
  private static analyzePalmPosition(
    _keypoints: number[][],
    _palmWidth: number,
    metrics: PostureMetrics
  ): { isCorrect: boolean; issue?: PostureIssue; penalty: number } {
    const { palmArch } = metrics;

    if (palmArch < POSTURE_THRESHOLDS.PALM_COLLAPSED) {
      return {
        isCorrect: false,
        penalty: 20,
        issue: {
          type: 'palm',
          severity: 'medium',
          message: 'Palma da mão muito achatada - Perda de controle',
          suggestedFix:
            'Crie um arco natural na palma. Imagine que você está segurando uma laranja na palma da mão. Esse arco é essencial para independência dos dedos e controle dinâmico.',
        },
      };
    }

    return { isCorrect: true, penalty: 0 };
  }

  /**
   * Analyze thumb position relative to hand
   */
  private static analyzeThumbPosition(
    keypoints: number[][],
    palmWidth: number,
    _metrics: PostureMetrics
  ): { isCorrect: boolean; issue?: PostureIssue; penalty: number } {
    const { THUMB_TIP, INDEX_MCP, THUMB_CMC } = LANDMARK_INDICES;

    const thumbToIndex = normalizeDistance(
      distance3D(keypoints[THUMB_TIP], keypoints[INDEX_MCP]),
      palmWidth
    );

    const thumbLength = normalizeDistance(
      distance3D(keypoints[THUMB_TIP], keypoints[THUMB_CMC]),
      palmWidth
    );

    const extensionRatio = thumbToIndex / thumbLength;

    if (extensionRatio < POSTURE_THRESHOLDS.THUMB_TUCKED) {
      return {
        isCorrect: false,
        penalty: 15,
        issue: {
          type: 'thumb',
          severity: 'medium',
          message: 'Polegar muito próximo dos outros dedos (recolhido)',
          suggestedFix:
            'Afaste o polegar, criando um espaço natural entre ele e o indicador. O polegar deve estar relaxado e ligeiramente arredondado, pronto para ação independente.',
        },
      };
    }

    if (extensionRatio > POSTURE_THRESHOLDS.THUMB_EXTENDED) {
      return {
        isCorrect: false,
        penalty: 10,
        issue: {
          type: 'thumb',
          severity: 'low',
          message: 'Polegar muito estendido',
          suggestedFix:
            'Relaxe o polegar, trazendo-o para uma posição mais próxima da mão. Evite tensão excessiva na articulação basal (CMC).',
        },
      };
    }

    return { isCorrect: true, penalty: 0 };
  }

  /**
   * Generate actionable recommendations based on issues and metrics
   */
  private static generateRecommendations(
    issues: PostureIssue[],
    _metrics: PostureMetrics
  ): string[] {
    const recommendations: string[] = [];

    if (issues.length === 0) {
      recommendations.push('✅ Excelente postura! Continue assim.');
      recommendations.push(
        '💡 Mantenha essa forma durante passagens rápidas para prevenir tensão acumulativa.'
      );
      return recommendations;
    }

    // Sort by severity
    const sortedIssues = issues.sort((a, b) => {
      const severityOrder = { critical: 0, high: 1, medium: 2, low: 3 };
      return severityOrder[a.severity] - severityOrder[b.severity];
    });

    // Critical issues get immediate attention
    const criticalIssues = sortedIssues.filter(i => i.severity === 'critical');
    if (criticalIssues.length > 0) {
      recommendations.push('🚨 ATENÇÃO CRÍTICA: Hiperextensão detectada');
      recommendations.push('⛔ Pare de tocar imediatamente e consulte um profissional');
      return recommendations;
    }

    // Primary recommendation (most severe issue)
    recommendations.push(`🎯 Prioridade: ${sortedIssues[0].suggestedFix}`);

    // Secondary recommendations
    if (sortedIssues.length > 1) {
      recommendations.push(`➡️ Depois: ${sortedIssues[1].suggestedFix}`);
    }

    // Context-specific tips
    const highSeverity = issues.some(i => i.severity === 'high');
    if (highSeverity) {
      recommendations.push(
        '🪞 Dica: Pratique na frente de um espelho por 5-10 minutos diariamente para corrigir hábitos posturais.'
      );
      recommendations.push(
        '📚 Exercício: Toque a escala de C maior muito lentamente, focando exclusivamente na postura, não na velocidade.'
      );
    }

    return recommendations;
  }

  /**
   * Get color code for score visualization
   */
  static getScoreColor(score: number): string {
    if (score >= 85) return '#10b981'; // Green - Excellent
    if (score >= 70) return '#22c55e'; // Light green - Good
    if (score >= 55) return '#f59e0b'; // Yellow - Needs improvement
    if (score >= 40) return '#f97316'; // Orange - Poor
    return '#ef4444'; // Red - Critical
  }

  /**
   * Get message for score
   */
  static getScoreMessage(score: number): string {
    if (score >= 90) return 'Postura Excelente! 🎯';
    if (score >= 80) return 'Boa Postura! ✅';
    if (score >= 70) return 'Postura Aceitável 👍';
    if (score >= 60) return 'Precisa Melhorar ⚠️';
    if (score >= 40) return 'Postura Ruim ⚠️';
    return 'Atenção Crítica! ❌';
  }
}
