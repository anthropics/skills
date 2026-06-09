/**
 * Hand Posture Detection Service
 * Uses ml5.js handpose model to detect hand posture and provide feedback
 */

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
}

export interface PostureIssue {
  type: 'wrist' | 'fingers' | 'palm' | 'thumb';
  severity: 'low' | 'medium' | 'high';
  message: string;
  suggestedFix: string;
}

/**
 * Analyze hand posture for piano playing
 * Based on classical piano technique principles
 */
export class HandPostureAnalyzer {
  /**
   * Analyze complete hand posture
   */
  static analyzePosture(landmarks: HandLandmarks): PostureAnalysis {
    const issues: PostureIssue[] = [];
    let score = 100;

    // Analyze wrist position
    const wristAnalysis = this.analyzeWrist(landmarks.keypoints);
    if (!wristAnalysis.isCorrect) {
      issues.push(wristAnalysis.issue!);
      score -= wristAnalysis.issue!.severity === 'high' ? 30 : 15;
    }

    // Analyze finger curvature
    const fingerAnalysis = this.analyzeFingerCurvature(landmarks.keypoints);
    if (!fingerAnalysis.isCorrect) {
      issues.push(fingerAnalysis.issue!);
      score -= fingerAnalysis.issue!.severity === 'high' ? 25 : 10;
    }

    // Analyze palm position
    const palmAnalysis = this.analyzePalmPosition(landmarks.keypoints);
    if (!palmAnalysis.isCorrect) {
      issues.push(palmAnalysis.issue!);
      score -= palmAnalysis.issue!.severity === 'high' ? 20 : 10;
    }

    // Analyze thumb position
    const thumbAnalysis = this.analyzeThumbPosition(landmarks.keypoints);
    if (!thumbAnalysis.isCorrect) {
      issues.push(thumbAnalysis.issue!);
      score -= thumbAnalysis.issue!.severity === 'high' ? 15 : 5;
    }

    // Generate recommendations
    const recommendations = this.generateRecommendations(issues);

    return {
      isCorrect: issues.length === 0,
      score: Math.max(0, score),
      issues,
      recommendations,
    };
  }

  /**
   * Analyze wrist position (should be level with hand, not too low)
   */
  private static analyzeWrist(keypoints: number[][]): { isCorrect: boolean; issue?: PostureIssue } {
    const wrist = keypoints[0]; // Wrist keypoint
    const middleFingerBase = keypoints[9]; // Middle finger MCP joint

    // Calculate vertical distance (Y-axis)
    const verticalDiff = middleFingerBase[1] - wrist[1];

    // Wrist should be roughly level or slightly above finger base
    if (verticalDiff < -30) {
      return {
        isCorrect: false,
        issue: {
          type: 'wrist',
          severity: 'high',
          message: 'Pulso muito baixo',
          suggestedFix:
            'Levante o pulso até ficar no mesmo nível dos dedos. Imagine uma linha reta do cotovelo até os dedos.',
        },
      };
    }

    if (verticalDiff > 40) {
      return {
        isCorrect: false,
        issue: {
          type: 'wrist',
          severity: 'medium',
          message: 'Pulso muito alto',
          suggestedFix: 'Abaixe levemente o pulso. O pulso deve estar relaxado, não tenso.',
        },
      };
    }

    return { isCorrect: true };
  }

  /**
   * Analyze finger curvature (should be naturally curved, not flat)
   */
  private static analyzeFingerCurvature(keypoints: number[][]): {
    isCorrect: boolean;
    issue?: PostureIssue;
  } {
    // Analyze index finger as representative
    const indexBase = keypoints[5]; // Index MCP
    const indexMiddle = keypoints[6]; // Index PIP
    const indexTip = keypoints[8]; // Index DIP

    // Calculate curvature using the middle joint position
    const baseToTipDistance = Math.hypot(indexTip[0] - indexBase[0], indexTip[1] - indexBase[1]);

    const baseToMiddleDistance = Math.hypot(
      indexMiddle[0] - indexBase[0],
      indexMiddle[1] - indexBase[1]
    );

    const curvatureRatio = baseToMiddleDistance / baseToTipDistance;

    // Too flat (ratio close to 1)
    if (curvatureRatio > 0.8) {
      return {
        isCorrect: false,
        issue: {
          type: 'fingers',
          severity: 'high',
          message: 'Dedos muito retos',
          suggestedFix:
            'Curve os dedos naturalmente, como se estivesse segurando uma bola. Isso dá mais controle e previne lesões.',
        },
      };
    }

    // Too curved (ratio too small)
    if (curvatureRatio < 0.4) {
      return {
        isCorrect: false,
        issue: {
          type: 'fingers',
          severity: 'medium',
          message: 'Dedos muito curvados',
          suggestedFix: 'Relaxe os dedos um pouco. A curvatura deve ser natural, não forçada.',
        },
      };
    }

    return { isCorrect: true };
  }

  /**
   * Analyze palm position (should be arched, not collapsed)
   */
  private static analyzePalmPosition(keypoints: number[][]): {
    isCorrect: boolean;
    issue?: PostureIssue;
  } {
    const wrist = keypoints[0];
    const indexBase = keypoints[5];
    const pinkyBase = keypoints[17];

    // Calculate palm width
    const palmWidth = Math.hypot(pinkyBase[0] - indexBase[0], pinkyBase[1] - indexBase[1]);

    // Calculate palm center to wrist distance
    const palmCenterX = (indexBase[0] + pinkyBase[0]) / 2;
    const palmCenterY = (indexBase[1] + pinkyBase[1]) / 2;
    const palmHeight = Math.hypot(palmCenterX - wrist[0], palmCenterY - wrist[1]);

    // Palm should have an arch (height/width ratio)
    const archRatio = palmHeight / palmWidth;

    if (archRatio < 0.6) {
      return {
        isCorrect: false,
        issue: {
          type: 'palm',
          severity: 'medium',
          message: 'Palma da mão muito achatada',
          suggestedFix: 'Crie um arco natural na palma da mão. Imagine segurar uma laranja.',
        },
      };
    }

    return { isCorrect: true };
  }

  /**
   * Analyze thumb position (should be relaxed and rounded, not tucked under)
   */
  private static analyzeThumbPosition(keypoints: number[][]): {
    isCorrect: boolean;
    issue?: PostureIssue;
  } {
    const thumbBase = keypoints[1];
    const thumbTip = keypoints[4];
    const indexBase = keypoints[5];

    // Calculate thumb extension
    const thumbToIndex = Math.hypot(thumbTip[0] - indexBase[0], thumbTip[1] - indexBase[1]);

    const thumbLength = Math.hypot(thumbTip[0] - thumbBase[0], thumbTip[1] - thumbBase[1]);

    const extensionRatio = thumbToIndex / thumbLength;

    // Thumb too close to fingers (tucked)
    if (extensionRatio < 0.7) {
      return {
        isCorrect: false,
        issue: {
          type: 'thumb',
          severity: 'medium',
          message: 'Polegar muito próximo dos outros dedos',
          suggestedFix:
            'Mantenha o polegar mais afastado e relaxado, formando um espaço natural com o indicador.',
        },
      };
    }

    // Thumb too extended
    if (extensionRatio > 1.8) {
      return {
        isCorrect: false,
        issue: {
          type: 'thumb',
          severity: 'low',
          message: 'Polegar muito estendido',
          suggestedFix: 'Relaxe o polegar, mantendo-o em uma posição mais natural.',
        },
      };
    }

    return { isCorrect: true };
  }

  /**
   * Generate actionable recommendations based on issues
   */
  private static generateRecommendations(issues: PostureIssue[]): string[] {
    const recommendations: string[] = [];

    if (issues.length === 0) {
      return ['Excelente postura! Continue assim. 👏'];
    }

    // Sort by severity
    const sortedIssues = issues.sort((a, b) => {
      const severityOrder = { high: 0, medium: 1, low: 2 };
      return severityOrder[a.severity] - severityOrder[b.severity];
    });

    // Add primary recommendation (most severe issue)
    recommendations.push(`🎯 Prioridade: ${sortedIssues[0].suggestedFix}`);

    // Add secondary recommendations
    if (sortedIssues.length > 1) {
      recommendations.push(`➡️ Depois: ${sortedIssues[1].suggestedFix}`);
    }

    // Add general tip
    if (issues.some(i => i.severity === 'high')) {
      recommendations.push(
        '💡 Dica: Pratique a postura na frente de um espelho por 5 minutos antes de tocar.'
      );
    }

    return recommendations;
  }

  /**
   * Get visual feedback color based on score
   */
  static getScoreColor(score: number): string {
    if (score >= 80) return '#10b981'; // Green - Good
    if (score >= 60) return '#f59e0b'; // Yellow - Needs improvement
    return '#ef4444'; // Red - Poor
  }

  /**
   * Get visual feedback message based on score
   */
  static getScoreMessage(score: number): string {
    if (score >= 90) return 'Postura Excelente! 🎯';
    if (score >= 80) return 'Boa Postura! ✅';
    if (score >= 70) return 'Postura Aceitável 👍';
    if (score >= 60) return 'Precisa Melhorar ⚠️';
    return 'Atenção à Postura! ❌';
  }
}
