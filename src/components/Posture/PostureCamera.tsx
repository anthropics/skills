import { useEffect, useRef, useState } from 'react';
import ml5 from 'ml5';
import {
  HandPostureAnalyzer,
  type PostureAnalysis,
  type HandLandmarks,
} from '../../services/handPostureDetection';
import './PostureCamera.css';

interface PostureCameraProps {
  onAnalysisUpdate?: (analysis: PostureAnalysis) => void;
  isActive?: boolean;
}

export function PostureCamera({ onAnalysisUpdate, isActive = true }: PostureCameraProps) {
  const videoRef = useRef<HTMLVideoElement>(null);
  const canvasRef = useRef<HTMLCanvasElement>(null);
  const [isLoading, setIsLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [analysis, setAnalysis] = useState<PostureAnalysis | null>(null);
  const [handDetected, setHandDetected] = useState(false);
  const handposeRef = useRef<any>(null);
  const animationFrameRef = useRef<number>();

  useEffect(() => {
    if (!isActive) return;

    let mounted = true;
    let stream: MediaStream | null = null;

    const initCamera = async () => {
      try {
        // Request webcam access
        stream = await navigator.mediaDevices.getUserMedia({
          video: {
            width: 640,
            height: 480,
            facingMode: 'user',
          },
        });

        if (!mounted || !videoRef.current) return;

        videoRef.current.srcObject = stream;

        // Wait for video to load
        await new Promise<void>(resolve => {
          if (!videoRef.current) return;
          videoRef.current.onloadedmetadata = () => {
            videoRef.current?.play();
            resolve();
          };
        });

        // Initialize ml5.js handpose model
        if (!mounted) return;

        const handpose = await ml5.handpose(videoRef.current, {
          flipHorizontal: true,
          maxContinuousChecks: 10,
          detectionConfidence: 0.8,
          scoreThreshold: 0.5,
          iouThreshold: 0.3,
        });

        if (!mounted) return;

        handposeRef.current = handpose;
        setIsLoading(false);

        // Start detection loop
        startDetection();
      } catch (err) {
        console.error('Error initializing camera:', err);
        setError('Não foi possível acessar a câmera. Verifique as permissões do navegador.');
        setIsLoading(false);
      }
    };

    const startDetection = () => {
      const detect = async () => {
        if (!mounted || !isActive || !handposeRef.current || !videoRef.current) return;

        try {
          const predictions = await handposeRef.current.predict();

          if (predictions && predictions.length > 0) {
            setHandDetected(true);

            // Get first hand detected
            const hand = predictions[0];

            // Convert to our format
            const landmarks: HandLandmarks = {
              keypoints: hand.landmarks,
              handedness: hand.handedness || 'Right',
              confidence: hand.handInViewConfidence || 0.8,
            };

            // Analyze posture
            const postureAnalysis = HandPostureAnalyzer.analyzePosture(landmarks);
            setAnalysis(postureAnalysis);
            onAnalysisUpdate?.(postureAnalysis);

            // Draw landmarks on canvas
            drawHandLandmarks(hand.landmarks, postureAnalysis);
          } else {
            setHandDetected(false);
            clearCanvas();
          }
        } catch (err) {
          console.error('Error during hand detection:', err);
        }

        // Continue detection loop
        if (mounted && isActive) {
          animationFrameRef.current = requestAnimationFrame(detect);
        }
      };

      detect();
    };

    const drawHandLandmarks = (landmarks: number[][], analysis: PostureAnalysis) => {
      const canvas = canvasRef.current;
      const video = videoRef.current;
      if (!canvas || !video) return;

      const ctx = canvas.getContext('2d');
      if (!ctx) return;

      // Clear canvas
      ctx.clearRect(0, 0, canvas.width, canvas.height);

      // Set canvas size to match video
      canvas.width = video.videoWidth;
      canvas.height = video.videoHeight;

      // Draw landmarks
      const color = HandPostureAnalyzer.getScoreColor(analysis.score);

      // Draw connections between joints
      const connections = [
        [0, 1],
        [1, 2],
        [2, 3],
        [3, 4], // Thumb
        [0, 5],
        [5, 6],
        [6, 7],
        [7, 8], // Index
        [0, 9],
        [9, 10],
        [10, 11],
        [11, 12], // Middle
        [0, 13],
        [13, 14],
        [14, 15],
        [15, 16], // Ring
        [0, 17],
        [17, 18],
        [18, 19],
        [19, 20], // Pinky
      ];

      ctx.strokeStyle = color;
      ctx.lineWidth = 2;

      connections.forEach(([start, end]) => {
        const startPoint = landmarks[start];
        const endPoint = landmarks[end];
        ctx.beginPath();
        ctx.moveTo(startPoint[0], startPoint[1]);
        ctx.lineTo(endPoint[0], endPoint[1]);
        ctx.stroke();
      });

      // Draw keypoints
      ctx.fillStyle = color;
      landmarks.forEach(landmark => {
        ctx.beginPath();
        ctx.arc(landmark[0], landmark[1], 5, 0, 2 * Math.PI);
        ctx.fill();
      });

      // Highlight issues
      if (analysis.issues.length > 0) {
        ctx.fillStyle = 'rgba(239, 68, 68, 0.3)';
        analysis.issues.forEach(issue => {
          let pointIndex = 0;
          switch (issue.type) {
            case 'wrist':
              pointIndex = 0;
              break;
            case 'fingers':
              pointIndex = 8;
              break;
            case 'thumb':
              pointIndex = 4;
              break;
            case 'palm':
              pointIndex = 9;
              break;
          }
          const point = landmarks[pointIndex];
          ctx.beginPath();
          ctx.arc(point[0], point[1], 20, 0, 2 * Math.PI);
          ctx.fill();
        });
      }
    };

    const clearCanvas = () => {
      const canvas = canvasRef.current;
      if (!canvas) return;
      const ctx = canvas.getContext('2d');
      if (!ctx) return;
      ctx.clearRect(0, 0, canvas.width, canvas.height);
    };

    initCamera();

    return () => {
      mounted = false;
      if (animationFrameRef.current) {
        cancelAnimationFrame(animationFrameRef.current);
      }
      if (stream) {
        stream.getTracks().forEach(track => track.stop());
      }
    };
  }, [isActive, onAnalysisUpdate]);

  if (!isActive) {
    return null;
  }

  return (
    <div className="posture-camera">
      <div className="camera-container">
        <video ref={videoRef} className="camera-video" playsInline muted />
        <canvas ref={canvasRef} className="camera-overlay" />

        {isLoading && (
          <div className="camera-loading">
            <div className="spinner"></div>
            <p>Inicializando câmera e modelo de IA...</p>
          </div>
        )}

        {error && (
          <div className="camera-error">
            <p>❌ {error}</p>
          </div>
        )}

        {!isLoading && !error && !handDetected && (
          <div className="camera-prompt">
            <p>👋 Posicione sua mão na frente da câmera</p>
          </div>
        )}
      </div>

      {analysis && handDetected && (
        <div className="posture-feedback">
          <div
            className="posture-score"
            style={{ backgroundColor: HandPostureAnalyzer.getScoreColor(analysis.score) }}
          >
            <div className="score-value">{analysis.score}</div>
            <div className="score-label">{HandPostureAnalyzer.getScoreMessage(analysis.score)}</div>
          </div>

          {analysis.issues.length > 0 && (
            <div className="posture-issues">
              <h4>⚠️ Problemas Detectados:</h4>
              <ul>
                {analysis.issues.map((issue, index) => (
                  <li key={index} className={`issue-${issue.severity}`}>
                    <strong>{issue.message}</strong>
                    <p className="issue-fix">{issue.suggestedFix}</p>
                  </li>
                ))}
              </ul>
            </div>
          )}

          {analysis.recommendations.length > 0 && (
            <div className="posture-recommendations">
              <h4>💡 Recomendações:</h4>
              <ul>
                {analysis.recommendations.map((rec, index) => (
                  <li key={index}>{rec}</li>
                ))}
              </ul>
            </div>
          )}
        </div>
      )}
    </div>
  );
}
