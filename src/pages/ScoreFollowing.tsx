import React, { useState } from 'react';
import YouTubeUrlInput from '../components/ScoreFollowing/YouTubeUrlInput';
import MidiPlayer from '../components/Player/MidiPlayer';
import {
  youtubeToMidiService,
  ConversionProgress,
  ConversionResult,
} from '../services/youtubeToMidi';
import { DifficultyAnalyzer, DifficultyAnalysis } from '../services/difficultyAnalyzer';
import { Midi } from '@tonejs/midi';
import './ScoreFollowing.css';

type WorkflowStage = 'input' | 'converting' | 'ready' | 'error';

const ScoreFollowing: React.FC = () => {
  const [stage, setStage] = useState<WorkflowStage>('input');
  const [conversionProgress, setConversionProgress] = useState<ConversionProgress | null>(null);
  const [conversionResult, setConversionResult] = useState<ConversionResult | null>(null);
  const [difficultyAnalysis, setDifficultyAnalysis] = useState<DifficultyAnalysis | null>(null);
  const [midiData, setMidiData] = useState<ArrayBuffer | null>(null);
  const [currentVideoId, setCurrentVideoId] = useState<string>('');

  const handleUrlSubmit = async (url: string, videoId: string) => {
    setCurrentVideoId(videoId);
    setStage('converting');

    try {
      const result = await youtubeToMidiService.convertVideo(
        { videoId, videoUrl: url },
        progress => {
          setConversionProgress(progress);
        }
      );

      setConversionResult(result);

      if (result.success && result.midiData) {
        setMidiData(result.midiData);

        // Analyze difficulty
        const midi = new Midi(result.midiData);
        const analysis = DifficultyAnalyzer.analyzeMidi(midi);
        setDifficultyAnalysis(analysis);

        setStage('ready');
      } else {
        setStage('error');
      }
    } catch (error) {
      console.error('Conversion error:', error);
      setStage('error');
    }
  };

  const handleReset = () => {
    setStage('input');
    setConversionProgress(null);
    setConversionResult(null);
    setDifficultyAnalysis(null);
    setMidiData(null);
    setCurrentVideoId('');
  };

  return (
    <div className="score-following-page">
      <div className="container">
        {stage === 'input' && (
          <div className="stage-content fade-in">
            <YouTubeUrlInput onUrlSubmit={handleUrlSubmit} isProcessing={false} />
          </div>
        )}

        {stage === 'converting' && conversionProgress && (
          <div className="stage-content fade-in">
            <ConversionProgressView progress={conversionProgress} videoId={currentVideoId} />
          </div>
        )}

        {stage === 'ready' && difficultyAnalysis && conversionResult && (
          <div className="stage-content fade-in">
            <DifficultyDisplay analysis={difficultyAnalysis} result={conversionResult} />

            {midiData && (
              <div className="player-section">
                <MidiPlayer midiData={midiData} autoPlay={false} />
              </div>
            )}

            <div className="actions">
              <button onClick={handleReset} className="btn-secondary">
                ← Converter Outro Vídeo
              </button>
            </div>
          </div>
        )}

        {stage === 'error' && (
          <div className="stage-content fade-in">
            <ErrorView onRetry={handleReset} />
          </div>
        )}
      </div>
    </div>
  );
};

// Conversion Progress Component
const ConversionProgressView: React.FC<{ progress: ConversionProgress; videoId: string }> = ({
  progress,
  videoId,
}) => {
  const getProgressPercentage = () => {
    return progress.progress;
  };

  const getStageClassName = (stageName: string, threshold: number) => {
    if (progress.stage === stageName) return 'active';
    if (progress.progress > threshold) return 'complete';
    return '';
  };

  return (
    <div className="conversion-progress">
      <div className="progress-header">
        <h2>🎵 Processando...</h2>
        <p>{progress.message}</p>
      </div>

      <div className="progress-preview">
        <img
          src={`https://img.youtube.com/vi/${videoId}/mqdefault.jpg`}
          alt="Video thumbnail"
          className="processing-thumbnail"
        />
      </div>

      <div className="progress-bar-wrapper">
        <div className="progress-bar-track">
          <div className="progress-bar-fill" style={{ width: `${getProgressPercentage()}%` }}>
            <span className="progress-percentage">{Math.round(getProgressPercentage())}%</span>
          </div>
        </div>
      </div>

      <div className="progress-stages">
        <div className={`stage ${getStageClassName('downloading', 0)}`}>
          <div className="stage-icon">📥</div>
          <div className="stage-label">Download</div>
        </div>
        <div className={`stage ${getStageClassName('analyzing', 40)}`}>
          <div className="stage-icon">🤖</div>
          <div className="stage-label">Análise IA</div>
        </div>
        <div className={`stage ${getStageClassName('converting', 70)}`}>
          <div className="stage-icon">🎹</div>
          <div className="stage-label">Conversão</div>
        </div>
        <div className={`stage ${getStageClassName('complete', 100)}`}>
          <div className="stage-icon">✅</div>
          <div className="stage-label">Concluído</div>
        </div>
      </div>
    </div>
  );
};

// Difficulty Display Component
const DifficultyDisplay: React.FC<{ analysis: DifficultyAnalysis; result: ConversionResult }> = ({
  analysis,
  result,
}) => {
  const difficultyColor = DifficultyAnalyzer.getColor(analysis.overallDifficulty);

  return (
    <div className="difficulty-display">
      <div className="difficulty-header">
        <h2>📊 Análise de Dificuldade</h2>
      </div>

      <div className="difficulty-card">
        <div className="overall-difficulty">
          <div
            className="difficulty-badge"
            style={{
              backgroundColor: difficultyColor.backgroundColor,
              color: difficultyColor.color,
              borderColor: difficultyColor.borderColor,
            }}
          >
            {DifficultyAnalyzer.getDifficultyLabel(analysis.overallDifficulty)}
          </div>
          <div className="difficulty-score">
            <span className="score-label">Pontuação:</span>
            <span className="score-value">{Math.round(analysis.difficultyScore)}/100</span>
          </div>
        </div>

        <div className="statistics-grid">
          <div className="stat-card">
            <div className="stat-icon">🎵</div>
            <div className="stat-value">{analysis.statistics.totalNotes}</div>
            <div className="stat-label">Total de Notas</div>
          </div>

          <div className="stat-card">
            <div className="stat-icon">⏱️</div>
            <div className="stat-value">{result.metadata?.duration || 0}s</div>
            <div className="stat-label">Duração</div>
          </div>

          <div className="stat-card">
            <div className="stat-icon">🎯</div>
            <div className="stat-value">{Math.round(analysis.statistics.averageTempo)}</div>
            <div className="stat-label">Notas/Segundo</div>
          </div>

          <div className="stat-card">
            <div className="stat-icon">🎼</div>
            <div className="stat-value">{analysis.statistics.maxNotesPerSecond}</div>
            <div className="stat-label">Pico de Velocidade</div>
          </div>
        </div>

        <div className="notes-distribution">
          <h4>Distribuição de Dificuldade:</h4>
          <div className="distribution-bars">
            <div className="distribution-bar">
              <span className="bar-label">🟢 Fácil</span>
              <div className="bar-track">
                <div
                  className="bar-fill easy"
                  style={{
                    width: `${(analysis.statistics.easyNotes / analysis.statistics.totalNotes) * 100}%`,
                  }}
                ></div>
              </div>
              <span className="bar-value">{analysis.statistics.easyNotes}</span>
            </div>

            <div className="distribution-bar">
              <span className="bar-label">🟡 Médio</span>
              <div className="bar-track">
                <div
                  className="bar-fill medium"
                  style={{
                    width: `${(analysis.statistics.mediumNotes / analysis.statistics.totalNotes) * 100}%`,
                  }}
                ></div>
              </div>
              <span className="bar-value">{analysis.statistics.mediumNotes}</span>
            </div>

            <div className="distribution-bar">
              <span className="bar-label">🔴 Difícil</span>
              <div className="bar-track">
                <div
                  className="bar-fill hard"
                  style={{
                    width: `${(analysis.statistics.hardNotes / analysis.statistics.totalNotes) * 100}%`,
                  }}
                ></div>
              </div>
              <span className="bar-value">{analysis.statistics.hardNotes}</span>
            </div>
          </div>
        </div>
      </div>
    </div>
  );
};

// Error View Component
const ErrorView: React.FC<{ onRetry: () => void }> = ({ onRetry }) => {
  return (
    <div className="error-view">
      <div className="error-icon">⚠️</div>
      <h2>Ops! Algo deu errado</h2>
      <p>Não foi possível processar o vídeo. Isso pode acontecer por diversos motivos:</p>
      <ul>
        <li>URL inválida ou vídeo não disponível</li>
        <li>Vídeo sem áudio claro de piano</li>
        <li>Problema temporário no servidor</li>
      </ul>

      <div className="error-note">
        <strong>Nota:</strong> Esta é uma versão de demonstração. A conversão real de YouTube para
        MIDI requer integração com backend e modelos de IA para detecção de pitch.
      </div>

      <button onClick={onRetry} className="btn-primary">
        ← Tentar Novamente
      </button>
    </div>
  );
};

export default ScoreFollowing;
