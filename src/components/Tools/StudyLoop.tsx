import React, { useState, useEffect } from 'react';
import './Tools.css';

interface StudyLoopProps {
  measures: number[];
  onLoopChange: (measures: number[], isLooping: boolean) => void;
  currentMeasure: number;
}

const StudyLoop: React.FC<StudyLoopProps> = ({ measures, onLoopChange, currentMeasure }) => {
  const [isLooping, setIsLooping] = useState(false);
  const [loopStart, setLoopStart] = useState(1);
  const [loopEnd, setLoopEnd] = useState(4);
  const [repetitions, setRepetitions] = useState(5);
  const [completedRepetitions, setCompletedRepetitions] = useState(0);
  const [showSettings, setShowSettings] = useState(false);

  const availableMeasures =
    measures.length > 0 ? measures : Array.from({ length: 32 }, (_, i) => i + 1);

  useEffect(() => {
    if (isLooping && currentMeasure === loopEnd) {
      const newCompleted = completedRepetitions + 1;
      setCompletedRepetitions(newCompleted);

      if (newCompleted >= repetitions) {
        setIsLooping(false);
        onLoopChange([], false);
      }
    }
  }, [currentMeasure, loopEnd, isLooping, completedRepetitions, repetitions, onLoopChange]);

  const handleStartLoop = () => {
    const loopMeasures = Array.from({ length: loopEnd - loopStart + 1 }, (_, i) => loopStart + i);

    setIsLooping(true);
    setCompletedRepetitions(0);
    onLoopChange(loopMeasures, true);
  };

  const handleStopLoop = () => {
    setIsLooping(false);
    setCompletedRepetitions(0);
    onLoopChange([], false);
  };

  const progress = (completedRepetitions / repetitions) * 100;

  return (
    <div className="study-loop">
      <div className="loop-header">
        <h3>🔄 Loop de Estudo</h3>
        <div className="loop-status">
          {isLooping ? (
            <span className="looping">
              Repetindo... ({completedRepetitions}/{repetitions})
            </span>
          ) : (
            <span className="paused">Pausado</span>
          )}
        </div>
      </div>

      <div className="loop-controls">
        <div className="measure-range">
          <div className="range-input">
            <label htmlFor="loop-start">Início:</label>
            <select
              id="loop-start"
              value={loopStart}
              onChange={e => setLoopStart(Number(e.target.value))}
              disabled={isLooping}
            >
              {availableMeasures.map(measure => (
                <option key={measure} value={measure}>
                  Compasso {measure}
                </option>
              ))}
            </select>
          </div>

          <div className="range-input">
            <label htmlFor="loop-end">Fim:</label>
            <select
              id="loop-end"
              value={loopEnd}
              onChange={e => setLoopEnd(Number(e.target.value))}
              disabled={isLooping}
            >
              {availableMeasures
                .filter(measure => measure >= loopStart)
                .map(measure => (
                  <option key={measure} value={measure}>
                    Compasso {measure}
                  </option>
                ))}
            </select>
          </div>
        </div>

        <div className="repetition-control">
          <label>Repetições: {repetitions}</label>
          <input
            type="range"
            min="1"
            max="20"
            value={repetitions}
            onChange={e => setRepetitions(Number(e.target.value))}
            disabled={isLooping}
          />
        </div>

        <div className="loop-actions">
          {!isLooping ? (
            <button className="start-loop" onClick={handleStartLoop}>
              ▶️ Iniciar Loop
            </button>
          ) : (
            <button className="stop-loop" onClick={handleStopLoop}>
              ⏹️ Parar Loop
            </button>
          )}

          <button className="settings-toggle" onClick={() => setShowSettings(!showSettings)}>
            ⚙️
          </button>
        </div>
      </div>

      {isLooping && (
        <div className="loop-progress">
          <div className="progress-bar">
            <div className="progress-fill" style={{ width: `${progress}%` }}></div>
          </div>
          <span className="progress-text">
            {completedRepetitions} de {repetitions} repetições
          </span>
        </div>
      )}

      {showSettings && (
        <div className="loop-settings">
          <h4>Configurações do Loop</h4>
          <div className="setting">
            <label>
              <input type="checkbox" defaultChecked />
              Pausa automática ao completar
            </label>
          </div>
          <div className="setting">
            <label>
              <input type="checkbox" defaultChecked />
              Aumentar BPM progressivamente
            </label>
          </div>
          <div className="setting">
            <label>
              <input type="checkbox" />
              Tocar demonstração antes de cada repetição
            </label>
          </div>
        </div>
      )}

      <div className="current-loop">
        <strong>Loop Atual:</strong> Compassos {loopStart} a {loopEnd}
        {isLooping && <span className="current-measure">• Compasso atual: {currentMeasure}</span>}
      </div>
    </div>
  );
};

export default StudyLoop;
