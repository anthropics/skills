import React from 'react';
import './Gamification.css';

interface StreakCounterProps {
  currentStreak: number;
  bestStreak: number;
  todayPracticed: boolean;
}

const StreakCounter: React.FC<StreakCounterProps> = ({
  currentStreak,
  bestStreak,
  todayPracticed,
}) => {
  const getFlameIntensity = (streak: number) => {
    if (streak >= 30) return 'inferno';
    if (streak >= 14) return 'hot';
    if (streak >= 7) return 'warm';
    return 'cool';
  };

  return (
    <div className="streak-counter">
      <div className="streak-header">
        <h3>🔥 Sequência de Prática</h3>
      </div>

      <div className="streak-display">
        <div className="current-streak">
          <div
            className={`flame ${getFlameIntensity(currentStreak)} ${todayPracticed ? 'active' : ''}`}
          >
            🔥
          </div>
          <div className="streak-info">
            <span className="streak-number">{currentStreak}</span>
            <span className="streak-label">dias seguidos</span>
          </div>
        </div>

        <div className="streak-stats">
          <div className="stat">
            <span className="stat-value">{bestStreak}</span>
            <span className="stat-label">melhor sequência</span>
          </div>
          <div className="stat">
            <span className="stat-value">{todayPracticed ? '✅' : '⏳'}</span>
            <span className="stat-label">hoje</span>
          </div>
        </div>
      </div>

      {currentStreak > 0 && (
        <div className="streak-motivation">
          {currentStreak >= 30 && '🔥 Incrível! Você é uma máquina de prática!'}
          {currentStreak >= 14 && currentStreak < 30 && '🌟 Excelente consistência!'}
          {currentStreak >= 7 && currentStreak < 14 && '💪 Ótimo trabalho! Continue assim!'}
          {currentStreak > 0 &&
            currentStreak < 7 &&
            '🚀 Bom começo! Vamos construir essa sequência!'}
        </div>
      )}
    </div>
  );
};

export default StreakCounter;
