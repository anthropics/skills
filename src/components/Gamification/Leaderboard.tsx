import React, { useState } from 'react';
import './Gamification.css';

export interface LeaderboardEntry {
  userId: string;
  username: string;
  avatar?: string;
  score: number;
  level: number;
  streak: number;
  accuracy: number;
  rank: number;
  isCurrentUser?: boolean;
}

interface LeaderboardProps {
  entries: LeaderboardEntry[];
  timeFrame: 'daily' | 'weekly' | 'monthly' | 'allTime';
  onTimeFrameChange: (timeFrame: 'daily' | 'weekly' | 'monthly' | 'allTime') => void;
}

const Leaderboard: React.FC<LeaderboardProps> = ({ entries, timeFrame, onTimeFrameChange }) => {
  const [expandedUser, setExpandedUser] = useState<string | null>(null);

  const getRankIcon = (rank: number) => {
    switch (rank) {
      case 1:
        return '🥇';
      case 2:
        return '🥈';
      case 3:
        return '🥉';
      default:
        return `#${rank}`;
    }
  };

  const timeFrameLabels = {
    daily: 'Hoje',
    weekly: 'Esta Semana',
    monthly: 'Este Mês',
    allTime: 'Todos os Tempos',
  };

  return (
    <div className="leaderboard">
      <div className="leaderboard-header">
        <h3>🏆 Ranking dos Pianistas</h3>
        <div className="time-frame-selector">
          {(['daily', 'weekly', 'monthly', 'allTime'] as const).map(timeFrameOption => (
            <button
              key={timeFrameOption}
              className={`time-frame-btn ${timeFrame === timeFrameOption ? 'active' : ''}`}
              onClick={() => onTimeFrameChange(timeFrameOption)}
            >
              {timeFrameLabels[timeFrameOption]}
            </button>
          ))}
        </div>
      </div>

      <div className="leaderboard-list">
        {entries.map(entry => (
          <div
            key={entry.userId}
            className={`leaderboard-entry ${entry.isCurrentUser ? 'current-user' : ''} ${expandedUser === entry.userId ? 'expanded' : ''}`}
            onClick={() => setExpandedUser(expandedUser === entry.userId ? null : entry.userId)}
          >
            <div className="entry-main">
              <div className="rank">{getRankIcon(entry.rank)}</div>

              <div className="user-info">
                <div className="avatar">{entry.avatar || '🎹'}</div>
                <div className="user-details">
                  <span className="username">{entry.username}</span>
                  {entry.isCurrentUser && <span className="you-badge">Você</span>}
                </div>
              </div>

              <div className="score">{entry.score.toLocaleString()}</div>
            </div>

            {expandedUser === entry.userId && (
              <div className="entry-details">
                <div className="detail">
                  <span className="label">Nível</span>
                  <span className="value">{entry.level}</span>
                </div>
                <div className="detail">
                  <span className="label">Sequência</span>
                  <span className="value">{entry.streak} dias</span>
                </div>
                <div className="detail">
                  <span className="label">Precisão</span>
                  <span className="value">{Math.round(entry.accuracy * 100)}%</span>
                </div>
              </div>
            )}
          </div>
        ))}
      </div>

      {entries.length === 0 && (
        <div className="empty-leaderboard">
          <p>Nenhum dado disponível para este período</p>
          <small>Comece a praticar para aparecer no ranking!</small>
        </div>
      )}
    </div>
  );
};

export default Leaderboard;
