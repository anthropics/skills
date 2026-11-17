import React from 'react';
import './Gamification.css';

export interface Achievement {
  id: string;
  title: string;
  description: string;
  icon: string;
  progress: number;
  maxProgress: number;
  unlocked: boolean;
  unlockedAt?: Date;
  category: 'practice' | 'accuracy' | 'consistency' | 'mastery';
  points: number;
}

interface AchievementSystemProps {
  achievements: Achievement[];
  totalPoints: number;
  level: number;
}

const AchievementSystem: React.FC<AchievementSystemProps> = ({
  achievements,
  totalPoints,
  level,
}) => {
  const unlockedAchievements = achievements.filter(a => a.unlocked);
  const lockedAchievements = achievements.filter(a => !a.unlocked);

  const getLevelProgress = () => {
    return Math.min((totalPoints % 100) / 100, 1);
  };

  return (
    <div className="achievement-system">
      <div className="achievement-header">
        <h3>🏆 Conquistas</h3>
        <div className="level-display">
          <div className="level-badge">Nível {level}</div>
          <div className="points">{totalPoints} pontos</div>
        </div>
      </div>

      <div className="level-progress">
        <div className="level-progress-bar" style={{ width: `${getLevelProgress() * 100}%` }}></div>
        <span className="level-progress-text">
          {Math.round(getLevelProgress() * 100)}% para o nível {level + 1}
        </span>
      </div>

      <div className="achievements-grid">
        {unlockedAchievements.map(achievement => (
          <div key={achievement.id} className="achievement unlocked">
            <div className="achievement-icon">{achievement.icon}</div>
            <div className="achievement-info">
              <h4>{achievement.title}</h4>
              <p>{achievement.description}</p>
              <span className="achievement-points">+{achievement.points} pontos</span>
            </div>
          </div>
        ))}

        {lockedAchievements.map(achievement => (
          <div key={achievement.id} className="achievement locked">
            <div className="achievement-icon">🔒</div>
            <div className="achievement-info">
              <h4>Conquista Secreta</h4>
              <p>Continue praticando para descobrir!</p>
              <div className="progress-bar">
                <div
                  className="progress-fill"
                  style={{ width: `${(achievement.progress / achievement.maxProgress) * 100}%` }}
                ></div>
              </div>
            </div>
          </div>
        ))}
      </div>
    </div>
  );
};

export default AchievementSystem;
