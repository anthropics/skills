import React, { useState, useEffect } from 'react';
import StreakCounter from '../components/Gamification/StreakCounter';
import AchievementSystem from '../components/Gamification/AchievementSystem';
import Leaderboard from '../components/Gamification/Leaderboard';
import Metronome from '../components/Tools/Metronome';
import StudyLoop from '../components/Tools/StudyLoop';
import { useGamification } from '../hooks/useGamification';
import './StudentDashboard.css';

const StudentDashboard: React.FC = () => {
  const [activeTab, setActiveTab] = useState<'progress' | 'tools' | 'community'>('progress');
  const [_selectedMeasures, setSelectedMeasures] = useState<number[]>([1, 2, 3, 4]);
  const [currentMeasure, _setCurrentMeasure] = useState(1);
  const [leaderboardTimeFrame, setLeaderboardTimeFrame] = useState<
    'daily' | 'weekly' | 'monthly' | 'allTime'
  >('weekly');

  const gamification = useGamification();

  useEffect(() => {
    gamification.loadLeaderboard(leaderboardTimeFrame);
  }, [leaderboardTimeFrame]);

  // Simular dados de sessão
  const handleSessionComplete = () => {
    gamification.recordSession({
      duration: 25,
      accuracy: 0.87,
      hasErrors: true,
    });
  };

  const handleLoopChange = (measures: number[], isLooping: boolean) => {
    setSelectedMeasures(measures);
    // Aqui você integraria com o player de partitura
    console.log('Loop changed:', measures, isLooping);
  };

  return (
    <div className="student-dashboard">
      <div className="dashboard-header">
        <h1>🎹 Meu Progresso</h1>
        <button className="session-button" onClick={handleSessionComplete}>
          + Nova Sessão
        </button>
      </div>

      {/* Stats Overview */}
      <div className="stats-overview">
        <StreakCounter
          currentStreak={gamification.streak}
          bestStreak={gamification.bestStreak}
          todayPracticed={gamification.todayPracticed}
        />

        <div className="stat-cards">
          <div className="stat-card">
            <div className="stat-icon">🎯</div>
            <div className="stat-content">
              <span className="stat-value">87%</span>
              <span className="stat-label">Precisão Média</span>
            </div>
          </div>

          <div className="stat-card">
            <div className="stat-icon">⏱️</div>
            <div className="stat-content">
              <span className="stat-value">45min</span>
              <span className="stat-label">Tempo Hoje</span>
            </div>
          </div>

          <div className="stat-card">
            <div className="stat-icon">📈</div>
            <div className="stat-content">
              <span className="stat-value">+12%</span>
              <span className="stat-label">Evolução Semanal</span>
            </div>
          </div>
        </div>
      </div>

      {/* Navigation Tabs */}
      <div className="dashboard-tabs">
        <button
          className={`tab ${activeTab === 'progress' ? 'active' : ''}`}
          onClick={() => setActiveTab('progress')}
        >
          📊 Meu Progresso
        </button>
        <button
          className={`tab ${activeTab === 'tools' ? 'active' : ''}`}
          onClick={() => setActiveTab('tools')}
        >
          🛠️ Ferramentas
        </button>
        <button
          className={`tab ${activeTab === 'community' ? 'active' : ''}`}
          onClick={() => setActiveTab('community')}
        >
          👥 Comunidade
        </button>
      </div>

      {/* Tab Content */}
      <div className="tab-content">
        {activeTab === 'progress' && (
          <div className="progress-tab">
            <div className="progress-column">
              <AchievementSystem
                achievements={gamification.achievements}
                totalPoints={gamification.totalPoints}
                level={gamification.level}
              />
            </div>

            <div className="progress-column">
              <div className="recent-sessions">
                <h3>📅 Sessões Recentes</h3>
                <div className="sessions-list">
                  {[1, 2, 3, 4, 5].map(session => (
                    <div key={session} className="session-item">
                      <div className="session-date">
                        {new Date(Date.now() - session * 86400000).toLocaleDateString('pt-BR')}
                      </div>
                      <div className="session-stats">
                        <span>25min</span>
                        <span>85%</span>
                        <span>⭐ 4.2</span>
                      </div>
                    </div>
                  ))}
                </div>
              </div>

              <div className="practice-goals">
                <h3>🎯 Metas de Prática</h3>
                <div className="goals-list">
                  <div className="goal-item">
                    <span>🎹 Praticar escalas maiores</span>
                    <div className="goal-progress">
                      <div className="progress-bar">
                        <div className="progress-fill" style={{ width: '75%' }}></div>
                      </div>
                      <span>3/4 sessões</span>
                    </div>
                  </div>

                  <div className="goal-item">
                    <span>🎵 Aprender nova peça</span>
                    <div className="goal-progress">
                      <div className="progress-bar">
                        <div className="progress-fill" style={{ width: '40%' }}></div>
                      </div>
                      <span>40% completa</span>
                    </div>
                  </div>
                </div>
              </div>
            </div>
          </div>
        )}

        {activeTab === 'tools' && (
          <div className="tools-tab">
            <div className="tools-column">
              <Metronome initialBpm={120} />
              <StudyLoop
                measures={[1, 2, 3, 4, 5, 6, 7, 8]}
                onLoopChange={handleLoopChange}
                currentMeasure={currentMeasure}
              />
            </div>

            <div className="tools-column">
              <div className="tool-card">
                <h3>🎧 Isolador de Áudio</h3>
                <p>Use Spleeter para isolar o piano de gravações</p>
                <button className="tool-button">Processar Áudio</button>
              </div>

              <div className="tool-card">
                <h3>📝 Anotações Musicais</h3>
                <textarea
                  placeholder="Anote observações sobre sua prática..."
                  className="notes-textarea"
                ></textarea>
              </div>

              <div className="tool-card">
                <h3>🎼 Gerador de Exercícios</h3>
                <div className="exercise-options">
                  <button>Escalas</button>
                  <button>Arpejos</button>
                  <button>Acordes</button>
                </div>
              </div>
            </div>
          </div>
        )}

        {activeTab === 'community' && (
          <div className="community-tab">
            <Leaderboard
              entries={gamification.leaderboard}
              timeFrame={leaderboardTimeFrame}
              onTimeFrameChange={setLeaderboardTimeFrame}
            />

            <div className="community-stats">
              <div className="community-card">
                <h4>🌍 Ranking Global</h4>
                <div className="global-rank">
                  <span className="rank-number">#127</span>
                  <span className="rank-label">de 2.847 pianistas</span>
                </div>
              </div>

              <div className="community-card">
                <h4>👥 Amigos</h4>
                <div className="friends-list">
                  <div className="friend">
                    <span>🎹 PianoMaster</span>
                    <span>Nível 15</span>
                  </div>
                  <div className="friend">
                    <span>🎵 MusicLover</span>
                    <span>Nível 12</span>
                  </div>
                </div>
                <button className="add-friend">+ Adicionar Amigos</button>
              </div>
            </div>
          </div>
        )}
      </div>
    </div>
  );
};

export default StudentDashboard;
