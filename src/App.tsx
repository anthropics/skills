import { useState } from 'react';
import StudentDashboard from './pages/StudentDashboard';
import ScoreFollowing from './pages/ScoreFollowing';
import './App.css';

type ViewType = 'dashboard' | 'practice' | 'learn' | 'score-following';

function App() {
  const [currentView, setCurrentView] = useState<ViewType>('dashboard');

  return (
    <div className="app">
      <header className="app-header">
        <div className="container">
          <div className="header-content">
            <div className="logo">
              <h1>🎹 Piano Tutor</h1>
              <span className="tagline">Treinamento Inteligente com IA</span>
            </div>
            <nav className="main-nav">
              <button
                className={`nav-button ${currentView === 'dashboard' ? 'active' : ''}`}
                onClick={() => setCurrentView('dashboard')}
              >
                Dashboard
              </button>
              <button
                className={`nav-button ${currentView === 'score-following' ? 'active' : ''}`}
                onClick={() => setCurrentView('score-following')}
              >
                YouTube → Tutorial
              </button>
              <button className="nav-button" disabled>
                Prática
              </button>
              <button className="nav-button" disabled>
                Aprender
              </button>
            </nav>
          </div>
        </div>
      </header>

      <main className="app-main">
        {currentView === 'dashboard' && <StudentDashboard />}
        {currentView === 'score-following' && <ScoreFollowing />}
      </main>

      <footer className="app-footer">
        <div className="container">
          <p>Piano Tutor v1.0.0 - MVP | Desenvolvido com React + TypeScript + IA</p>
        </div>
      </footer>
    </div>
  );
}

export default App;
