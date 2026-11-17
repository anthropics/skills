import { useState, Suspense, lazy } from 'react';
import './App.css';

// Lazy load components to identify which one is breaking
const StudentDashboard = lazy(() => import('./pages/StudentDashboard'));
const ScoreFollowing = lazy(() => import('./pages/ScoreFollowing'));

type ViewType = 'dashboard' | 'practice' | 'learn' | 'score-following';

function LoadingFallback({ message }: { message: string }) {
  return (
    <div
      style={{
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
        minHeight: '50vh',
        fontSize: '1.5rem',
        color: '#667eea',
      }}
    >
      <div style={{ textAlign: 'center' }}>
        <div style={{ fontSize: '3rem', marginBottom: '1rem' }}>⏳</div>
        <div>{message}</div>
      </div>
    </div>
  );
}

function ErrorBoundary({ children }: { children: React.ReactNode }) {
  const [hasError, setHasError] = useState(false);
  const [error, setError] = useState<Error | null>(null);

  if (hasError) {
    return (
      <div
        style={{
          padding: '2rem',
          margin: '2rem',
          background: '#fee',
          border: '2px solid #f00',
          borderRadius: '8px',
        }}
      >
        <h2>❌ Erro ao carregar componente</h2>
        <pre
          style={{
            background: '#fff',
            padding: '1rem',
            borderRadius: '4px',
            overflow: 'auto',
          }}
        >
          {error?.toString()}
          {'\n\n'}
          {error?.stack}
        </pre>
        <button
          onClick={() => {
            setHasError(false);
            setError(null);
            window.location.reload();
          }}
          style={{
            padding: '0.5rem 1rem',
            marginTop: '1rem',
            cursor: 'pointer',
          }}
        >
          Recarregar
        </button>
      </div>
    );
  }

  try {
    return <>{children}</>;
  } catch (e) {
    setHasError(true);
    setError(e as Error);
    return null;
  }
}

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
        <ErrorBoundary>
          <Suspense fallback={<LoadingFallback message="Carregando componente..." />}>
            {currentView === 'dashboard' && <StudentDashboard />}
            {currentView === 'score-following' && <ScoreFollowing />}
          </Suspense>
        </ErrorBoundary>
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
