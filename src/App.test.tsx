import { useState, useEffect } from 'react';

function AppTest() {
  const [logs, setLogs] = useState<string[]>(['🎹 Piano Tutor - Diagnóstico']);
  const [error, setError] = useState<string | null>(null);

  useEffect(() => {
    const addLog = (msg: string) => setLogs(prev => [...prev, msg]);

    try {
      addLog('✅ React renderizado');
      addLog('✅ useEffect executado');

      // Test localStorage
      try {
        localStorage.setItem('test', 'ok');
        localStorage.removeItem('test');
        addLog('✅ localStorage funciona');
      } catch (e) {
        addLog('❌ localStorage com problema: ' + e);
      }

      // Test imports
      addLog('🔍 Testando imports...');

      import('./hooks/useGamification')
        .then(() => {
          addLog('✅ useGamification importado');
        })
        .catch(e => {
          addLog('❌ Erro no useGamification: ' + e.message);
          setError(e.toString());
        });

      import('./pages/StudentDashboard')
        .then(() => {
          addLog('✅ StudentDashboard importado');
        })
        .catch(e => {
          addLog('❌ Erro no StudentDashboard: ' + e.message);
          setError(e.toString());
        });

      import('./services/handPostureDetection.v2')
        .then(() => {
          addLog('✅ handPostureDetection.v2 importado');
        })
        .catch(e => {
          addLog('❌ Erro no handPostureDetection.v2: ' + e.message);
          setError(e.toString());
        });

      import('./services/temporalSync')
        .then(() => {
          addLog('✅ temporalSync importado');
        })
        .catch(e => {
          addLog('❌ Erro no temporalSync: ' + e.message);
          setError(e.toString());
        });

      import('./hooks/usePremiumPosture')
        .then(() => {
          addLog('✅ usePremiumPosture importado');
        })
        .catch(e => {
          addLog('❌ Erro no usePremiumPosture: ' + e.message);
          setError(e.toString());
        });
    } catch (e: any) {
      addLog('❌ ERRO CRÍTICO: ' + e.message);
      setError(e.toString());
    }
  }, []);

  return (
    <div
      style={{
        minHeight: '100vh',
        background: error
          ? 'linear-gradient(135deg, #ef4444 0%, #dc2626 100%)'
          : 'linear-gradient(135deg, #667eea 0%, #764ba2 100%)',
        color: 'white',
        fontFamily: 'Monaco, Courier, monospace',
        padding: '2rem',
        fontSize: '14px',
      }}
    >
      <div style={{ maxWidth: '800px', margin: '0 auto' }}>
        <h1 style={{ fontSize: '2rem', marginBottom: '2rem' }}>🔍 Piano Tutor - Diagnóstico</h1>

        <div
          style={{
            background: 'rgba(0,0,0,0.3)',
            borderRadius: '8px',
            padding: '1.5rem',
            marginBottom: '1rem',
          }}
        >
          {logs.map((log, i) => (
            <div
              key={i}
              style={{
                marginBottom: '0.5rem',
                paddingLeft: '1rem',
                borderLeft: log.includes('❌') ? '3px solid #ef4444' : '3px solid #10b981',
              }}
            >
              {log}
            </div>
          ))}
        </div>

        {error && (
          <div
            style={{
              background: 'rgba(239, 68, 68, 0.3)',
              borderRadius: '8px',
              padding: '1.5rem',
              marginTop: '1rem',
              border: '2px solid #ef4444',
            }}
          >
            <h3 style={{ marginTop: 0 }}>⚠️ Erro Detectado:</h3>
            <pre
              style={{
                whiteSpace: 'pre-wrap',
                wordBreak: 'break-word',
                fontSize: '12px',
              }}
            >
              {error}
            </pre>
          </div>
        )}

        <div
          style={{
            marginTop: '2rem',
            padding: '1rem',
            background: 'rgba(255,255,255,0.1)',
            borderRadius: '8px',
            fontSize: '12px',
          }}
        >
          <p style={{ margin: '0.5rem 0' }}>📍 URL: {window.location.href}</p>
          <p style={{ margin: '0.5rem 0' }}>
            🌐 User Agent: {navigator.userAgent.substring(0, 80)}...
          </p>
          <p style={{ margin: '0.5rem 0' }}>⏰ Timestamp: {new Date().toLocaleString()}</p>
        </div>
      </div>
    </div>
  );
}

export default AppTest;
