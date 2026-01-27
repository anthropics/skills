function AppTest() {
  return (
    <div
      style={{
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
        height: '100vh',
        background: 'linear-gradient(135deg, #667eea 0%, #764ba2 100%)',
        color: 'white',
        fontFamily: 'Arial, sans-serif',
      }}
    >
      <div style={{ textAlign: 'center' }}>
        <h1 style={{ fontSize: '4rem', margin: 0 }}>🎹</h1>
        <h2 style={{ fontSize: '2rem', marginTop: '1rem' }}>Piano Tutor</h2>
        <p style={{ fontSize: '1.2rem', marginTop: '1rem' }}>Carregando...</p>
        <div
          style={{
            marginTop: '2rem',
            padding: '1rem',
            background: 'rgba(255,255,255,0.1)',
            borderRadius: '8px',
          }}
        >
          <p style={{ margin: '0.5rem 0' }}>✅ React carregado</p>
          <p style={{ margin: '0.5rem 0' }}>✅ Vite funcionando</p>
          <p style={{ margin: '0.5rem 0' }}>⚙️ Testando componentes...</p>
        </div>
      </div>
    </div>
  );
}

export default AppTest;
