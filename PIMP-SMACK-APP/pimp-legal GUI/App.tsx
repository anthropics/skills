import React, { useState, useEffect } from 'react';
import { CaseData, ViewState } from './types';
import { INITIAL_CASE_DATA } from './constants';
import { IntakeWizard } from './components/IntakeWizard';
import { Dashboard } from './components/Dashboard';
import { ClaimsBuilder } from './components/ClaimsBuilder';
import { DocumentGenerator } from './components/DocumentGenerator';
import { Shield, Settings } from 'lucide-react';

function App() {
  const [view, setView] = useState<ViewState>('landing');
  const [caseData, setCaseData] = useState<CaseData>(INITIAL_CASE_DATA);
  const [isLoaded, setIsLoaded] = useState(false);

  // Load from local storage
  useEffect(() => {
    const saved = localStorage.getItem('pimp_case_data');
    if (saved) {
        try {
            setCaseData(JSON.parse(saved));
            setView('dashboard'); // Auto-login to dashboard if data exists
        } catch (e) {
            console.error("Failed to load save data", e);
        }
    }
    setIsLoaded(true);
  }, []);

  // Save to local storage on change
  useEffect(() => {
    if (isLoaded) {
        localStorage.setItem('pimp_case_data', JSON.stringify(caseData));
    }
  }, [caseData, isLoaded]);

  const updateCaseData = (updates: Partial<CaseData>) => {
      setCaseData(prev => ({ ...prev, ...updates }));
  };

  const handleReset = () => {
      if(confirm("NUKE EVERYTHING? This cannot be undone.")) {
          localStorage.removeItem('pimp_case_data');
          setCaseData(INITIAL_CASE_DATA);
          setView('landing');
      }
  };

  // --- VIEWS ---

  if (view === 'landing') {
      return (
          <div className="min-h-screen bg-bg-primary text-gray-200 overflow-x-hidden">
              {/* HERO SECTION */}
              <section className="relative min-h-screen flex flex-col items-center justify-center p-4">
                  <div className="absolute inset-0 bg-[url('https://images.unsplash.com/photo-1550684848-fac1c5b4e853?q=80&w=2070&auto=format&fit=crop')] bg-cover opacity-10 blur-sm pointer-events-none"></div>
                  <div className="z-10 text-center max-w-3xl space-y-8">
                      <div className="mb-8">
                           <h1 className="text-6xl font-display font-black text-white mb-2 glitch-text">PIMP LEGAL</h1>
                           <p className="text-accent-cyan font-mono tracking-widest text-sm">PRO SE INTELLIGENT MOTION PROCESSOR</p>
                      </div>
                      
                      <div className="space-y-6">
                          <button 
                            onClick={() => setView('documents')}
                            className="bg-accent-magenta text-white px-12 py-6 rounded-lg font-bold uppercase tracking-wider hover:bg-white hover:text-black hover:shadow-[0_0_40px_rgba(255,0,255,0.7)] transition-all text-2xl w-full"
                            title="Format your legal document"
                          >
                            ⚡ FORMAT MY DOCUMENT
                          </button>
                          
                          <p className="text-accent-cyan text-lg font-mono">Cheaper than a cheeseburger 🍔</p>
                          <p className="text-gray-500 text-sm">Paste → Pick Court → Download DOCX</p>
                      </div>
                      
                      <div className="mt-12 animate-bounce">
                          <p className="text-gray-600 text-xs">↓ See How It Works ↓</p>
                      </div>
                  </div>
              </section>

              {/* VIDEO SECTION */}
              <section className="py-20 px-4 bg-bg-secondary">
                  <div className="max-w-4xl mx-auto text-center">
                      <h2 className="text-3xl font-display font-bold text-white mb-4">WHITE GLOVE JUSTICE</h2>
                      <p className="text-gray-400 mb-8">Watch how proper formatting punches corruption in the face</p>
                      
                      {/* WHITE GLOVE JUSTICE VIDEO */}
                      <video 
                        src="/white-glove-justice.mp4" 
                        controls 
                        className="w-full rounded-xl shadow-2xl"
                        poster=""
                      >
                        Your browser does not support video playback.
                      </video>
                  </div>
              </section>

              {/* FORMATTING TOOLS SHOWCASE */}
              <section className="py-20 px-4">
                  <div className="max-w-6xl mx-auto">
                      <h2 className="text-3xl font-display font-bold text-white text-center mb-4">FORMATTING ARSENAL</h2>
                      <p className="text-gray-400 text-center mb-12">Court-perfect documents. Every time.</p>
                      
                      <div className="grid md:grid-cols-3 gap-6">
                          {/* Tool Card 1 */}
                          <div className="bg-bg-secondary border border-gray-800 rounded-xl p-6 hover:border-accent-cyan transition-colors">
                              <div className="text-4xl mb-4">📋</div>
                              <h3 className="text-xl font-bold text-white mb-2">Ninth Circuit Formatter</h3>
                              <p className="text-gray-400 text-sm mb-4">Century Schoolbook 14pt, FRAP 28 compliant, automatic TOC/TOA generation</p>
                              <p className="text-accent-cyan font-mono text-xs">Appellate briefs • Motions • Declarations</p>
                          </div>
                          
                          {/* Tool Card 2 */}
                          <div className="bg-bg-secondary border border-gray-800 rounded-xl p-6 hover:border-accent-magenta transition-colors">
                              <div className="text-4xl mb-4">⚖️</div>
                              <h3 className="text-xl font-bold text-white mb-2">District Court Formatter</h3>
                              <p className="text-gray-400 text-sm mb-4">Times New Roman 12pt, local rule compliance, automatic caption generation</p>
                              <p className="text-accent-magenta font-mono text-xs">Complaints • Answers • Motions</p>
                          </div>
                          
                          {/* Tool Card 3 */}
                          <div className="bg-bg-secondary border border-gray-800 rounded-xl p-6 hover:border-accent-yellow transition-colors">
                              <div className="text-4xl mb-4">🏛️</div>
                              <h3 className="text-xl font-bold text-white mb-2">State Court Formatter</h3>
                              <p className="text-gray-400 text-sm mb-4">Clackamas County, Oregon state courts, jurisdiction-specific styling</p>
                              <p className="text-accent-yellow font-mono text-xs">State filings • Local forms</p>
                          </div>
                      </div>
                  </div>
              </section>

              {/* SKILL PACK PURCHASE */}
              <section className="py-20 px-4 bg-bg-secondary">
                  <div className="max-w-4xl mx-auto text-center">
                      <h2 className="text-3xl font-display font-bold text-white mb-4">GET THE SKILL PACK</h2>
                      <p className="text-gray-400 mb-8">Download the skills. Use with Claude, ChatGPT, or any AI. Format unlimited documents.</p>
                      
                      <div className="bg-gradient-to-br from-gray-900 to-bg-primary border border-accent-cyan rounded-2xl p-8 max-w-md mx-auto">
                          <p className="text-accent-cyan font-mono text-sm mb-2">PRO SE FORMATTING SKILLS</p>
                          <p className="text-5xl font-display font-black text-white mb-4">$4.99</p>
                          <p className="text-gray-500 text-sm mb-6">One-time purchase. Forever yours.</p>
                          
                          <ul className="text-left text-gray-300 text-sm space-y-2 mb-8">
                              <li>✓ All 18 formatting skills</li>
                              <li>✓ Court-specific profiles (Ninth Circuit, District, State)</li>
                              <li>✓ Python scripts for automation</li>
                              <li>✓ Works with Claude, ChatGPT, Gemini</li>
                              <li>✓ Unlimited document formatting</li>
                          </ul>
                          
                          <a 
                            href="#" 
                            className="block bg-accent-cyan text-black px-8 py-4 rounded-lg font-bold uppercase tracking-wider hover:bg-white transition-colors"
                          >
                            Download on App Store
                          </a>
                          <p className="text-gray-600 text-xs mt-4">Also available on Google Play</p>
                      </div>
                  </div>
              </section>

              {/* FOOTER CTA */}
              <section className="py-12 px-4 text-center border-t border-gray-800">
                  <p className="text-gray-500 text-sm mb-4">Ready to stop getting destroyed by procedural games?</p>
                  <button 
                    onClick={() => setView('documents')}
                    className="bg-accent-magenta text-white px-8 py-4 rounded-lg font-bold uppercase tracking-wider hover:bg-white hover:text-black transition-all"
                    title="Try formatting now"
                  >
                    Try It Free →
                  </button>
              </section>
          </div>
      );
  }

  return (
    <div className="min-h-screen bg-bg-primary text-gray-200 font-sans selection:bg-accent-magenta/30 selection:text-white">
        {/* Top Nav */}
        <nav className="border-b border-gray-800 bg-bg-secondary/50 backdrop-blur-md sticky top-0 z-50">
            <div className="max-w-7xl mx-auto px-6 h-16 flex items-center justify-between">
                <button onClick={() => setView('dashboard')} className="flex items-center gap-2 group">
                    <Shield className="text-accent-cyan group-hover:text-white transition-colors" />
                    <span className="font-display font-bold text-lg tracking-wider">PIMP <span className="text-gray-500 group-hover:text-gray-300">LEGAL</span></span>
                </button>
                
                <div className="flex items-center gap-6">
                    {view !== 'dashboard' && view !== 'intake' && (
                        <button onClick={() => setView('dashboard')} className="text-sm font-bold text-gray-400 hover:text-white uppercase">
                            Return to War Room
                        </button>
                    )}
                    <button onClick={handleReset} className="text-gray-600 hover:text-status-danger transition-colors">
                        <Settings size={18} />
                    </button>
                </div>
            </div>
        </nav>

        {/* View Router */}
        <main className="animate-in fade-in duration-300">
            {view === 'intake' && (
                <IntakeWizard 
                    caseData={caseData} 
                    updateCaseData={updateCaseData} 
                    onComplete={() => setView('dashboard')} 
                />
            )}
            
            {view === 'dashboard' && (
                <Dashboard 
                    caseData={caseData} 
                    onChangeView={(v) => setView(v as ViewState)} 
                />
            )}

            {view === 'claims' && (
                <ClaimsBuilder 
                    caseData={caseData} 
                    updateCaseData={updateCaseData}
                    onBack={() => setView('dashboard')}
                />
            )}

            {view === 'documents' && (
                <DocumentGenerator 
                    caseData={caseData}
                    onBack={() => setView('dashboard')}
                />
            )}

            {/* Placeholders for other views */}
            {(view === 'evidence' || view === 'timeline') && (
                <div className="flex flex-col items-center justify-center h-[80vh] text-center">
                    <h2 className="text-4xl font-display font-bold text-gray-700 mb-4">MODULE UNDER CONSTRUCTION</h2>
                    <p className="text-accent-cyan font-mono">Construction Drones Deployed.</p>
                    <button onClick={() => setView('dashboard')} className="mt-8 text-white hover:underline">Return to Base</button>
                </div>
            )}
        </main>
    </div>
  );
}

export default App;
