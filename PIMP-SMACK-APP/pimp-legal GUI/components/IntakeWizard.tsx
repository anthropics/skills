import React, { useState } from 'react';
import { CaseData, PartyInfo, CaseInfo, Defendant } from '../types';
import { ArrowRight, ArrowLeft, User, Building, Scale, BookOpen, FileText, Target } from 'lucide-react';

interface Props {
  caseData: CaseData;
  updateCaseData: (data: Partial<CaseData>) => void;
  onComplete: () => void;
}

const steps = [
    { id: 1, title: 'Your Story', icon: BookOpen },
    { id: 2, title: 'The Bad Guys', icon: Building },
    { id: 3, title: 'Which Court?', icon: Scale },
    { id: 4, title: 'Evidence Check', icon: FileText },
    { id: 5, title: 'Relief', icon: Target },
    { id: 6, title: 'Who Are You?', icon: User },
];

export const IntakeWizard: React.FC<Props> = ({ caseData, updateCaseData, onComplete }) => {
  const [currentStep, setCurrentStep] = useState(1);

  const next = () => setCurrentStep(prev => Math.min(prev + 1, steps.length));
  const back = () => setCurrentStep(prev => Math.max(prev - 1, 1));
  const finish = () => onComplete();

  // Helper to update specific nested state
  const updateParty = (u: Partial<PartyInfo>) => updateCaseData({ partyInfo: { ...caseData.partyInfo, ...u } });
  const updateCase = (u: Partial<CaseInfo>) => updateCaseData({ caseInfo: { ...caseData.caseInfo, ...u } });
  const updateStory = (u: Partial<typeof caseData.story>) => updateCaseData({ story: { ...caseData.story, ...u } });
  
  const addDefendant = () => {
      const newDef: Defendant = {
          id: caseData.defendants.length + 1,
          name: '',
          role: 'Individual',
          description: ''
      };
      updateCaseData({ defendants: [...caseData.defendants, newDef] });
  };
  
  const updateDefendant = (id: number, u: Partial<Defendant>) => {
      const updated = caseData.defendants.map(d => d.id === id ? { ...d, ...u } : d);
      updateCaseData({ defendants: updated });
  };

  return (
    <div className="w-full max-w-4xl mx-auto p-6">
      {/* Progress Header */}
      <div className="mb-8">
        <h2 className="text-3xl font-display font-bold text-accent-cyan mb-2 glitch-text">INITIALIZING LAWSUIT PROTOCOL</h2>
        <div className="flex justify-between items-center mb-4">
            {steps.map(s => (
                <div key={s.id} className={`flex flex-col items-center ${s.id === currentStep ? 'text-accent-magenta' : s.id < currentStep ? 'text-accent-cyan' : 'text-gray-600'}`}>
                    <div className={`w-8 h-8 rounded-full flex items-center justify-center border-2 mb-1 ${s.id === currentStep ? 'border-accent-magenta bg-accent-magenta/20' : 'border-current'}`}>
                        <s.icon size={14} />
                    </div>
                    <span className="text-[10px] uppercase font-bold tracking-widest">{s.title}</span>
                </div>
            ))}
        </div>
        <div className="w-full h-1 bg-gray-800 rounded-full overflow-hidden">
            <div 
                className="h-full bg-gradient-to-r from-accent-cyan to-accent-magenta transition-all duration-300 ease-out"
                style={{ width: `${(currentStep / steps.length) * 100}%` }}
            />
        </div>
      </div>

      <div className="cyber-panel p-8 rounded-xl min-h-[400px]">
        {/* Step 6: Party Info (LAST) */}
        {currentStep === 6 && (
            <div className="space-y-6 animate-in fade-in slide-in-from-right-8">
                <h3 className="text-2xl font-bold text-white mb-4">Identify Yourself</h3>
                <div className="grid grid-cols-2 gap-4">
                    <div className="col-span-2">
                        <label className="block text-accent-cyan text-xs uppercase font-bold mb-1">Full Legal Name</label>
                        <input value={caseData.partyInfo.name} onChange={e => updateParty({ name: e.target.value, nameCaps: e.target.value.toUpperCase() })} className="w-full p-3 rounded" placeholder="John Q. Citizen" />
                    </div>
                    <div>
                        <label className="block text-accent-cyan text-xs uppercase font-bold mb-1">Role</label>
                        <select value={caseData.partyInfo.role} onChange={e => updateParty({ role: e.target.value as any })} className="w-full p-3 rounded">
                            <option value="Plaintiff">Plaintiff (Suing)</option>
                            <option value="Defendant">Defendant (Being Sued)</option>
                        </select>
                    </div>
                    <div>
                        <label className="block text-accent-cyan text-xs uppercase font-bold mb-1">Are you Pro Se?</label>
                        <select className="w-full p-3 rounded" disabled value="true">
                            <option value="true">Yes (Representing Self)</option>
                        </select>
                    </div>
                    <div className="col-span-2">
                        <label className="block text-accent-cyan text-xs uppercase font-bold mb-1">Mailing Address</label>
                        <input value={caseData.partyInfo.addressLine1} onChange={e => updateParty({ addressLine1: e.target.value })} className="w-full p-3 rounded mb-2" placeholder="123 Freedom Way" />
                        <input value={caseData.partyInfo.cityStateZip} onChange={e => updateParty({ cityStateZip: e.target.value })} className="w-full p-3 rounded" placeholder="Portland, OR 97204" />
                    </div>
                     <div>
                        <label className="block text-accent-cyan text-xs uppercase font-bold mb-1">Phone</label>
                        <input value={caseData.partyInfo.phone} onChange={e => updateParty({ phone: e.target.value })} className="w-full p-3 rounded" placeholder="555-0199" />
                    </div>
                     <div>
                        <label className="block text-accent-cyan text-xs uppercase font-bold mb-1">Email</label>
                        <input value={caseData.partyInfo.email} onChange={e => updateParty({ email: e.target.value })} className="w-full p-3 rounded" placeholder="you@example.com" />
                    </div>
                </div>
            </div>
        )}

        {/* Step 3: Court Info */}
        {currentStep === 3 && (
             <div className="space-y-6 animate-in fade-in slide-in-from-right-8">
                <h3 className="text-2xl font-bold text-white mb-4">Battlefield Selection</h3>
                <div className="grid grid-cols-1 gap-4">
                     <div>
                        <label className="block text-accent-cyan text-xs uppercase font-bold mb-1">Target Court</label>
                        <input value={caseData.caseInfo.courtName} onChange={e => updateCase({ courtName: e.target.value })} className="w-full p-3 rounded" />
                    </div>
                    <div>
                        <label className="block text-accent-cyan text-xs uppercase font-bold mb-1">Jurisdiction / Division</label>
                        <input value={caseData.caseInfo.jurisdiction} onChange={e => updateCase({ jurisdiction: e.target.value })} className="w-full p-3 rounded" placeholder="e.g. District of Oregon" />
                    </div>
                    <div>
                        <label className="block text-accent-cyan text-xs uppercase font-bold mb-1">Case Number (if assigned)</label>
                        <input value={caseData.caseInfo.caseNumber} onChange={e => updateCase({ caseNumber: e.target.value })} className="w-full p-3 rounded" placeholder="2:24-cv-00000" />
                    </div>
                </div>
            </div>
        )}

        {/* Step 2: Defendants */}
        {currentStep === 2 && (
             <div className="space-y-6 animate-in fade-in slide-in-from-right-8">
                <div className="flex justify-between items-center">
                    <h3 className="text-2xl font-bold text-white">The Opposition</h3>
                    <button onClick={addDefendant} className="bg-accent-magenta/20 border border-accent-magenta text-accent-magenta px-4 py-2 rounded hover:bg-accent-magenta hover:text-white transition-colors text-sm uppercase font-bold">
                        + Add Target
                    </button>
                </div>
                
                <div className="space-y-4 max-h-[400px] overflow-y-auto pr-2">
                    {caseData.defendants.length === 0 && <p className="text-gray-500 italic text-center py-8">No targets identified yet.</p>}
                    {caseData.defendants.map((def, idx) => (
                        <div key={def.id} className="bg-bg-primary p-4 rounded border border-gray-700 relative">
                            <div className="absolute top-2 right-2 text-[10px] text-gray-500 font-mono">ID: {def.id}</div>
                            <div className="grid grid-cols-2 gap-4">
                                <div className="col-span-2">
                                    <label className="block text-gray-500 text-[10px] uppercase font-bold mb-1">Name</label>
                                    <input value={def.name} onChange={e => updateDefendant(def.id, { name: e.target.value })} className="w-full p-2 rounded text-sm" placeholder="Officer Bad Actor" />
                                </div>
                                <div>
                                    <label className="block text-gray-500 text-[10px] uppercase font-bold mb-1">Type</label>
                                    <select value={def.role} onChange={e => updateDefendant(def.id, { role: e.target.value as any })} className="w-full p-2 rounded text-sm">
                                        <option value="Individual">Individual</option>
                                        <option value="Corporation">Corporation</option>
                                        <option value="Government">Government Entity</option>
                                        <option value="Official Capacity">Official Capacity</option>
                                    </select>
                                </div>
                                <div>
                                    <label className="block text-gray-500 text-[10px] uppercase font-bold mb-1">Brief Description</label>
                                    <input value={def.description} onChange={e => updateDefendant(def.id, { description: e.target.value })} className="w-full p-2 rounded text-sm" placeholder="What did they do?" />
                                </div>
                            </div>
                        </div>
                    ))}
                </div>
            </div>
        )}

        {/* Step 1: Story (FIRST!) */}
        {currentStep === 1 && (
             <div className="space-y-6 animate-in fade-in slide-in-from-right-8">
                <h3 className="text-2xl font-bold text-white mb-4">What Happened?</h3>
                <p className="text-gray-400 text-sm mb-4">Tell your story plainly. We'll worry about the legal jargon later.</p>
                <textarea 
                    value={caseData.story.whatHappened}
                    onChange={e => updateStory({ whatHappened: e.target.value })}
                    className="w-full h-64 p-4 rounded text-base leading-relaxed"
                    placeholder="On [Date], I was at [Location] when..."
                />
            </div>
        )}

        {/* Step 4: Evidence Check */}
        {currentStep === 4 && (
             <div className="space-y-6 animate-in fade-in slide-in-from-right-8">
                <h3 className="text-2xl font-bold text-white mb-4">Evidence Check</h3>
                <p className="text-gray-400 text-sm">Do you have any of the following? (You can upload files later)</p>
                <div className="grid grid-cols-2 gap-4">
                    {['Emails', 'Letters', 'Photos', 'Videos', 'Contracts', 'Witnesses'].map(type => (
                        <label key={type} className="flex items-center gap-3 p-4 bg-bg-primary rounded border border-gray-800 hover:border-accent-cyan cursor-pointer transition-all">
                            <input type="checkbox" className="w-5 h-5 accent-accent-cyan" />
                            <span className="text-white font-mono">{type}</span>
                        </label>
                    ))}
                </div>
            </div>
        )}

        {/* Step 5: Relief */}
        {currentStep === 5 && (
             <div className="space-y-6 animate-in fade-in slide-in-from-right-8">
                <h3 className="text-2xl font-bold text-white mb-4">What Do You Want?</h3>
                <div>
                    <label className="block text-accent-cyan text-xs uppercase font-bold mb-1">Damages (Money/Harm)</label>
                    <textarea value={caseData.story.whatYouLost} onChange={e => updateStory({ whatYouLost: e.target.value })} className="w-full h-32 p-3 rounded" placeholder="I lost my job, medical bills totaling $50k, emotional distress..." />
                </div>
                 <div>
                    <label className="block text-accent-cyan text-xs uppercase font-bold mb-1">Relief Requested</label>
                    <textarea value={caseData.story.whatYouWant} onChange={e => updateStory({ whatYouWant: e.target.value })} className="w-full h-32 p-3 rounded" placeholder="I want $100k in damages, my job back, and for them to stop..." />
                </div>
            </div>
        )}

      </div>

      {/* Navigation */}
      <div className="flex justify-between mt-8">
        <button 
            onClick={back} 
            disabled={currentStep === 1}
            className={`flex items-center gap-2 px-6 py-3 rounded font-bold uppercase tracking-wider ${currentStep === 1 ? 'opacity-0' : 'text-gray-400 hover:text-white'}`}
        >
            <ArrowLeft size={20} /> Back
        </button>

        {currentStep < steps.length ? (
            <button 
                onClick={next}
                className="bg-accent-cyan text-black px-8 py-3 rounded font-bold uppercase tracking-wider hover:bg-white hover:shadow-[0_0_20px_rgba(0,255,255,0.5)] transition-all flex items-center gap-2"
            >
                Next <ArrowRight size={20} />
            </button>
        ) : (
            <button 
                onClick={finish}
                className="bg-accent-magenta text-white px-8 py-3 rounded font-bold uppercase tracking-wider hover:shadow-[0_0_20px_rgba(255,0,255,0.5)] transition-all flex items-center gap-2"
            >
                ENTER WAR ROOM <Target size={20} />
            </button>
        )}
      </div>
    </div>
  );
};
