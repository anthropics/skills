import React, { useState } from 'react';
import { CaseData, DocumentDraft } from '../types';
import { generateDocx } from '../services/docxService';
import { Download, FileText, Bot } from 'lucide-react';
import { v4 as uuidv4 } from 'uuid';

interface Props {
  caseData: CaseData;
  onBack: () => void;
}

export const DocumentGenerator: React.FC<Props> = ({ caseData, onBack }) => {
  const [activeDraft, setActiveDraft] = useState<DocumentDraft | null>(null);
  const [isGenerating, setIsGenerating] = useState(false);
  const [pastedText, setPastedText] = useState('');
  const [selectedCourt, setSelectedCourt] = useState('ninth_circuit');
  const [showQuickFormat, setShowQuickFormat] = useState(true);

  const courts = [
    { id: 'ninth_circuit', name: 'Ninth Circuit Court of Appeals', font: 'Century Schoolbook 14pt' },
    { id: 'district_oregon', name: 'District of Oregon', font: 'Times New Roman 12pt' },
    { id: 'district_california', name: 'Central District of California', font: 'Times New Roman 12pt' },
    { id: 'clackamas_county', name: 'Clackamas County Circuit Court', font: 'Times New Roman 12pt' },
  ];

  const quickFormat = async () => {
    if (!pastedText.trim()) {
      alert('Paste your document text first!');
      return;
    }
    setIsGenerating(true);
    try {
      const quickDraft: DocumentDraft = {
        id: uuidv4(),
        type: 'Motion',
        title: 'FORMATTED_DOCUMENT',
        sections: [{ id: uuidv4(), heading: 'Document', content: pastedText }]
      };
      const blob = await generateDocx(caseData, quickDraft);
      const url = window.URL.createObjectURL(blob);
      const link = window.document.createElement('a');
      link.href = url;
      link.download = `FORMATTED_${selectedCourt.toUpperCase()}.docx`;
      window.document.body.appendChild(link);
      link.click();
      window.document.body.removeChild(link);
    } catch (e) {
      console.error(e);
      alert("Error generating document");
    } finally {
      setIsGenerating(false);
    }
  };

  const startDraft = (type: DocumentDraft['type']) => {
      const newDraft: DocumentDraft = {
          id: uuidv4(),
          type,
          title: type === 'Complaint' ? 'COMPLAINT FOR DAMAGES AND INJUNCTIVE RELIEF' : `MOTION FOR ${type.toUpperCase()}`,
          sections: [
              { id: uuidv4(), heading: 'Introduction', content: caseData.story.whatHappened.substring(0, 500) + '...' },
              { id: uuidv4(), heading: 'Jurisdiction', content: 'This Court has subject matter jurisdiction pursuant to 28 U.S.C. § 1331 because this action arises under the Constitution and laws of the United States.' },
              { id: uuidv4(), heading: 'Parties', content: `Plaintiff ${caseData.partyInfo.name} is a resident of ${caseData.partyInfo.cityStateZip}.` },
              { id: uuidv4(), heading: 'Factual Allegations', content: caseData.story.whatHappened },
              { id: uuidv4(), heading: 'Claims for Relief', content: 'PLAINTIFF REALLEGES and incorporates by reference the paragraphs above.' },
              { id: uuidv4(), heading: 'Prayer for Relief', content: caseData.story.whatYouWant }
          ]
      };
      setActiveDraft(newDraft);
  };

  const updateSection = (id: string, content: string) => {
      if (!activeDraft) return;
      const updatedSections = activeDraft.sections.map(s => s.id === id ? { ...s, content } : s);
      setActiveDraft({ ...activeDraft, sections: updatedSections });
  };

  const handleDownload = async () => {
      if (!activeDraft) return;
      setIsGenerating(true);
      try {
          const blob = await generateDocx(caseData, activeDraft);
          const url = window.URL.createObjectURL(blob);
          const link = window.document.createElement('a');
          link.href = url;
          link.download = `${activeDraft.title.replace(/\s+/g, '_')}.docx`;
          window.document.body.appendChild(link);
          link.click();
          window.document.body.removeChild(link);
      } catch (e) {
          console.error(e);
          alert("Firing mechanism jammed. Check console.");
      } finally {
          setIsGenerating(false);
      }
  };

  if (activeDraft) {
      return (
          <div className="p-6 max-w-5xl mx-auto h-screen flex flex-col">
              <div className="flex justify-between items-center mb-6">
                  <div>
                    <h2 className="text-2xl font-display font-bold text-white">{activeDraft.title}</h2>
                    <span className="text-xs font-mono text-accent-cyan">DRAFTING MODE</span>
                  </div>
                  <div className="flex gap-4">
                      <button onClick={() => setActiveDraft(null)} className="text-gray-400 hover:text-white px-4">Discard</button>
                      <button 
                        onClick={handleDownload}
                        className="bg-accent-magenta text-white px-6 py-2 rounded font-bold uppercase flex items-center gap-2 hover:shadow-[0_0_15px_rgba(255,0,255,0.5)] transition-all"
                      >
                         {isGenerating ? 'Firing...' : 'Fire Cannon (.docx)'} <Download size={18} />
                      </button>
                  </div>
              </div>

              <div className="flex-1 overflow-y-auto space-y-6 pr-4">
                  {activeDraft.sections.map((section) => (
                      <div key={section.id} className="cyber-panel p-6 rounded-xl">
                          <div className="flex justify-between items-center mb-2">
                            <h3 className="text-lg font-bold text-accent-yellow uppercase">{section.heading}</h3>
                            <button className="text-xs text-accent-cyan flex items-center gap-1 opacity-50 hover:opacity-100">
                                <Bot size={12} /> AI Assist
                            </button>
                          </div>
                          <textarea 
                            value={section.content}
                            onChange={(e) => updateSection(section.id, e.target.value)}
                            className="w-full h-48 bg-bg-primary p-4 rounded text-sm leading-relaxed border border-gray-800 focus:border-accent-cyan transition-colors font-serif text-gray-300"
                          />
                      </div>
                  ))}
              </div>
          </div>
      )
  }

  return (
    <div className="p-6 max-w-7xl mx-auto space-y-8">
         <div className="flex items-center justify-between">
            <h2 className="text-3xl font-display font-bold text-white glitch-text">FORMAT YOUR DOCUMENT</h2>
            <button onClick={onBack} className="text-gray-400 hover:text-white font-mono uppercase text-sm">← Back</button>
        </div>

        {/* QUICK FORMAT - THE MAIN PRODUCT */}
        <div className="cyber-panel p-8 rounded-xl border-2 border-accent-magenta">
            <h3 className="text-xl font-bold text-accent-magenta mb-4">⚡ QUICK FORMAT</h3>
            <p className="text-gray-400 text-sm mb-4">Paste your text below. We'll format it for your court.</p>
            
            <div className="grid grid-cols-1 md:grid-cols-3 gap-4 mb-4">
                <div className="md:col-span-2">
                    <label className="block text-accent-cyan text-xs uppercase font-bold mb-1">Select Court</label>
                    <select 
                        value={selectedCourt} 
                        onChange={(e) => setSelectedCourt(e.target.value)}
                        className="w-full p-3 rounded bg-bg-primary border border-gray-700"
                        title="Select your court"
                    >
                        {courts.map(c => (
                            <option key={c.id} value={c.id}>{c.name} ({c.font})</option>
                        ))}
                    </select>
                </div>
                <div className="flex items-end">
                    <button 
                        onClick={quickFormat}
                        disabled={isGenerating}
                        className="w-full bg-accent-magenta text-white px-6 py-3 rounded font-bold uppercase hover:shadow-[0_0_20px_rgba(255,0,255,0.5)] transition-all disabled:opacity-50"
                    >
                        {isGenerating ? 'Generating...' : '⬇ DOWNLOAD .DOCX'}
                    </button>
                </div>
            </div>
            
            <textarea 
                value={pastedText}
                onChange={(e) => setPastedText(e.target.value)}
                placeholder="Paste your document text here... We'll handle the formatting (margins, fonts, spacing, etc.)"
                className="w-full h-64 p-4 rounded bg-bg-primary border border-gray-700 focus:border-accent-magenta transition-colors text-sm"
            />
        </div>

        {/* Advanced - Build from Template */}
        <div className="border-t border-gray-800 pt-8">
            <h3 className="text-lg font-bold text-gray-500 mb-4">Or: Build from Template</h3>
            <div className="grid grid-cols-2 md:grid-cols-5 gap-4">
                {['Complaint', 'Motion', 'Brief', 'Notice', 'Declaration'].map(type => (
                <button 
                    key={type}
                    onClick={() => startDraft(type as any)}
                    className="cyber-panel p-8 rounded-xl hover:bg-bg-card hover:border-accent-cyan transition-all group text-left relative overflow-hidden"
                >
                    <div className="absolute top-0 right-0 p-4 opacity-5 group-hover:opacity-10 transition-opacity">
                        <FileText size={100} />
                    </div>
                    <h3 className="text-2xl font-bold text-white mb-2">{type.toUpperCase()}</h3>
                    <p className="text-sm text-gray-400">Initiate drafting sequence for standard federal {type.toLowerCase()}.</p>
                    <div className="mt-4 text-accent-cyan text-xs font-mono opacity-0 group-hover:opacity-100 transition-opacity">
                        CLICK TO INITIALIZE {'->'}
                    </div>
                </button>
            ))}
            </div>
        </div>
    </div>
  );
};
