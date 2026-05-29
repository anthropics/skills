import React from 'react';
import { CaseData, Claim } from '../types';
import { AVAILABLE_CLAIMS } from '../constants';
import { Plus, Trash2, CheckCircle, AlertCircle } from 'lucide-react';
import { v4 as uuidv4 } from 'uuid';

interface Props {
  caseData: CaseData;
  updateCaseData: (data: Partial<CaseData>) => void;
  onBack: () => void;
}

export const ClaimsBuilder: React.FC<Props> = ({ caseData, updateCaseData, onBack }) => {
  
  const addClaim = (template: Partial<Claim>) => {
      const newClaim: Claim = {
          id: uuidv4(),
          claimNumber: caseData.claims.length + 1,
          name: template.name!,
          statute: template.statute!,
          elements: template.elements!.map(e => ({...e})),
          defendantIds: []
      };
      updateCaseData({ claims: [...caseData.claims, newClaim] });
  };

  const removeClaim = (id: string) => {
      updateCaseData({ claims: caseData.claims.filter(c => c.id !== id) });
  };

  return (
    <div className="p-6 max-w-7xl mx-auto space-y-6">
        <div className="flex items-center justify-between mb-6">
            <h2 className="text-3xl font-display font-bold text-accent-cyan glitch-text">CHOOSE YOUR WEAPONS</h2>
            <button onClick={onBack} className="text-gray-400 hover:text-white font-mono uppercase text-sm">Esc / Back</button>
        </div>

        <div className="grid grid-cols-1 md:grid-cols-3 gap-6">
            {/* Library */}
            <div className="cyber-panel p-6 rounded-xl md:col-span-1 h-fit">
                <h3 className="text-xl font-bold text-white mb-4 border-b border-gray-700 pb-2">Armory</h3>
                <div className="space-y-3">
                    {AVAILABLE_CLAIMS.map((claim, idx) => (
                        <button 
                            key={idx}
                            onClick={() => addClaim(claim)}
                            className="w-full text-left p-3 rounded bg-bg-primary border border-gray-700 hover:border-accent-cyan hover:shadow-[0_0_10px_rgba(0,255,255,0.2)] transition-all group"
                        >
                            <div className="font-bold text-sm text-gray-200 group-hover:text-white">{claim.name}</div>
                            <div className="text-[10px] text-gray-500 font-mono mt-1">{claim.statute}</div>
                        </button>
                    ))}
                </div>
            </div>

            {/* Active Claims */}
            <div className="md:col-span-2 space-y-6">
                {caseData.claims.length === 0 && (
                    <div className="flex items-center justify-center h-64 border-2 border-dashed border-gray-800 rounded-xl text-gray-600 font-mono">
                        NO CLAIMS SELECTED. SELECT FROM ARMORY.
                    </div>
                )}
                
                {caseData.claims.map((claim) => (
                    <div key={claim.id} className="cyber-panel p-6 rounded-xl border-l-4 border-accent-magenta">
                        <div className="flex justify-between items-start mb-4">
                            <div>
                                <div className="text-[10px] font-mono text-accent-magenta mb-1">CLAIM #{claim.claimNumber}</div>
                                <h3 className="text-xl font-bold text-white">{claim.name}</h3>
                                <div className="text-xs text-gray-400 font-mono">{claim.statute}</div>
                            </div>
                            <button onClick={() => removeClaim(claim.id)} className="text-gray-600 hover:text-status-danger transition-colors">
                                <Trash2 size={18} />
                            </button>
                        </div>

                        <div className="space-y-2 mt-4">
                            <h4 className="text-xs uppercase font-bold text-gray-500 mb-2">Elements Required To Prove:</h4>
                            {claim.elements.map((el) => (
                                <div key={el.elementNumber} className="flex items-center gap-3 bg-bg-primary/50 p-2 rounded">
                                    <div className={`w-2 h-2 rounded-full ${el.satisfied ? 'bg-status-success' : 'bg-status-danger'}`}></div>
                                    <div className="flex-1">
                                        <div className="text-sm font-bold text-gray-300">
                                            <span className="font-mono text-gray-600 mr-2">E{el.elementNumber}</span> 
                                            {el.name}
                                        </div>
                                        <div className="text-[10px] text-gray-500">{el.description}</div>
                                    </div>
                                    <div className="text-[10px] font-mono text-accent-cyan opacity-50">
                                        UID: {claim.claimNumber}{el.elementNumber}*
                                    </div>
                                </div>
                            ))}
                        </div>
                    </div>
                ))}
            </div>
        </div>
    </div>
  );
};
