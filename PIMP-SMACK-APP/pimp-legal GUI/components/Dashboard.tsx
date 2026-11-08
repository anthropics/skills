import React from 'react';
import { CaseData, Deadline } from '../types';
import { AlertTriangle, FileText, Target, Clock, Shield, Upload } from 'lucide-react';
import { AVAILABLE_CLAIMS } from '../constants';

interface Props {
  caseData: CaseData;
  onChangeView: (view: string) => void;
}

export const Dashboard: React.FC<Props> = ({ caseData, onChangeView }) => {
  const nextDeadline = caseData.deadlines[0]; // Simplification for MVP

  return (
    <div className="space-y-8 p-6 max-w-7xl mx-auto">
      {/* Header Info */}
      <div className="flex justify-between items-end border-b border-gray-800 pb-4">
        <div>
            <h1 className="text-4xl font-display font-black text-white glitch-text mb-2">WAR ROOM</h1>
            <div className="flex items-center gap-4 text-sm font-mono text-gray-400">
                <span>CASE: <span className="text-accent-cyan">{caseData.caseInfo.caseNumber || 'UNASSIGNED'}</span></span>
                <span>STATUS: <span className="text-accent-yellow">BUILDING CASE</span></span>
                <span>ROLE: <span className="text-white">{caseData.partyInfo.role.toUpperCase()}</span></span>
            </div>
        </div>
        <div className="text-right">
             <div className="text-xs text-gray-500 uppercase font-bold tracking-widest mb-1">Opponent</div>
             <div className="text-accent-magenta font-bold text-lg">
                {caseData.defendants.length > 0 ? caseData.defendants[0].name : 'UNKNOWN'} 
                {caseData.defendants.length > 1 && ` +${caseData.defendants.length - 1}`}
             </div>
        </div>
      </div>

      {/* Main Grid */}
      <div className="grid grid-cols-1 lg:grid-cols-3 gap-6">
        
        {/* DEADLINE CARD (PIMP CLAP CARD) */}
        <div className="lg:col-span-1">
            <div className="cyber-panel p-6 rounded-xl h-full border-t-4 border-status-danger relative overflow-hidden group">
                 <div className="absolute top-0 right-0 p-4 opacity-10 group-hover:opacity-20 transition-opacity">
                    <AlertTriangle size={100} />
                 </div>
                 <h3 className="text-status-danger font-display font-bold text-xl mb-4 flex items-center gap-2">
                    <Clock className="animate-pulse-fast" /> IMMINENT THREAT
                 </h3>
                 
                 {nextDeadline ? (
                     <div className="space-y-4">
                        <div className="text-4xl font-bold text-white mb-2">
                            {Math.ceil((new Date(nextDeadline.dueDate).getTime() - Date.now()) / (1000 * 3600 * 24))} DAYS
                        </div>
                        <div>
                            <div className="text-xs text-gray-500 uppercase font-bold">Action Required</div>
                            <div className="text-lg text-white font-bold">{nextDeadline.name}</div>
                        </div>
                        <div>
                            <div className="text-xs text-gray-500 uppercase font-bold">Consequence</div>
                            <div className="text-status-danger font-bold uppercase">{nextDeadline.consequence}</div>
                        </div>
                     </div>
                 ) : (
                     <div className="text-gray-500">No active threats detected. Stay vigilant.</div>
                 )}
            </div>
        </div>

        {/* ACTION MODULES */}
        <div className="lg:col-span-2 grid grid-cols-2 gap-4">
            
            <button onClick={() => onChangeView('claims')} className="cyber-panel p-6 rounded-xl hover:bg-bg-card transition-all text-left group border-l-4 border-accent-cyan">
                <div className="flex justify-between items-start mb-4">
                    <Shield size={32} className="text-accent-cyan group-hover:scale-110 transition-transform" />
                    <span className="text-2xl font-bold text-white">{caseData.claims.length}</span>
                </div>
                <h4 className="font-display font-bold text-lg text-white mb-1">Claims / Offense</h4>
                <p className="text-xs text-gray-400">Select weapons and map elements to evidence.</p>
            </button>

            <button onClick={() => onChangeView('evidence')} className="cyber-panel p-6 rounded-xl hover:bg-bg-card transition-all text-left group border-l-4 border-accent-magenta">
                <div className="flex justify-between items-start mb-4">
                    <Upload size={32} className="text-accent-magenta group-hover:scale-110 transition-transform" />
                    <span className="text-2xl font-bold text-white">{caseData.evidence.length}</span>
                </div>
                <h4 className="font-display font-bold text-lg text-white mb-1">Evidence Locker</h4>
                <p className="text-xs text-gray-400">Load ammo. Tag files. Link to claims.</p>
            </button>

            <button onClick={() => onChangeView('timeline')} className="cyber-panel p-6 rounded-xl hover:bg-bg-card transition-all text-left group border-l-4 border-accent-yellow">
                <div className="flex justify-between items-start mb-4">
                    <Clock size={32} className="text-accent-yellow group-hover:scale-110 transition-transform" />
                    <span className="text-2xl font-bold text-white">{caseData.timeline.length}</span>
                </div>
                <h4 className="font-display font-bold text-lg text-white mb-1">Timeline</h4>
                <p className="text-xs text-gray-400">Visualize the corruption chronologically.</p>
            </button>

            <button onClick={() => onChangeView('documents')} className="cyber-panel p-6 rounded-xl hover:bg-bg-card transition-all text-left group border-l-4 border-white bg-accent-cyan/10">
                <div className="flex justify-between items-start mb-4">
                    <FileText size={32} className="text-white group-hover:scale-110 transition-transform" />
                    <span className="text-2xl font-bold text-white">{caseData.documents.length}</span>
                </div>
                <h4 className="font-display font-bold text-lg text-white mb-1">Fire Cannon</h4>
                <p className="text-xs text-gray-400">Generate Court-Ready Documents.</p>
            </button>
        </div>
      </div>

      {/* Recent Activity Log (Fake for Visual) */}
      <div className="cyber-panel p-6 rounded-xl">
        <h4 className="text-xs uppercase font-bold text-gray-500 mb-4 tracking-widest">System Logs</h4>
        <div className="space-y-3 font-mono text-sm">
            <div className="flex gap-4">
                <span className="text-gray-600">10:42:01</span>
                <span className="text-accent-cyan">[SYSTEM]</span>
                <span className="text-gray-300">Case initialized. Protocol active.</span>
            </div>
            {caseData.claims.length > 0 && (
                <div className="flex gap-4">
                    <span className="text-gray-600">10:45:22</span>
                    <span className="text-accent-magenta">[OFFENSE]</span>
                    <span className="text-gray-300">Added Claim: {caseData.claims[0].name}</span>
                </div>
            )}
        </div>
      </div>
    </div>
  );
};
