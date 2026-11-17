// --- PIMP Legal Master Schema ---

export interface PartyInfo {
  name: string;
  nameCaps: string;
  addressLine1: string;
  addressLine2?: string;
  cityStateZip: string;
  email: string;
  phone: string;
  role: 'Plaintiff' | 'Defendant' | 'Appellant' | 'Appellee';
  proSe: boolean;
}

export interface CaseInfo {
  caseNumber: string;
  courtName: string;
  courtType: 'district' | 'appeals' | 'state' | 'bankruptcy';
  jurisdiction: string; // e.g., "District of Oregon"
  judgeName?: string;
  lowerCourtCase?: string;
  lowerCourtName?: string;
  filingDate?: string;
}

export interface Defendant {
  id: number;  // 1-9, used in UID
  name: string;
  role: 'Individual' | 'Corporation' | 'Government' | 'Official Capacity';
  description: string;
}

export interface ClaimElement {
  elementNumber: number;  // 1-9, used in UID
  name: string;
  description: string;
  satisfied: boolean;
  evidenceIds: string[];
}

export interface Claim {
  id: string; // Internal UUID
  claimNumber: number;  // 1-9, used in UID
  name: string;
  statute: string;
  elements: ClaimElement[];
  defendantIds: number[];
}

export interface Evidence {
  id: string;
  type: 'document' | 'email' | 'photo' | 'video' | 'testimony' | 'admission' | 'other';
  description: string;
  date?: string;
  filePath?: string; // Placeholder for file reference
  fileName?: string;
  uidsSatisfied: string[];  // e.g., ["111", "121", "231"]
  keyQuote?: string;
}

export interface TimelineEvent {
  id: string;
  date: string;
  description: string;
  actors: string[]; // Defendant names or "Self"
  evidenceIds: string[];
  claimUids: string[];
}

export interface Deadline {
  id: string;
  name: string;
  dueDate: string;
  rule: string;
  consequence: string;
  status: 'not_started' | 'in_progress' | 'complete';
  urgency: 'low' | 'medium' | 'high' | 'critical';
}

export interface DocumentSection {
  id: string;
  heading: string;
  content: string;
  aiPrompt?: string;
}

export interface DocumentDraft {
  id: string;
  type: 'Complaint' | 'Motion' | 'Declaration' | 'Brief' | 'Notice';
  title: string;
  sections: DocumentSection[];
}

export interface CaseData {
  partyInfo: PartyInfo;
  caseInfo: CaseInfo;
  defendants: Defendant[];
  claims: Claim[];
  evidence: Evidence[];
  timeline: TimelineEvent[];
  deadlines: Deadline[];
  story: {
    whatHappened: string;
    whatYouLost: string;
    whatYouWant: string;
  };
  documents: DocumentDraft[];
}

// --- App UI State ---

export type ViewState = 'landing' | 'intake' | 'dashboard' | 'claims' | 'evidence' | 'timeline' | 'documents' | 'deadlines';

export interface AIModelConfig {
  id: string;
  name: string;
  provider: 'google' | 'anthropic' | 'openai';
  isAvailable: boolean;
}

export interface LogEntry {
  timestamp: string;
  model: string;
  type: 'request' | 'response' | 'error';
  content: string;
}
