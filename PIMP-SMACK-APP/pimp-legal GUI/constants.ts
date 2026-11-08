import { CaseData, Claim, Deadline } from './types';

export const INITIAL_CASE_DATA: CaseData = {
  partyInfo: {
    name: '',
    nameCaps: '',
    addressLine1: '',
    addressLine2: '',
    cityStateZip: '',
    email: '',
    phone: '',
    role: 'Plaintiff',
    proSe: true
  },
  caseInfo: {
    caseNumber: '',
    courtName: 'United States District Court',
    courtType: 'district',
    jurisdiction: 'District of Oregon',
    judgeName: '',
  },
  defendants: [],
  claims: [],
  evidence: [],
  timeline: [],
  deadlines: [
    {
      id: 'd1',
      name: 'Complaint Filing',
      dueDate: new Date(Date.now() + 86400000 * 30).toISOString().split('T')[0],
      rule: 'Statute of Limitations',
      consequence: 'CASE BARRED FOREVER',
      status: 'in_progress',
      urgency: 'high'
    }
  ],
  story: {
    whatHappened: '',
    whatYouLost: '',
    whatYouWant: ''
  },
  documents: []
};

// --- TEMPLATES ---

export const AVAILABLE_CLAIMS: Partial<Claim>[] = [
  {
    name: '42 U.S.C. § 1983 - Deprivation of Rights',
    statute: '42 U.S.C. § 1983',
    elements: [
      { elementNumber: 1, name: 'Under Color of Law', description: 'Defendant acted under state/local authority', satisfied: false, evidenceIds: [] },
      { elementNumber: 2, name: 'Deprivation of Right', description: 'Plaintiff was deprived of a Constitutionally protected right', satisfied: false, evidenceIds: [] },
      { elementNumber: 3, name: 'Causation', description: 'Defendant\'s conduct caused the harm', satisfied: false, evidenceIds: [] }
    ]
  },
  {
    name: 'Title VII - Employment Discrimination',
    statute: '42 U.S.C. § 2000e',
    elements: [
      { elementNumber: 1, name: 'Protected Class', description: 'Member of protected class (race, color, religion, sex, national origin)', satisfied: false, evidenceIds: [] },
      { elementNumber: 2, name: 'Qualified', description: 'Qualified for the position', satisfied: false, evidenceIds: [] },
      { elementNumber: 3, name: 'Adverse Action', description: 'Suffered adverse employment action (fired, demoted)', satisfied: false, evidenceIds: [] },
      { elementNumber: 4, name: 'Circumstances', description: 'Circumstances give rise to inference of discrimination', satisfied: false, evidenceIds: [] }
    ]
  },
  {
    name: 'Common Law Fraud',
    statute: 'Common Law',
    elements: [
      { elementNumber: 1, name: 'Representation', description: 'Defendant made a representation', satisfied: false, evidenceIds: [] },
      { elementNumber: 2, name: 'Falsity', description: 'Representation was false', satisfied: false, evidenceIds: [] },
      { elementNumber: 3, name: 'Materiality', description: 'Representation was material', satisfied: false, evidenceIds: [] },
      { elementNumber: 4, name: 'Knowledge', description: 'Defendant knew it was false', satisfied: false, evidenceIds: [] },
      { elementNumber: 5, name: 'Reliance', description: 'Plaintiff justifiably relied on it', satisfied: false, evidenceIds: [] },
      { elementNumber: 6, name: 'Damages', description: 'Plaintiff suffered harm', satisfied: false, evidenceIds: [] }
    ]
  }
];

export const DEADLINE_TEMPLATES: Partial<Deadline>[] = [
    { name: 'Initial Disclosures', rule: 'FRCP 26(a)', consequence: 'EVIDENCE EXCLUDED', urgency: 'medium' },
    { name: 'Response to Motion to Dismiss', rule: 'Local Rule 7', consequence: 'MOTION GRANTED / CASE DISMISSED', urgency: 'critical' },
    { name: 'Discovery Cutoff', rule: 'Scheduling Order', consequence: 'NO MORE EVIDENCE GATHERING', urgency: 'high' }
];
