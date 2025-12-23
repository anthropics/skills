/**
 * Generate UID from claim, element, defendant
 * Format: [Claim 1-9][Element 1-9][Defendant 0-9]
 * Defendant 0 = all defendants
 */
export function generateUID(
  claimNumber: number, 
  elementNumber: number, 
  defendantNumber: number
): string {
  return `${claimNumber}${elementNumber}${defendantNumber}`;
}

/**
 * Parse UID back to components
 */
export function parseUID(uid: string): {
  claim: number;
  element: number;
  defendant: number;
} {
  return {
    claim: parseInt(uid[0]),
    element: parseInt(uid[1]),
    defendant: parseInt(uid[2])
  };
}

/**
 * Get all UIDs for a claim
 */
export function getClaimUIDs(claimNumber: number): string[] {
  const uids: string[] = [];
  for (let e = 1; e <= 9; e++) {
    for (let d = 0; d <= 9; d++) {
      uids.push(generateUID(claimNumber, e, d));
    }
  }
  return uids;
}

export function formatUID(uid: string): string {
    const { claim, element, defendant } = parseUID(uid);
    return `C${claim}:E${element}:D${defendant}`;
}
