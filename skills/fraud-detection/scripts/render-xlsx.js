import { readFileSync } from "node:fs";
import path from "node:path";

// Renders out/referrals.json → out/referrals.xlsx (3 sheets) using ExcelJS. SIU case-management
// tools ingest sheets, so this sits alongside the HTML packets. exceljs is an OPTIONAL dependency —
// if it isn't installed the script prints a one-line skip and exits 0; the dashboard + packets
// stand on their own.   node scripts/render-xlsx.js
import { outDir as resolveOutDir } from "./paths.js";

let ExcelJS;
try {
  ({ default: ExcelJS } = await import("exceljs"));
} catch {
  console.log(
    "render-xlsx: exceljs not installed — skipping (optional). `npm i exceljs` to enable.",
  );
  process.exit(0);
}

const outDir = resolveOutDir();
const data = JSON.parse(readFileSync(path.join(outDir, "referrals.json"), "utf8"));
const BANNER = `${data.meta.disclaimer} — ${data.meta.language}`;

// CSV/spreadsheet formula-injection guard: a cell whose text starts with = + - @ is executed as a
// formula by Excel/Sheets. Prefix any such string value with an apostrophe so it stays literal.
const sx = (v) => (typeof v === "string" && /^[=+\-@]/.test(v) ? "'" + v : v);

const wb = new ExcelJS.Workbook();
wb.creator = "fraud-detection";

function bannerRow(ws, span) {
  const row = ws.addRow([BANNER]);
  ws.mergeCells(row.number, 1, row.number, span);
  row.getCell(1).font = { bold: true, color: { argb: "FFFFFFFF" } };
  row.getCell(1).fill = { type: "pattern", pattern: "solid", fgColor: { argb: "FF7A2E1E" } };
  row.getCell(1).alignment = { wrapText: true };
}

// --- Sheet 1: Summary (one row per referral) ---
const s1 = wb.addWorksheet("Summary");
bannerRow(s1, 7);
s1.addRow([
  "NPI",
  "Schemes",
  "Scheme count",
  "# Claims",
  "Confidence",
  "Recoverable $ (rule-based)",
  "Statistical estimate $",
]);
s1.getRow(2).font = { bold: true };
for (const r of data.referrals) {
  s1.addRow([
    sx(r.npi),
    sx(r.schemes.join(", ")),
    r.schemeCount,
    r.claimIds.length,
    sx(r.confidence),
    r.recoverableUsd ?? r.exposureUsd,
    r.statisticalEstimateUsd ?? 0,
  ]);
}
s1.columns = [
  { width: 18 },
  { width: 34 },
  { width: 13 },
  { width: 10 },
  { width: 12 },
  { width: 22 },
  { width: 20 },
];
for (const col of [6, 7]) {
  s1.getColumn(col).numFmt = '"$"#,##0';
  s1.getColumn(col).alignment = { horizontal: "right" };
}
s1.views = [{ state: "frozen", ySplit: 2 }]; // freeze banner + header

// --- Sheet 2: Claim detail (one row per finding, self-citing) ---
const s2 = wb.addWorksheet("Claim detail");
s2.addRow([
  "NPI",
  "Scheme",
  "Finding",
  "Rule cited",
  "Computed",
  "Threshold",
  "Claim IDs",
  "Exposure $",
]);
s2.getRow(1).font = { bold: true };
for (const r of data.referrals) {
  for (const f of r.findings) {
    s2.addRow([
      sx(f.npi),
      sx(f.scheme),
      sx(f.summary || f.citation.rule),
      sx(f.citation.rule),
      sx(String(f.citation.computed)),
      sx(String(f.citation.threshold)),
      sx(f.claimIds.join(", ")),
      f.exposureUsd,
    ]);
  }
}
s2.columns = [
  { width: 16 },
  { width: 22 },
  { width: 60 },
  { width: 46 },
  { width: 14 },
  { width: 12 },
  { width: 22 },
  { width: 12 },
];
s2.getColumn(8).numFmt = '"$"#,##0';
s2.views = [{ state: "frozen", ySplit: 1 }];

// --- Sheet 3: Methodology & provenance ---
const s3 = wb.addWorksheet("Methodology");
const rows = [
  ["Disclaimer", data.meta.disclaimer],
  ["Language", data.meta.language],
  ["Rule quarter", data.meta.quarter],
  ["Detectors run", data.meta.detectors.join(", ")],
  ["Referrals", data.meta.referralCount],
  ["Recoverable $ (rule-based)", data.meta.recoverableUsd ?? data.meta.totalExposureUsd],
  ["Statistical estimate $", data.meta.statisticalEstimateUsd ?? 0],
  ["Total exposure $ (combined)", data.meta.totalExposureUsd],
  ["Gate findings kept", data.meta.gate ? data.meta.gate.findings : "n/a"],
  ["Gate dropped", data.meta.gate ? data.meta.gate.droppedAtGate : "n/a"],
  [
    "Exposure note",
    "Recoverable = hard rule-based (tier 1). Statistical estimate = supporting indicator (tier 2), not a recoverable allegation. De-duplicated so a claim line counts once.",
  ],
];
rows.forEach((r) => s3.addRow(r));
s3.getColumn(1).font = { bold: true };
s3.columns = [{ width: 22 }, { width: 80 }];

const file = path.join(outDir, "referrals.xlsx");
await wb.xlsx.writeFile(file);
console.log(
  `referrals.xlsx written: 3 sheets (Summary/Claim detail/Methodology), ${data.referrals.length} referrals`,
);
