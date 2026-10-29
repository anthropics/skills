// Writes the per-specialty cohort slice (the exact rows D7's median/MAD were computed from) to
// <outDir>/cohort-<specialty>.csv so a skeptical reviewer can recompute the robust-z themselves.
// Called from screen.js after the sweep, before serialization — mutates evidence.cohortFile in place.
import path from "node:path";

import { ddl, refDb } from "./duck.js";

const MIN_BENES = 11; // mirror d07-outlier.js — CMS suppresses rows under 11 benes
const slug = (s) =>
  String(s)
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, "-")
    .replace(/^-+|-+$/g, "");
const q = (s) => String(s).replace(/'/g, "''");

export async function writeCohortSlices(result, ctx, outDir) {
  const db = refDb(ctx.quarter);
  const done = new Set();
  for (const r of result.referrals)
    for (const f of r.findings) {
      const e = f.evidence;
      if (f.detectorId !== "D7" || !e?.specialty || !e?.cohortN) continue;
      const file = `cohort-${slug(e.specialty)}.csv`;
      e.cohortFile = file;
      if (done.has(file)) continue;
      done.add(file);
      // Same filter as cohortStats() — keep the columns a reviewer needs to reproduce median/MAD.
      const out = path.join(outDir, file);
      await ddl(
        `COPY (SELECT Rndrng_NPI, Rndrng_Prvdr_Type, Rndrng_Prvdr_State_Abrvtn, Tot_Benes, Tot_Srvcs, ` +
          `round(Tot_Srvcs::double / Tot_Benes::double, 4) AS Srvcs_Per_Bene ` +
          `FROM partb_by_provider ` +
          `WHERE Rndrng_Prvdr_Type = '${q(e.specialty)}' AND Tot_Benes::int >= ${MIN_BENES}) ` +
          `TO '${q(out)}' (HEADER)`,
        { db },
      );
    }
}
