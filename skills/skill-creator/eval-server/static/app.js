// skill-creator eval dashboard — vanilla JS SSE client
// All dynamic strings are inserted via textContent or createElement to avoid XSS.

const $ = (id) => document.getElementById(id);

const state = {
  skills: [],
  selectedSkill: null,
  evalCandidates: [],
  selectedEvalSet: null,
  evalSetSize: 0,
  runId: null,
  evtSource: null,
  trainQueries: [],
  testQueries: [],
  history: [],
  result: null,
};

// ---- DOM helpers ----

function el(tag, props = {}, children = []) {
  const node = document.createElement(tag);
  for (const [k, v] of Object.entries(props)) {
    if (k === "className") node.className = v;
    else if (k === "dataset") for (const [dk, dv] of Object.entries(v)) node.dataset[dk] = dv;
    else if (k === "textContent") node.textContent = v;
    else if (k === "title") node.title = v;
    else if (k === "value") node.value = v;
    else if (k === "type") node.type = v;
    else node.setAttribute(k, v);
  }
  for (const c of children) {
    if (c == null) continue;
    if (typeof c === "string") node.appendChild(document.createTextNode(c));
    else node.appendChild(c);
  }
  return node;
}

function clear(node) {
  while (node.firstChild) node.removeChild(node.firstChild);
}

// ---- bootstrap ----

async function loadSkills() {
  const res = await fetch("/api/skills");
  state.skills = await res.json();
  const sel = $("skill-select");
  clear(sel);
  sel.appendChild(el("option", { value: "" }, ["— select skill —"]));
  for (const s of state.skills) {
    const opt = el("option", { value: s.name, title: s.description_preview }, [
      `${s.name}  (${s.description_len} chars)`,
    ]);
    sel.appendChild(opt);
  }
}

async function loadSkillDetail(name) {
  if (!name) {
    state.selectedSkill = null;
    state.evalCandidates = [];
    $("skill-desc-preview").textContent = "";
    const sel = $("eval-set-select");
    clear(sel);
    sel.appendChild(el("option", { value: "" }, ["— pick a skill first —"]));
    sel.disabled = true;
    $("eval-set-stats").textContent = "";
    refreshStartButton();
    return;
  }
  const res = await fetch(`/api/skills/${encodeURIComponent(name)}`);
  if (!res.ok) {
    $("skill-desc-preview").textContent = "(failed to load)";
    return;
  }
  const data = await res.json();
  state.selectedSkill = data;
  state.evalCandidates = data.eval_candidates || [];
  $("skill-desc-preview").textContent =
    data.description.slice(0, 200) + (data.description.length > 200 ? "…" : "");

  const sel = $("eval-set-select");
  clear(sel);
  if (state.evalCandidates.length === 0) {
    sel.appendChild(el("option", { value: "" }, ["no eval sets found — paste JSON below"]));
    sel.disabled = true;
  } else {
    sel.disabled = false;
    sel.appendChild(el("option", { value: "" }, ["— select eval set —"]));
    for (const c of state.evalCandidates) {
      sel.appendChild(
        el("option", { value: c.path }, [
          `${c.name}  (${c.size} queries: ${c.should_trigger}+ / ${c.should_not_trigger}-)`,
        ]),
      );
    }
  }
  $("eval-set-stats").textContent = `${state.evalCandidates.length} candidate eval sets discovered`;
  refreshStartButton();
}

function refreshStartButton() {
  const skillOk = !!state.selectedSkill;
  const evalOk = !!$("eval-set-select").value || !!$("eval-set-paste").value.trim();
  $("start-btn").disabled = !(skillOk && evalOk);
}

// ---- run start ----

async function startRun() {
  const skill = state.selectedSkill;
  if (!skill) return;

  const evalSetPath = $("eval-set-select").value;
  const pasted = $("eval-set-paste").value.trim();
  if (pasted && !evalSetPath) {
    alert(
      "Paste-JSON support requires saving to disk first. Save your JSON to a file under <skill>/evals/ or <skill>-workspace/ and reload, or pick from the dropdown.",
    );
    return;
  }

  const body = {
    skill_path: skill.skill_path,
    eval_set_path: evalSetPath,
    model: $("model-select").value,
    num_workers: parseInt($("num-workers").value, 10),
    timeout: parseInt($("timeout").value, 10),
    max_iterations: parseInt($("max-iterations").value, 10),
    runs_per_query: parseInt($("runs-per-query").value, 10),
    trigger_threshold: parseFloat($("trigger-threshold").value),
    holdout: parseFloat($("holdout").value),
    description: $("description-override").value.trim() || null,
  };

  const res = await fetch("/api/runs", {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify(body),
  });
  if (!res.ok) {
    const err = await res.json().catch(() => ({}));
    alert("Failed to start: " + (err.error || res.statusText));
    return;
  }
  const { run_id } = await res.json();
  state.runId = run_id;
  state.history = [];
  state.result = null;
  state.trainQueries = [];
  state.testQueries = [];
  resetTable();
  $("run-id").textContent = run_id;
  $("run-iter-max").textContent = String(body.max_iterations);
  $("run-iter").textContent = "0";
  setStatus("running");
  $("start-btn").disabled = true;
  $("stop-btn").disabled = false;
  $("apply-best-btn").disabled = true;
  setConnectionPill("running");

  attachStream(run_id);
}

function resetTable() {
  clear($("results-tbody"));
  const head = $("results-thead-row");
  clear(head);
  head.appendChild(el("th", {}, ["Iter"]));
  head.appendChild(el("th", {}, ["Train"]));
  head.appendChild(el("th", {}, ["Test"]));
  head.appendChild(el("th", { className: "desc-col" }, ["Description"]));
}

function attachStream(runId) {
  if (state.evtSource) state.evtSource.close();
  const es = new EventSource(`/api/runs/${encodeURIComponent(runId)}/stream`);
  state.evtSource = es;

  es.onmessage = (e) => {
    let evt;
    try {
      evt = JSON.parse(e.data);
    } catch {
      return;
    }
    handleEvent(evt);
  };
  es.onerror = () => {
    setConnectionPill("error");
  };
}

function handleEvent(evt) {
  switch (evt.event) {
    case "snapshot":
      if (evt.history && evt.history.length) {
        renderHeaderFromEntry(evt.history[0]);
        for (const entry of evt.history) appendIterationRow(entry);
        state.history = evt.history.slice();
      }
      if (evt.params) {
        $("run-iter-max").textContent = String(evt.params.max_iterations);
      }
      if (evt.result) {
        state.result = evt.result;
        showFinalResult(evt.result);
      }
      setStatus(evt.status);
      break;

    case "iteration_start":
      $("run-iter").textContent = String(evt.iteration);
      setStatus("running");
      break;

    case "iteration_done":
      if (state.history.length === 0) renderHeaderFromEntry(evt.entry);
      state.history.push(evt.entry);
      appendIterationRow(evt.entry);
      $("run-iter").textContent = String(evt.iteration);
      break;

    case "improving":
      setStatus("improving");
      break;

    case "loop_done":
      state.result = evt.result;
      showFinalResult(evt.result);
      setStatus("complete");
      $("stop-btn").disabled = true;
      $("start-btn").disabled = false;
      $("apply-best-btn").disabled = false;
      setConnectionPill("complete");
      if (state.evtSource) state.evtSource.close();
      break;

    case "error":
      setStatus("error");
      $("run-status").title = evt.error || "";
      $("stop-btn").disabled = true;
      $("start-btn").disabled = false;
      setConnectionPill("error");
      if (state.evtSource) state.evtSource.close();
      break;

    default:
      break;
  }
}

// ---- table rendering ----

function renderHeaderFromEntry(entry) {
  const trainResults = entry.train_results || entry.results || [];
  const testResults = entry.test_results || [];
  state.trainQueries = trainResults.map((r) => ({ query: r.query, should_trigger: r.should_trigger }));
  state.testQueries = testResults.map((r) => ({ query: r.query, should_trigger: r.should_trigger }));
  $("train-size").textContent = String(state.trainQueries.length);
  $("test-size").textContent = String(state.testQueries.length);

  const head = $("results-thead-row");
  clear(head);
  head.appendChild(el("th", {}, ["Iter"]));
  head.appendChild(el("th", {}, ["Train"]));
  head.appendChild(el("th", {}, ["Test"]));
  head.appendChild(el("th", { className: "desc-col" }, ["Description"]));
  for (const q of state.trainQueries) {
    const cls = q.should_trigger ? "positive-col" : "negative-col";
    head.appendChild(el("th", { className: cls, title: q.query }, [truncate(q.query, 40)]));
  }
  for (const q of state.testQueries) {
    const cls = "test-col " + (q.should_trigger ? "positive-col" : "negative-col");
    head.appendChild(el("th", { className: cls, title: q.query }, [truncate(q.query, 40)]));
  }
}

function appendIterationRow(entry) {
  const tbody = $("results-tbody");
  const tr = el("tr", { dataset: { iteration: String(entry.iteration) } });

  const trainCorrect = aggregateCorrect(entry.train_results || entry.results || []);
  const testCorrect = aggregateCorrect(entry.test_results || []);

  tr.appendChild(el("td", {}, [String(entry.iteration)]));
  tr.appendChild(
    el("td", {}, [
      el("span", { className: `score-pill ${scoreClass(trainCorrect)}` }, [
        `${trainCorrect.correct}/${trainCorrect.total}`,
      ]),
    ]),
  );
  tr.appendChild(
    el("td", {}, [
      el("span", { className: `score-pill ${scoreClass(testCorrect)}` }, [
        `${testCorrect.correct}/${testCorrect.total}`,
      ]),
    ]),
  );
  tr.appendChild(el("td", { className: "desc-cell" }, [entry.description || ""]));

  const trainByQuery = new Map((entry.train_results || entry.results || []).map((r) => [r.query, r]));
  const testByQuery = new Map((entry.test_results || []).map((r) => [r.query, r]));

  for (const q of state.trainQueries) {
    tr.appendChild(makeResultCell(trainByQuery.get(q.query) || {}, false));
  }
  for (const q of state.testQueries) {
    tr.appendChild(makeResultCell(testByQuery.get(q.query) || {}, true));
  }

  tbody.appendChild(tr);
  highlightBestRow();
}

function makeResultCell(r, isTest) {
  const cls = "result-cell" + (isTest ? " test-result-cell" : "");
  if (Object.keys(r).length === 0) {
    return el("td", { className: cls }, [el("span", { className: "rate" }, ["—"])]);
  }
  const ok = !!r.pass;
  const td = el("td", { className: cls + (ok ? " pass" : " fail") }, [
    ok ? "✓" : "✗",
    el("span", { className: "rate" }, [`${r.triggers}/${r.runs}`]),
  ]);
  return td;
}

function aggregateCorrect(results) {
  let correct = 0;
  let total = 0;
  for (const r of results) {
    const runs = r.runs || 0;
    const triggers = r.triggers || 0;
    total += runs;
    if (r.should_trigger) correct += triggers;
    else correct += runs - triggers;
  }
  return { correct, total };
}

function scoreClass({ correct, total }) {
  if (total === 0) return "score-bad";
  const ratio = correct / total;
  if (ratio >= 0.8) return "score-good";
  if (ratio >= 0.5) return "score-ok";
  return "score-bad";
}

function highlightBestRow() {
  if (state.history.length === 0) return;
  const useTest = state.testQueries.length > 0;
  const bestEntry = state.history.reduce((a, b) => {
    const av = useTest ? (a.test_passed ?? 0) : (a.train_passed ?? a.passed ?? 0);
    const bv = useTest ? (b.test_passed ?? 0) : (b.train_passed ?? b.passed ?? 0);
    return bv > av ? b : a;
  });
  document.querySelectorAll("tr.best-row").forEach((r) => r.classList.remove("best-row"));
  const row = document.querySelector(`tr[data-iteration="${bestEntry.iteration}"]`);
  if (row) row.classList.add("best-row");
  $("best-description").textContent = bestEntry.description || "";
  const ts = useTest ? bestEntry.test_passed : bestEntry.train_passed;
  const tot = useTest ? bestEntry.test_total : bestEntry.train_total;
  $("best-score").textContent = `${ts}/${tot} (iter ${bestEntry.iteration})`;
}

function showFinalResult(result) {
  $("best-description").textContent = result.best_description || "";
  $("best-score").textContent = result.best_score || "—";
}

// ---- status + ui plumbing ----

function setStatus(s) {
  const pill = $("run-status");
  pill.className = "pill pill-" + s;
  pill.textContent = s;
}
function setConnectionPill(s) {
  const pill = $("connection-pill");
  pill.className = "pill pill-" + s;
  pill.textContent = s;
}

// ---- stop + apply ----

async function stopRun() {
  if (!state.runId) return;
  await fetch(`/api/runs/${encodeURIComponent(state.runId)}/stop`, { method: "POST" });
}

async function applyBest() {
  if (!state.runId) return;
  if (!confirm("Overwrite SKILL.md with the best description?")) return;
  const res = await fetch(`/api/runs/${encodeURIComponent(state.runId)}/apply`, {
    method: "POST",
  });
  const data = await res.json();
  if (data.ok) {
    alert("Applied. Backup at: " + data.backup);
  } else {
    alert("Failed: " + (data.error || "unknown"));
  }
}

// ---- run history ----

async function showRunsModal() {
  const res = await fetch("/api/runs");
  const runs = await res.json();
  const list = $("runs-list");
  clear(list);
  if (runs.length === 0) {
    list.appendChild(el("li", {}, ["No runs yet"]));
  } else {
    for (const r of runs) {
      const t = new Date(r.started_at * 1000).toLocaleString();
      const li = el("li", {}, [
        el("strong", {}, [r.run_id]),
        ` · ${r.status} · ${t} · iters=${r.iterations_run}`,
      ]);
      const btn = el("button", { className: "ghost-btn" }, ["view"]);
      btn.addEventListener("click", () => {
        document.getElementById("runs-modal").close();
        attachStream(r.run_id);
        state.runId = r.run_id;
        $("run-id").textContent = r.run_id;
      });
      li.appendChild(btn);
      list.appendChild(li);
    }
  }
  $("runs-modal").showModal();
}

// ---- helpers ----

function truncate(s, n) {
  if (typeof s !== "string") return "";
  return s.length > n ? s.slice(0, n - 1) + "…" : s;
}

// ---- wiring ----

document.addEventListener("DOMContentLoaded", () => {
  loadSkills();
  $("skill-select").addEventListener("change", (e) => loadSkillDetail(e.target.value));
  $("eval-set-select").addEventListener("change", refreshStartButton);
  $("eval-set-paste").addEventListener("input", refreshStartButton);
  $("start-btn").addEventListener("click", startRun);
  $("stop-btn").addEventListener("click", stopRun);
  $("apply-best-btn").addEventListener("click", applyBest);
  $("show-runs-btn").addEventListener("click", showRunsModal);
});
