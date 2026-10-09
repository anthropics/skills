import assert from 'node:assert/strict';
import fs from 'node:fs';
import vm from 'node:vm';
import test from 'node:test';

const html = fs.readFileSync(process.env.EVAL_VIEWER_HTML || new URL('../viewer.html', import.meta.url), 'utf8');
const init = html.slice(html.indexOf('    async function init()'), html.indexOf('    // ---- Navigation ----'));
const navigation = html.slice(html.indexOf('    function navigate('), html.indexOf('    // ---- Show a run ----'));
const feedback = html.slice(html.indexOf('    // ---- Feedback (saved'), html.indexOf('    // ---- Toast ----'));
const declarations = html.slice(html.indexOf('    // ---- State ----'), html.indexOf('    // ---- Init ----'))
  .split('\n').filter(line => /(?:let|const) (saveTimeout|feedbackRevision|feedbackSaveQueue|feedbackStatus|feedbackLoadState|dirtyRunIds)\b/.test(line)).join('\n');
const flush = () => new Promise(resolve => setImmediate(resolve));

function harness(immediateStatus, persistedStatus = 'in_progress', initialResponse) {
  const requests = [];
  const downloads = [];
  const listeners = {};
  const timers = new Map();
  let nextTimer = 0;
  let visible = false;
  const rendered = [];
  let context;
  const elements = {
    feedback: { value: '', addEventListener(event, callback) { listeners[event] = callback; } },
    'feedback-status': { textContent: '' },
    'retry-btn': { hidden: true, disabled: false },
    'done-title': { textContent: '' },
    'done-message': { textContent: '' },
    'skill-name': { textContent: '' },
    'prev-btn': { disabled: false },
    'next-btn': { disabled: false },
    'done-btn': { disabled: false },
    'done-overlay': { classList: { add() { visible = true; }, remove() { visible = false; } } },
  };
  context = vm.createContext({
    EMBEDDED_DATA: { skill_name: 'Fabricated', runs: [{ id: 'first-run' }, { id: 'second-run' }] },
    currentIndex: 0, feedbackMap: {}, Date, Blob, location: { protocol: 'http:' },
    URL: { createObjectURL(blob) { downloads.push(blob); return 'blob:synthetic'; }, revokeObjectURL() {} },
    document: { getElementById(id) { return elements[id]; }, createElement() { return { click() {} }; } },
    showRun(index) {
      rendered.push(index);
      context.currentIndex = index;
      elements.feedback.value = context.feedbackMap[context.EMBEDDED_DATA.runs[index].id] || '';
      elements['feedback-status'].textContent = '';
    },
    updateNavButtons() {
      elements['prev-btn'].disabled = context.currentIndex === 0;
      elements['next-btn'].disabled = context.currentIndex === context.EMBEDDED_DATA.runs.length - 1;
    },
    setTimeout(callback) { timers.set(++nextTimer, callback); return nextTimer; },
    clearTimeout(id) { timers.delete(id); },
    fetch(_url, options) {
      if (!options) return (typeof initialResponse === 'function' ? initialResponse() : initialResponse) || Promise.resolve({ ok: true, status: 200,
        json: async () => ({ status: persistedStatus, reviews: [] }) });
      const payload = JSON.parse(options.body);
      let resolve;
      let reject;
      const pending = new Promise((yes, no) => { resolve = yes; reject = no; });
      requests.push({ payload, settle(status = 200) {
        if (status === 'offline') reject(new Error('Fabricated offline failure'));
        else resolve({ ok: status >= 200 && status < 300, status });
      } });
      if (immediateStatus !== undefined) requests.at(-1).settle(immediateStatus);
      return pending;
    },
  });
  vm.runInContext(declarations + '\n' + init + navigation + feedback, context);
  vm.runInContext("if (typeof feedbackLoadState !== 'undefined') feedbackLoadState = 'known';", context);
  return { context, elements, requests, timers, downloads, rendered, visible: () => visible,
    hasInputListener: () => typeof listeners.input === 'function',
    input(text) { if (elements.feedback.disabled) return;
      elements.feedback.value = text; listeners.input?.(); } };
}

function deferred() {
  let resolve;
  const promise = new Promise(yes => { resolve = yes; });
  return { promise, resolve };
}

function restoredResponse(status = 200) {
  return { ok: status >= 200 && status < 300, status, json: async () => ({
    status: 'complete', reviews: [{ run_id: 'first-run', feedback: 'Older server note' }],
  }) };
}

test('the first trial displays while feedback controls wait for the initial read', async () => {
  const restore = deferred();
  const h = harness(200, 'in_progress', restore.promise);
  const loading = h.context.init();
  assert.equal(h.elements['skill-name'].textContent, 'Fabricated');
  assert.deepEqual(h.rendered, [0]);
  for (const name of ['feedback', 'prev-btn', 'next-btn', 'done-btn']) {
    assert.equal(h.elements[name].disabled, true);
  }
  await h.context.showDoneDialog();
  assert.equal(h.requests.length, 0);
  assert.equal(h.visible(), false);
  restore.resolve(restoredResponse());
  await loading;
  assert.equal(h.hasInputListener(), true);
  assert.equal(h.elements.feedback.disabled, false);
  assert.equal(h.elements['next-btn'].disabled, false);
  assert.equal(h.elements['done-btn'].disabled, false);
});

test('a delayed initial read cannot accept or save an early edit', async () => {
  const restore = deferred();
  const h = harness(200, 'in_progress', restore.promise);
  const loading = h.context.init();
  h.input('Newer local note');
  await h.context.saveCurrentFeedback();
  assert.equal(h.elements.feedback.value, '');
  assert.equal(h.requests.length, 0);
  restore.resolve(restoredResponse());
  await loading;
  assert.equal(h.elements.feedback.value, 'Older server note');
  h.input('Newer local note');
  await h.context.saveCurrentFeedback();
  assert.equal(h.requests[0].payload.reviews[0].feedback, 'Newer local note');
});

test('navigation waits for restoration and then preserves the loaded note', async () => {
  const restore = deferred();
  const h = harness(200, 'in_progress', restore.promise);
  const loading = h.context.init();
  h.context.navigate(1);
  assert.equal(h.context.currentIndex, 0);
  assert.equal(h.requests.length, 0);
  restore.resolve(restoredResponse());
  await loading;
  h.context.navigate(1);
  await flush();
  assert.equal(h.context.currentIndex, 1);
  assert.equal(h.requests[0].payload.reviews[0].feedback, 'Older server note');
});

test('response-body loading stays guarded and editing resumes after restoration', async () => {
  const body = deferred();
  const h = harness(200, 'in_progress', Promise.resolve({ ok: true, status: 200,
    json: () => body.promise }));
  const loading = h.context.init();
  await flush();
  assert.equal(h.elements.feedback.disabled, true);
  h.input('New note during body loading');
  assert.equal(h.elements.feedback.value, '');
  assert.equal(h.timers.size, 0);
  body.resolve(await restoredResponse().json());
  await loading;
  assert.equal(h.elements.feedback.value, 'Older server note');
  h.input('New note after body loading');
  for (const callback of h.timers.values()) callback();
  await flush();
  assert.equal(h.requests.at(-1).payload.reviews[0].feedback, 'New note after body loading');
  assert.equal(h.requests.at(-1).payload.status, 'in_progress');
});

test('a pristine viewer still restores its note and complete status', async () => {
  const h = harness(200, 'in_progress', Promise.resolve(restoredResponse()));
  await h.context.init();
  assert.equal(h.elements.feedback.value, 'Older server note');
  assert.equal(vm.runInContext('feedbackStatus', h.context), 'complete');
});

test('an unsuccessful initial response cannot restore a feedback payload', async () => {
  const h = harness(200, 'in_progress', Promise.resolve(restoredResponse(500)));
  await h.context.init();
  assert.equal(h.elements.feedback.value, '');
  assert.equal(vm.runInContext('feedbackStatus', h.context), 'in_progress');
  assert.equal(h.hasInputListener(), true);
});

for (const failure of ['not-found', 'offline', 'malformed']) {
  test(`initial ${failure} feedback recovery preserves local edits without server writes`, async () => {
    const response = failure === 'offline' ? Promise.reject(new Error('Fabricated offline read'))
      : Promise.resolve(failure === 'not-found' ? restoredResponse(404)
        : { ok: true, status: 200, json: async () => { throw new SyntaxError('Fabricated malformed JSON'); } });
    const h = harness(200, 'in_progress', response);
    await h.context.init();
    assert.equal(h.elements.feedback.disabled, false);
    assert.equal(h.elements['next-btn'].disabled, false);
    assert.equal(h.elements['done-btn'].disabled, false);
    assert.equal(h.elements.feedback.value, '');
    h.input('Fabricated note after a failed read');
    await h.context.saveCurrentFeedback();
    assert.equal(h.requests.length, 0);
    assert.match(h.elements['feedback-status'].textContent, /local|load|unread/i);
    await h.context.showDoneDialog();
    assert.equal(h.requests.length, 0);
    const local = JSON.parse(await h.downloads[0].text());
    assert.equal(local.status, 'in_progress');
    assert.equal(local.reviews[0].feedback, 'Fabricated note after a failed read');
  });
}

test('overlapping saves send and acknowledge snapshots in order', async () => {
  const h = harness();
  h.elements.feedback.value = 'Older fabricated note';
  const first = h.context.saveCurrentFeedback();
  h.elements.feedback.value = 'Newer fabricated note';
  const second = h.context.saveCurrentFeedback();
  await flush();
  assert.equal(h.requests.length, 1);
  h.requests[0].settle();
  await first;
  await flush();
  assert.equal(h.requests.length, 2);
  assert.equal(h.requests[1].payload.reviews[0].feedback, 'Newer fabricated note');
  assert.equal(h.elements['feedback-status'].textContent, '');
  h.requests[1].settle();
  await second;
  assert.equal(h.elements['feedback-status'].textContent, 'Saved');
});

test('editing during a save does not label the new note Saved', async () => {
  const h = harness();
  await h.context.init();
  h.input('First fabricated note');
  const first = h.context.saveCurrentFeedback();
  await flush();
  h.input('Unsaved newer note');
  h.requests[0].settle();
  await first;
  assert.equal(h.elements['feedback-status'].textContent, '');
});

test('Done cancels the pending debounce and remains the last write', async () => {
  const h = harness();
  await h.context.init();
  h.input('Fabricated completed note');
  assert.equal(h.timers.size, 1);
  const done = h.context.showDoneDialog();
  await flush();
  assert.equal(h.timers.size, 0);
  assert.equal(h.requests.length, 1);
  assert.equal(h.requests[0].payload.status, 'complete');
  h.requests[0].settle();
  await done;
  assert.equal(h.visible(), true);
});

test('Done waits behind an older save and completes with the latest note', async () => {
  const h = harness();
  h.elements.feedback.value = 'Older fabricated note';
  const save = h.context.saveCurrentFeedback();
  h.elements.feedback.value = 'Latest fabricated note';
  const done = h.context.showDoneDialog();
  await flush();
  assert.equal(h.requests.length, 1);
  h.requests[0].settle();
  await save;
  await flush();
  assert.equal(h.visible(), false);
  assert.equal(h.requests[1].payload.status, 'complete');
  assert.equal(h.requests[1].payload.reviews[0].feedback, 'Latest fabricated note');
  h.requests[1].settle();
  await done;
  assert.equal(h.visible(), true);
});

test('closing Done preserves complete until a reviewer edits again', async () => {
  const h = harness(200);
  await h.context.init();
  h.input('Fabricated completed note');
  await h.context.showDoneDialog();
  h.context.closeDoneDialog();
  await flush();
  assert.equal(h.visible(), false);
  assert.equal(h.requests.length, 1);
  assert.equal(h.requests[0].payload.status, 'complete');
  h.input('Fabricated resumed edit');
  for (const callback of h.timers.values()) callback();
  await flush();
  assert.equal(h.requests.length, 2);
  assert.equal(h.requests[1].payload.status, 'in_progress');
  assert.equal(h.requests[1].payload.reviews[0].feedback, 'Fabricated resumed edit');
});

test('navigation after Done preserves complete until an input edit', async () => {
  const h = harness(200);
  await h.context.init();
  h.input('Fabricated completed note');
  await h.context.showDoneDialog();
  h.context.closeDoneDialog();
  h.context.navigate(1);
  await flush();
  assert.equal(h.requests.at(-1).payload.status, 'complete');
  assert.equal(h.requests.at(-1).payload.reviews.length, 2);
  h.input('Fabricated edited incoming note');
  await h.context.saveCurrentFeedback();
  assert.equal(h.requests.at(-1).payload.status, 'in_progress');
});

test('initialisation restores complete and navigation retains it', async () => {
  const h = harness(200, 'complete');
  await h.context.init();
  h.context.navigate(1);
  await flush();
  assert.equal(h.requests.at(-1).payload.status, 'complete');
  h.input('Fabricated resumed review');
  await h.context.saveCurrentFeedback();
  assert.equal(h.requests.at(-1).payload.status, 'in_progress');
});

test('a fresh iteration does not restore stale completion', async () => {
  const h = harness(200, 'complete');
  h.context.EMBEDDED_DATA.previous_feedback = { 'first-run': 'Fabricated prior feedback' };
  await h.context.init();
  h.context.navigate(1);
  await flush();
  assert.equal(h.requests.at(-1).payload.status, 'in_progress');
});

test('navigation while Done is pending queues another complete snapshot', async () => {
  const h = harness();
  await h.context.init();
  h.input('Fabricated pending completion');
  const done = h.context.showDoneDialog();
  h.context.navigate(1);
  await flush();
  assert.equal(h.requests.length, 1);
  h.requests[0].settle();
  await done;
  await flush();
  assert.equal(h.requests[1].payload.status, 'complete');
  assert.equal(h.requests[1].payload.reviews.length, 2);
  h.requests[1].settle();
  await flush();
  assert.equal(h.visible(), false);
});

test('navigation saves the outgoing note and cancels its pending timer', async () => {
  const h = harness();
  await h.context.init();
  h.input('Outgoing fabricated note');
  h.context.navigate(1);
  await flush();
  assert.equal(h.context.currentIndex, 1);
  assert.equal(h.timers.size, 0);
  assert.equal(h.requests[0].payload.reviews[0].run_id, 'first-run');
  h.requests[0].settle();
  await flush();
  assert.equal(h.elements['feedback-status'].textContent, '');
  h.elements.feedback.value = 'Incoming fabricated note';
  const next = h.context.saveCurrentFeedback();
  await flush();
  assert.equal(h.requests[1].payload.reviews.length, 2);
  h.requests[1].settle();
  await next;
});

test('a failed save does not stop the next queued save', async () => {
  const h = harness();
  h.elements.feedback.value = 'Fabricated note';
  const first = h.context.saveCurrentFeedback();
  const second = h.context.saveCurrentFeedback();
  await flush();
  h.requests[0].settle(500);
  await first;
  await flush();
  assert.equal(h.requests.length, 2);
  h.requests[1].settle();
  await second;
  assert.equal(h.elements['feedback-status'].textContent, 'Saved');
});

test('editing while Done saves keeps the completion dialog hidden', async () => {
  const h = harness();
  await h.context.init();
  h.input('Fabricated note at Done');
  const done = h.context.showDoneDialog();
  await flush();
  h.input('Newer note awaiting save');
  h.requests[0].settle();
  await done;
  assert.equal(h.visible(), false);
});

for (const status of [200, 404, 500, 'offline']) {
  test(`existing feedback recovery for ${status}`, async () => {
    const h = harness(status);
    h.elements.feedback.value = 'Fabricated review note';
    await h.context.saveCurrentFeedback();
    assert.equal(h.context.feedbackMap['first-run'], 'Fabricated review note');
    assert.equal(h.elements['feedback-status'].textContent === 'Saved', status === 200);
    await h.context.showDoneDialog();
    assert.equal(h.downloads.length, status === 200 ? 0 : 1);
    if (h.downloads.length) {
      const downloaded = JSON.parse(await h.downloads[0].text());
      assert.equal(downloaded.reviews[0].feedback, 'Fabricated review note');
      assert.equal(downloaded.reviews[1].feedback, '');
    }
  });
}

test('the complete inline script parses', () => {
  const source = html.slice(html.indexOf('<script>') + '<script>'.length, html.lastIndexOf('</script>'));
  new vm.Script(source);
});


for (const body of [null, [], {status:'complete'}, {reviews:null}, {reviews:{}},
  {reviews:[{run_id:'first-run', feedback:12}]}, {reviews:[{feedback:'note'}]},
  {reviews:[{run_id:'first-run',feedback:'one'},{run_id:'first-run',feedback:'two'}]},
  {status:'invented',reviews:[]}, {unexpected:'value'}]) {
  test(`invalid saved document ${JSON.stringify(body)} prevents any POST`, async () => {
    const h = harness(200, 'in_progress', Promise.resolve({ok:true,status:200,json:async()=>body}));
    await h.context.init();
    h.input('Local note');
    await h.context.saveCurrentFeedback();
    await h.context.showDoneDialog();
    assert.equal(h.requests.length,0);
    assert.equal(h.elements['retry-btn'].hidden,false);
    const local=JSON.parse(await h.downloads[0].text());
    assert.equal(local.status,'in_progress');
    assert.equal(local.reviews[0].feedback,'Local note');
  });
}

test('successful empty200 is a new review and permits normal saves',async()=>{
  const h=harness(200,'in_progress',Promise.resolve({ok:true,status:200,json:async()=>({})}));
  await h.context.init();h.input('First new note');await h.context.saveCurrentFeedback();
  assert.equal(h.requests.length,1);assert.equal(h.requests[0].payload.reviews[0].feedback,'First new note');
});

test('retry retains local edits, deliberate blanks and unread other notes',async()=>{
  let attempts=0;
  const h=harness(200,'in_progress',()=>Promise.resolve(++attempts===1?restoredResponse(500):
    {ok:true,status:200,json:async()=>({status:'complete',reviews:[
      {run_id:'first-run',feedback:'Old first'}, {run_id:'second-run',feedback:'Old second'},
      {run_id:'unlisted-run',feedback:'Old unlisted'}]})}));
  await h.context.init();h.input('Local first');h.context.navigate(1);h.input('');
  await h.context.retryFeedbackLoad();
  assert.equal(h.elements.feedback.value,'');
  assert.equal(h.context.feedbackMap['first-run'],'Local first');
  assert.equal(h.context.feedbackMap['unlisted-run'],'Old unlisted');
  assert.equal(vm.runInContext('feedbackStatus',h.context),'in_progress');
  await h.context.showDoneDialog();
  const saved=h.requests.at(-1).payload;
  assert.equal(saved.reviews.find(r=>r.run_id==='unlisted-run').feedback,'Old unlisted');
  assert.equal(saved.reviews.find(r=>r.run_id==='second-run').feedback,'');
});

test('retry validates the whole response before committing any restored note',async()=>{
  let attempts=0;
  const h=harness(200,'in_progress',()=>Promise.resolve(++attempts===1?restoredResponse(500):
    {ok:true,status:200,json:async()=>({reviews:[{run_id:'first-run',feedback:'Partial old note'},
      {run_id:'second-run',feedback:42}]})}));
  await h.context.init();h.input('Local note');await h.context.retryFeedbackLoad();
  assert.equal(h.elements.feedback.value,'Local note');await h.context.showDoneDialog();
  assert.equal(h.requests.length,0);assert.equal(h.context.feedbackMap['second-run'],undefined);
});

test('pending retry locks input and navigation and suppresses duplicate reads',async()=>{
  let attempts=0;const retry=deferred();
  const h=harness(200,'in_progress',()=> ++attempts===1?Promise.resolve(restoredResponse(500)):retry.promise);
  await h.context.init();h.input('Local note');
  const loading=h.context.retryFeedbackLoad();
  const duplicate=h.context.retryFeedbackLoad();
  assert.equal(h.elements.feedback.disabled,true);h.input('Cannot replace local note');h.context.navigate(1);
  await h.context.showDoneDialog();assert.equal(h.requests.length,0);assert.equal(attempts,2);
  retry.resolve(restoredResponse());await loading;await duplicate;
  assert.equal(h.elements.feedback.value,'Local note');assert.equal(h.context.currentIndex,0);
});

test('retry without local edits restores complete status',async()=>{
  let attempts=0;
  const h=harness(200,'in_progress',()=>Promise.resolve(restoredResponse(++attempts===1?500:200)));
  await h.context.init();await h.context.retryFeedbackLoad();
  assert.equal(vm.runInContext('feedbackStatus',h.context),'complete');
  assert.equal(h.elements.feedback.value,'Older server note');assert.equal(h.elements['retry-btn'].hidden,true);
});

test('local Done does not mark completion or send a partial recovery to the server',async()=>{
  const h=harness(200,'in_progress',Promise.resolve(restoredResponse(500)));
  await h.context.init();h.input('Local note');await h.context.showDoneDialog();
  assert.equal(vm.runInContext('feedbackStatus',h.context),'in_progress');
  assert.equal(h.requests.length,0);assert.match(h.elements['done-message'].textContent,/earlier|unread|local/i);
});

test('static file viewing makes no requests and downloads all runs',async()=>{
  let attempts=0;
  const h=harness(200,'in_progress',()=>{attempts++;return Promise.resolve(restoredResponse());});
  h.context.location.protocol='file:';await h.context.init();h.input('Static note');
  await h.context.saveCurrentFeedback();await h.context.showDoneDialog();
  assert.equal(attempts,0);assert.equal(h.requests.length,0);
  const local=JSON.parse(await h.downloads[0].text());
  assert.equal(local.status,'complete');assert.equal(local.reviews.length,2);
});

test('reserved object keys in stored run IDs remain ordinary preserved notes',async()=>{
  const h=harness(200,'in_progress',Promise.resolve({ok:true,status:200,json:async()=>({reviews:[
    {run_id:'__proto__',feedback:'Reserved name note'},{run_id:'constructor',feedback:'Other name note'}]})}));
  await h.context.init();await h.context.showDoneDialog();
  assert.equal(h.requests[0].payload.reviews.find(r=>r.run_id==='__proto__').feedback,'Reserved name note');
  assert.equal(h.requests[0].payload.reviews.find(r=>r.run_id==='constructor').feedback,'Other name note');
});


for(const status of [500,'offline']) {
  test(`navigation retains a visible save failure for ${status}`,async()=>{
    const h=harness();await h.context.init();h.input('Outgoing local note');h.context.navigate(1);
    await flush();h.requests[0].settle(status);await flush();
    assert.equal(h.context.currentIndex,1);
    assert.equal(h.context.feedbackMap['first-run'],'Outgoing local note');
    assert.match(h.elements['feedback-status'].textContent,/Save failed/);
    const done=h.context.showDoneDialog();await flush();h.requests[1].settle(status);await done;
    const download=JSON.parse(await h.downloads[0].text());
    assert.equal(download.reviews[0].feedback,'Outgoing local note');
  });
  test(`retry automatically saves restored local edits and reports ${status}`,async()=>{
    let attempts=0;
    const h=harness(status,'in_progress',()=>Promise.resolve(++attempts===1?restoredResponse(500):
      {ok:true,status:200,json:async()=>({status:'complete',reviews:[
        {run_id:'first-run',feedback:'Old first'},{run_id:'second-run',feedback:'Old second'}]})}));
    await h.context.init();h.input('Local recovered edit');await h.context.retryFeedbackLoad();await flush();
    assert.equal(h.requests.length,1);
    assert.equal(h.requests[0].payload.status,'in_progress');
    assert.equal(h.requests[0].payload.reviews.find(r=>r.run_id==='first-run').feedback,'Local recovered edit');
    assert.equal(h.requests[0].payload.reviews.find(r=>r.run_id==='second-run').feedback,'Old second');
    assert.match(h.elements['feedback-status'].textContent,/Save failed/);
  });
}

test('retry alone automatically saves all restored notes and local overrides',async()=>{
  let attempts=0;
  const h=harness(200,'in_progress',()=>Promise.resolve(++attempts===1?restoredResponse(500):
    {ok:true,status:200,json:async()=>({status:'complete',reviews:[
      {run_id:'first-run',feedback:'Old first'},{run_id:'second-run',feedback:'Old second'}]})}));
  await h.context.init();h.input('Local recovered edit');await h.context.retryFeedbackLoad();await flush();
  assert.equal(h.requests.length,1);assert.equal(h.requests[0].payload.reviews.length,2);
  assert.equal(h.requests[0].payload.status,'in_progress');
  assert.equal(h.requests[0].payload.reviews.find(r=>r.run_id==='first-run').feedback,'Local recovered edit');
  assert.equal(h.requests[0].payload.reviews.find(r=>r.run_id==='second-run').feedback,'Old second');
  assert.equal(h.elements['feedback-status'].textContent,'Saved');
});

test('retry refreshes the current untouched textarea before automatic saving',async()=>{
  let attempts=0;
  const h=harness(200,'in_progress',()=>Promise.resolve(++attempts===1?restoredResponse(500):
    {ok:true,status:200,json:async()=>({reviews:[
      {run_id:'first-run',feedback:'Old first'},{run_id:'second-run',feedback:'Old second'}]})}));
  await h.context.init();h.input('Local first');h.context.navigate(1);await h.context.retryFeedbackLoad();
  assert.equal(h.requests.length,1);
  assert.equal(h.requests[0].payload.reviews.find(r=>r.run_id==='second-run').feedback,'Old second');
});
