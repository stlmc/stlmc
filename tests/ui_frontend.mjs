// Development-only JavaScript tests: node --test tests/ui_frontend.mjs.
// Installed STLmc users do not need Node or a frontend build tool.
import test from 'node:test';
import assert from 'node:assert/strict';
import {readableDetail, validateBase, configureLocalConnection, setupConnection} from '../src/stlmc/ui/frontend/js/connection.js';
import {summarize} from '../src/stlmc/ui/frontend/js/progress.js';
import {setupDocuments} from '../src/stlmc/ui/frontend/js/documents.js';
import {setupSettings} from '../src/stlmc/ui/frontend/js/settings.js';
import {failureSummary, setupResults} from '../src/stlmc/ui/frontend/js/results.js';
import {setupAnalysis} from '../src/stlmc/ui/frontend/js/analysis.js';

test('validation messages never dump input bodies or context JSON', () => {
  assert.equal(readableDetail([{loc: ['body', 'config'], msg: 'Value error, Invalid configuration syntax',
    input: 'private config contents', ctx: {error: 'internal'}}]), 'config: Invalid configuration syntax');
});

test('file watch reloads clean buffers, preserves edits and reports deletion', async () => {
  const oldWindow = globalThis.window, oldOption = globalThis.Option;
  globalThis.window = {confirm: () => true};
  globalThis.Option = function(text, value) { this.text = text; this.value = value; };
  try {
    const c = fakeContext(); let remote = {name: 'watch.model', text: 'first', revision: 'one'};
    let entries = [{name: remote.name, version: '1'}];
    c.json = async path => path === '/api/documents/watch' ? {model: entries, cfg: []} : remote;
    setupDocuments(c); c.$('documents').value = 'watch.model';
    await c.$('load-document').onclick();
    await c.watchDocuments();
    remote = {...remote, text: 'second', revision: 'two'}; entries = [{name: remote.name, version: '2'}];
    await c.watchDocuments(); assert.equal(c.$('model').value, 'second');
    c.$('model').value = 'local draft'; c.$('model').oninput();
    remote = {...remote, text: 'third', revision: 'three'}; entries = [{name: remote.name, version: '3'}];
    await c.watchDocuments();
    assert.equal(c.$('model').value, 'local draft'); assert.match(c.$('model-status').textContent, /Changed on disk/);
    entries = []; await c.watchDocuments();
    assert.match(c.$('model-status').textContent, /Removed on disk/);
    assert.equal(c.$('model').value, 'local draft');
    assert.deepEqual(c.$('documents').children.map(item => item.value), ['']);
  } finally { globalThis.window = oldWindow; globalThis.Option = oldOption; }
});

test('connection badge state follows polling failure and recovery', async () => {
  const c = fakeContext(); c.state.selected = null;
  c.json = async () => { throw new Error('offline'); };
  setupAnalysis(c); await c.refresh();
  assert.equal(c.state.connectionHealth, 'unreachable');
  c.json = async () => []; await c.refresh();
  assert.equal(c.state.connectionHealth, 'connected');
});

test('starting a new run hides the previous failure before settings/network waits', async () => {
  const c = fakeContext(); let finish;
  c.$('run-failure').hidden = false;
  c.syncSettings = () => new Promise(resolve => { finish = resolve; });
  setupAnalysis(c);
  const pending = c.$('run-form').onsubmit({preventDefault() {}});
  assert.equal(c.$('run-failure').hidden, true);
  finish(false); await pending;
});

test('history deletion confirms and submits finished runs only', async () => {
  const previous = globalThis.window;
  globalThis.window = {confirm: () => true};
  try {
    const c = fakeContext(); c.state.selected = 'finished';
    c.state.history = [{id: 'finished', state: 'failed'}, {id: 'active', state: 'running'}];
    let submitted;
    c.json = async (path, options) => {
      if (path === '/api/runs/clear') {
        submitted = JSON.parse(options.body); return {deleted: ['finished'], kept: []};
      }
      return [];
    };
    setupAnalysis(c); await c.$('clear-history').onclick();
    assert.deepEqual(submitted, {run_ids: ['finished']});
    assert.equal(c.state.selected, null);
    assert.deepEqual(c.$('results').children, []);
  } finally { globalThis.window = previous; }
});

test('settings display parser values and submit only user edits', async () => {
  const original = globalThis.Option;
  globalThis.Option = function(text, value) { this.text = text; this.value = value; };
  try {
    const c = fakeContext(), lookup = c.$;
    c.$ = id => { const item = lookup(id); item.addEventListener = (_, handler) => { item.edit = handler; }; return item; };
    c.$('model').value = 'model text'; c.$('config').value = 'config text';
    c.json = async (path, options) => {
      assert.equal(path, '/api/inspect'); assert.equal(JSON.parse(options.body).config, 'config text');
      return {common: {solver: 'auto', threshold: '.01', goal: 'f2', 'two-step': 'true',
        reach: 'false', 'path-strategy': 'symbolic'}, goals: ['f1', 'f2'], solver_choices: ['auto', 'z3']};
    };
    setupSettings(c); assert.equal(await c.syncSettings(), true);
    assert.deepEqual(c.$('goal').children.map(item => item.value), ['', 'f1', 'f2']);
    assert.equal(c.$('goal').value, 'f2'); assert.equal(c.$('solver').value, 'auto');
    assert.equal(c.$('bound').value, ''); assert.equal(c.$('time-bound').value, '');
    assert.equal(c.$('two-step').checked, true); assert.deepEqual(c.settingsPayload(), {});
    c.$('two-step').checked = false; c.$('two-step').edit();
    c.$('bound').value = '3'; c.$('bound').edit();
    assert.deepEqual(c.settingsPayload(), {two_step: false, bound: 3});
    await c.syncSettings(); assert.equal(c.$('bound').value, 3);
    c.$('bound').value = ''; c.$('bound').edit();
    assert.deepEqual(c.settingsPayload(), {two_step: false});
    // Editing while new config values are loading is explicit, even when the
    // chosen value happened to equal the previous configuration's baseline.
    c.state.settingsReady = false;
    c.$('solver').value = 'auto'; c.$('solver').edit();
    assert.equal(c.settingsPayload().solver, 'auto');
  } finally { globalThis.Option = original; }
});

test('failed and timed-out runs expose a bounded diagnostic without hiding partial results', () => {
  const summary = failureSummary({state: 'failed', exit_code: 2,
    log: '\u001b[31mError: unsupported ODE for z3\u001b[0m\n', results: [{status: 'satisfied'}]});
  assert.equal(summary.title, 'Analysis failed');
  assert.match(summary.detail, /unsupported ODE for z3/);
  assert.doesNotMatch(summary.detail, /\u001b/);
  assert.match(summary.exit, /2/);
  assert.equal(failureSummary({state: 'completed'}), null);
  assert.equal(failureSummary({state: 'timed_out', log: 'x'.repeat(5000)}).detail.length, 2000);
});

test('timeout, user stop and server shutdown have distinct reasons even with exit 130', () => {
  for (const [state, reason, expected] of [
    ['timed_out', 'timeout', /120 seconds/],
    ['cancelled', 'user_stop', /at your request/],
    ['interrupted', 'server_shutdown', /server was shutting down/],
  ]) {
    const result = failureSummary({state, termination_reason: reason, request: {timeout: 120},
      exit_code: 130, log: 'execution interrupted'});
    assert.match(result.reason, expected);
    assert.equal(result.detail, 'execution interrupted');
    assert.match(result.exit, /130/);
  }
  assert.match(failureSummary({state: 'timed_out', request: {timeout: 120},
    log: 'interrupted by user'}).reason, /120 seconds/);
  assert.match(failureSummary({state: 'interrupted'}).reason, /no termination cause was recorded/);
});

test('local UI discovers a custom API port without a token', async () => {
  const previous = globalThis.fetch;
  const input = {value: 'http://127.0.0.1:8765'};
  globalThis.fetch = async (url, options) => {
    assert.equal(url, '/local-connection.json');
    assert.equal(options.credentials, 'omit');
    return new Response(JSON.stringify({bridge_url: 'http://127.0.0.1:18080'}));
  };
  try {
    await configureLocalConnection({$: () => input, state: {}}, {protocol: 'http:', hostname: 'localhost'});
    assert.equal(input.value, 'http://127.0.0.1:18080');
    globalThis.fetch = () => { throw new Error('Hosted page must not fetch local config'); };
    await configureLocalConnection({$: () => input}, {protocol: 'https:', hostname: 'stlmc.github.io'});
  } finally { globalThis.fetch = previous; }
});

test('bridge URLs are loopback origins without credentials or paths', () => {
  assert.equal(validateBase('http://127.0.0.1:8765/'), 'http://127.0.0.1:8765');
  assert.equal(validateBase('http://localhost:8765'), 'http://localhost:8765');
  for (const url of ['https://example.com', 'http://localhost.evil', 'http://user:pass@localhost', 'http://127.0.0.1/path', 'http://localhost/?token=secret', 'file:///tmp/data']) {
    assert.throws(() => validateBase(url));
  }
});

test('completed bounds appear immediately, across goal sessions', () => {
  const events = [
    {event: 'run_started', goal: 'f1', session: 'a', time: 1, data: {max_bound: 4}},
    {event: 'bound_finished', goal: 'f1', session: 'a', time: 2, data: {bound: 0, result: 'unsat', elapsed: .125}},
    {event: 'run_started', goal: 'f2', session: 'b', time: 3, data: {max_bound: 2}},
    {event: 'bound_finished', goal: 'f2', session: 'b', time: 4, data: {bound: 0, result: 'sat', elapsed: .5}},
  ];
  const result = summarize({events}, 'running', 4, 5);
  assert.deepEqual(result.rows.map(row => [row.goal, row.bound, row.query]), [['f1', 0, 'UNSAT'], ['f2', 0, 'SAT']]);
  assert.equal(result.stage, 'f2 — finalizing result');
  assert.equal(result.since, 1);
});

test('before the first bound, progress does not invent a row', () => {
  const result = summarize({}, 'running', 4);
  assert.equal(result.rows.length, 0);
  assert.match(result.stage, /first completed bound/);
  assert.equal(summarize({}, 'completed', 4).since, null);
});

test('scenario data from a different goal is not displayed', () => {
  const events = [{event: 'run_started', session: 'new', goal: 'f3', time: 1, data: {max_bound: 4}}];
  const result = summarize({events, scenario: {session: 'old', data: {bound: 99}}}, 'running', 4, 2);
  assert.equal(result.scenario, null);
  assert.match(result.stage, /bound 0 of 4/);
});

function fakeContext() {
  const elements = new Map();
  const $ = id => {
    if (!elements.has(id)) elements.set(id, {value: '', textContent: '', children: ['old private DOM'], classList: {toggle() {}}, replaceChildren(...items) { this.children = items; }, append(...items) { this.children.push(...items); }});
    return elements.get(id);
  };
  const state = {epoch: 0, connection: {base: 'http://localhost:8765', token: 'old'}, selected: 'private', active: null};
  const c = {$, state, error(value) { this.lastError = value; }, message: error => error.message,
    clearDocuments() {}, clearPlots() { this.plotsCleared = true; }, updateButtons() {},
    fetchDocuments: async () => [[], []], populateDocuments() {}, refresh: async () => {}};
  $('bridge-url').value = 'http://127.0.0.1:8765';
  return c;
}

test('failed reconnect clears old authenticated DOM but not edited text', async () => {
  const previousFetch = globalThis.fetch, previousWindow = globalThis.window;
  globalThis.window = {addEventListener() {}};
  globalThis.fetch = async () => new Response(JSON.stringify({detail: 'Unauthorized'}), {status: 401});
  try {
    const c = fakeContext(); c.$('model').value = 'unsaved model'; c.$('token').value = 'invalid';
    setupConnection(c); await c.$('connect-form').onsubmit({preventDefault() {}});
    assert.equal(c.state.connection, null);
    for (const id of ['history', 'artifacts', 'results', 'progress-rows']) assert.deepEqual(c.$(id).children, []);
    assert.equal(c.$('model').value, 'unsaved model'); assert.equal(c.$('token').value, '');
    assert.match(c.lastError, /401/); assert.equal(c.plotsCleared, true);
  } finally { globalThis.fetch = previousFetch; globalThis.window = previousWindow; }
});

test('typing while a document loads preserves the newer buffer', async () => {
  const previousWindow = globalThis.window;
  globalThis.window = {confirm: () => true};
  try {
    const c = fakeContext(); let resolveLoad;
    c.json = () => new Promise(resolve => { resolveLoad = resolve; });
    setupDocuments(c); c.$('documents').value = 'remote.model';
    c.$('model').value = 'old draft'; const pending = c.$('load-document').onclick();
    c.$('model').value = 'new draft';
    resolveLoad({name: 'remote.model', text: 'remote contents', revision: 'a'}); await pending;
    assert.equal(c.$('model').value, 'new draft'); assert.match(c.lastError, /edits were kept/);
  } finally { globalThis.window = previousWindow; }
});

test('a delayed upload preserves typing and resets the file input for retry', async () => {
  const previousWindow = globalThis.window;
  globalThis.window = {confirm: () => true};
  try {
    const c = fakeContext(); let resolveFile; setupDocuments(c);
    const input = {value: 'file.model', files: [{name: 'file.model', size: 10, text: () => new Promise(resolve => { resolveFile = resolve; })}]};
    const pending = c.$('open-model').onchange({target: input}); c.$('model').value = 'typed draft';
    resolveFile('uploaded text'); await pending;
    assert.equal(c.$('model').value, 'typed draft'); assert.equal(input.value, ''); assert.match(c.lastError, /edits were kept/);
  } finally { globalThis.window = previousWindow; }
});

test('saving a former document cannot overwrite the selected document revision', async () => {
  const previousWindow = globalThis.window, previousOption = globalThis.Option;
  globalThis.window = {confirm: () => true}; globalThis.Option = class {constructor(text, value) {this.text = text; this.value = value;}};
  try {
    const c = fakeContext(); let resolveSave;
    c.json = (path, options) => options?.method === 'PUT' ? new Promise(resolve => { resolveSave = resolve; }) : Promise.resolve({name: 'new.model', text: 'new document', revision: 'new-revision'});
    setupDocuments(c); c.$('model-name').value = 'old.model'; c.$('model').value = 'old document';
    const pending = c.$('save-model').onclick(); c.$('documents').value = 'new.model'; await c.$('load-document').onclick();
    resolveSave({name: 'old.model', text: 'old document', revision: 'old-revision'}); await pending;
    assert.equal(c.$('model').value, 'new document'); assert.equal(c.$('model-name').value, 'new.model'); assert.equal(c.$('model-status').textContent, 'Saved');
  } finally { globalThis.window = previousWindow; globalThis.Option = previousOption; }
});

test('a transient graph fetch failure is retried on the next refresh', async () => {
  const previousDocument = globalThis.document;
  globalThis.document = {createElement: () => ({append() {}, children: []})};
  try {
    const c = fakeContext(); c.state.selected = 'run';
    c.json = async () => ({state: 'completed', request: {bound: 1}, results: [], files: ['plot.html'], progress: {}});
    let calls = 0;
    c.request = async () => { if (++calls === 1) throw new Error('temporary network error'); return new Response('<html>graph</html>'); };
    // The fake DOM needs append(), as only the real browser owns presentation.
    const baseLookup = c.$; c.$ = id => { const element = baseLookup(id); element.append = (...items) => element.children.push(...items); return element; };
    setupResults(c);
    await assert.rejects(c.showRun('run', c.state.connection, 0), /temporary/);
    await c.showRun('run', c.state.connection, 0);
    assert.equal(calls, 2); assert.equal(c.$('plots').children.length, 1); c.clearPlots();
  } finally { globalThis.document = previousDocument; }
});

test('an old connection attempt cannot overwrite a newer successful session', async () => {
  const previousFetch = globalThis.fetch, previousWindow = globalThis.window;
  globalThis.window = {addEventListener() {}};
  let releaseOld;
  globalThis.fetch = async (url, options) => {
    if (options.headers.get('Authorization') === 'Bearer old-attempt') return await new Promise(resolve => { releaseOld = resolve; });
    return new Response(JSON.stringify(url.endsWith('/api/bridge') ? {protocol: 1, version: 'test'} : {stlmc: true}));
  };
  try {
    const c = fakeContext(); setupConnection(c);
    c.$('token').value = 'old-attempt'; const old = c.$('connect-form').onsubmit({preventDefault() {}});
    c.$('token').value = 'new-attempt'; await c.$('connect-form').onsubmit({preventDefault() {}});
    releaseOld(new Response(JSON.stringify({protocol: 999}))); await old;
    assert.equal(c.state.connection.token, 'new-attempt'); assert.match(c.$('connection-state').textContent, /^Connected/);
  } finally { globalThis.fetch = previousFetch; globalThis.window = previousWindow; }
});
