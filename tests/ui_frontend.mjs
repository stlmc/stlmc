// Development-only JavaScript tests: node --test tests/ui_frontend.mjs.
// Installed STLmc users do not need Node or a frontend build tool.
import test from 'node:test';
import assert from 'node:assert/strict';
import {validateBase, configureLocalConnection, setupConnection} from '../src/stlmc/ui/frontend/js/connection.js';
import {summarize} from '../src/stlmc/ui/frontend/js/progress.js';
import {setupDocuments} from '../src/stlmc/ui/frontend/js/documents.js';
import {setupResults} from '../src/stlmc/ui/frontend/js/results.js';

test('local UI discovers a custom API port without a token', async () => {
  const previous = globalThis.fetch;
  const input = {value: 'http://127.0.0.1:8765'};
  globalThis.fetch = async (url, options) => {
    assert.equal(url, '/local-connection.json');
    assert.equal(options.credentials, 'omit');
    return new Response(JSON.stringify({bridge_url: 'http://127.0.0.1:18080'}));
  };
  try {
    await configureLocalConnection({$: () => input}, {protocol: 'http:', hostname: 'localhost'});
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
    if (!elements.has(id)) elements.set(id, {value: '', textContent: '', children: ['old private DOM'], classList: {toggle() {}}, replaceChildren(...items) { this.children = items; }});
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
