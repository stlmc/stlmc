'use strict';
(() => {
  const $ = id => document.getElementById(id);
  let connection = null;
  let epoch = 0;
  let selected = null;
  let active = null;
  let refreshing = false;
  let plotSignature = '';
  let plotUrls = [];
  const error = message => { $('error').textContent = message || ''; };
  const message = exception => exception instanceof Error ? exception.message : String(exception);

  function validateBase(value) {
    const url = new URL(value);
    if (!['http:', 'https:'].includes(url.protocol) || !['127.0.0.1', 'localhost'].includes(url.hostname) ||
        url.username || url.password || url.search || url.hash || (url.pathname !== '/' && url.pathname !== '')) {
      throw new Error('Use a loopback bridge URL, for example http://127.0.0.1:8765 (no path or credentials).');
    }
    return url.origin;
  }

  async function request(path, options = {}, session = connection) {
    if (!session) throw new Error('Connect to your local bridge first.');
    const headers = new Headers(options.headers || {});
    headers.set('Authorization', 'Bearer ' + session.token);
    if (options.body) headers.set('Content-Type', 'application/json');
    let response;
    try {
      response = await fetch(session.base + path, {...options, headers, credentials: 'omit',
        cache: 'no-store', redirect: 'error', signal: options.signal || AbortSignal.timeout(20000)});
    } catch (exception) {
      throw new Error('Cannot reach the local bridge. Check that it is running, the allowed origin matches this page, and your browser allows local-network access. You can instead open the locally hosted UI.');
    }
    if (!response.ok) {
      let detail = 'HTTP ' + response.status;
      try { const body = await response.json(); detail += ': ' + (typeof body.detail === 'string' ? body.detail : JSON.stringify(body.detail || body)); } catch (_) { /* No structured error. */ }
      throw new Error(detail);
    }
    return response;
  }
  const json = async (path, options, session) => (await request(path, options, session)).json();
  const filePath = (run, name) => '/api/runs/' + encodeURIComponent(run) + '/files/' + encodeURIComponent(name);

  function clearPlots() {
    $('plots').replaceChildren();
    plotUrls.forEach(url => URL.revokeObjectURL(url));
    plotUrls = [];
    plotSignature = '';
  }
  function updateButtons() {
    $('run').disabled = !connection || !!active;
    $('stop').disabled = !connection || !active || active.state === 'stopping';
    $('load-document').disabled = !connection;
  }
  function disconnect() {
    epoch += 1;
    connection = null;
    selected = active = null;
    $('token').value = '';
    $('connection-state').textContent = 'Disconnected. A running analysis is not cancelled by disconnecting.';
    $('history').replaceChildren();
    $('artifacts').replaceChildren();
    $('documents').replaceChildren(new Option('Choose a document', ''));
    $('results').replaceChildren();
    $('log').textContent = $('progress').textContent = $('run-state').textContent = '';
    clearPlots();
    updateButtons();
  }

  function download(blob, name) {
    const url = URL.createObjectURL(blob);
    const anchor = document.createElement('a');
    anchor.href = url; anchor.download = name;
    document.body.append(anchor); anchor.click(); anchor.remove();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
  }

  async function showRun(id, session, generation) {
    const job = await json('/api/runs/' + encodeURIComponent(id), undefined, session);
    if (generation !== epoch || selected !== id) return;
    $('run-state').textContent = 'Run ' + id + ' — ' + job.state;
    $('log').textContent = job.log || '';
    const progress = job.progress || {};
    $('progress').textContent = JSON.stringify(progress.scenario || (progress.events || []).slice(-1)[0] || {}, null, 2);
    $('results').replaceChildren();
    for (const result of job.results || []) {
      const row = document.createElement('p');
      row.textContent = [result.status, 'bound ' + result.bound, result.scope || '', result.formula || ''].join(' · ');
      $('results').append(row);
    }
    for (const warning of job.visualization_errors || []) {
      const row = document.createElement('p'); row.textContent = warning; $('results').append(row);
    }
    $('artifacts').replaceChildren();
    for (const name of job.files || []) {
      const button = document.createElement('button'); button.type = 'button'; button.textContent = 'Download ' + name;
      button.onclick = async () => {
        try {
          if (generation !== epoch) return;
          const blob = await (await request(filePath(id, name), {}, session)).blob();
          if (generation === epoch) download(blob, name);
        } catch (exception) { if (generation === epoch) error(message(exception)); }
      };
      $('artifacts').append(button);
    }
    const html = (job.files || []).filter(name => name.endsWith('.html'));
    const signature = id + ':' + html.join('|');
    if (signature !== plotSignature) {
      clearPlots(); plotSignature = signature;
      for (const name of html) {
        const blob = await (await request(filePath(id, name), {}, session)).blob();
        if (generation !== epoch || selected !== id) return;
        const url = URL.createObjectURL(new Blob([blob], {type: 'text/html'})); plotUrls.push(url);
        const frame = document.createElement('iframe'); frame.title = name; frame.sandbox = 'allow-scripts'; frame.src = url;
        $('plots').append(frame);
      }
    }
  }

  async function refresh() {
    if (!connection || refreshing) return;
    refreshing = true;
    const session = connection, generation = epoch;
    try {
      const jobs = await json('/api/runs', undefined, session);
      if (generation !== epoch) return;
      active = jobs.find(job => ['running', 'stopping'].includes(job.state)) || null;
      if (!selected && jobs.length) selected = jobs[0].id;
      $('history').replaceChildren();
      for (const job of jobs) {
        const button = document.createElement('button'); button.type = 'button';
        button.textContent = new Date(job.started * 1000).toLocaleString() + ' · ' + job.state;
        button.setAttribute('aria-current', String(job.id === selected));
        button.onclick = () => { if (generation !== epoch) return; selected = job.id; clearPlots(); refresh(); };
        $('history').append(button);
      }
      updateButtons();
      if (selected) await showRun(selected, session, generation);
    } catch (exception) { if (generation === epoch) error(message(exception)); }
    finally { refreshing = false; }
  }

  $('connect-form').onsubmit = async event => {
    event.preventDefault(); error('');
    const token = $('token').value.trim();
    const base = $('bridge-url').value.trim();
    disconnect();
    const generation = epoch;
    $('connection-state').textContent = 'Connecting…';
    try {
      const session = {base: validateBase(base), token};
      if (!token) throw new Error('Enter the session token printed by the local bridge.');
      const bridge = await json('/api/bridge', undefined, session);
      if (generation !== epoch) return;
      if (bridge.protocol !== 1) throw new Error('Unsupported bridge protocol. Update the local bridge.');
      const health = await json('/api/health', undefined, session);
      if (generation !== epoch) return;
      if (!health.stlmc) throw new Error(health.error || 'STLmc is unavailable in the bridge environment.');
      const [models, configs] = await Promise.all([
        json('/api/examples', undefined, session), json('/api/documents?kind=cfg', undefined, session)]);
      if (generation !== epoch) return;
      connection = session;
      $('connection-state').textContent = 'Connected to ' + session.base + ' · bridge ' + (bridge.version || 'protocol 1');
      $('documents').replaceChildren(new Option('Choose a document', ''));
      for (const doc of models) $('documents').append(new Option(doc.filename, doc.filename));
      for (const doc of configs) $('documents').append(new Option(doc.name, doc.name));
      updateButtons(); await refresh();
    } catch (exception) {
      if (generation !== epoch) return;
      disconnect();
      $('connection-state').textContent = 'Disconnected. Connection or runtime check failed.';
      error(message(exception)); updateButtons();
    }
  };
  $('disconnect').onclick = disconnect;
  $('load-document').onclick = async () => {
    const generation = epoch;
    try {
      if (!$('documents').value) return;
      const doc = await json('/api/documents/' + encodeURIComponent($('documents').value));
      if (generation !== epoch) return;
      $(doc.name.endsWith('.cfg') ? 'config' : 'model').value = doc.text;
    } catch (exception) { if (generation === epoch) error(message(exception)); }
  };
  $('run-form').onsubmit = async event => {
    event.preventDefault(); error('');
    const generation = epoch;
    try {
      const payload = {model: $('model').value, config: $('config').value, goal: $('goal').value.trim(),
        solver: $('solver').value, bound: Number($('bound').value), time_bound: Number($('time-bound').value),
        threshold: Number($('threshold').value), timeout: Number($('timeout').value),
        path_strategy: $('explicit').checked ? 'explicit' : 'symbolic', two_step: $('two-step').checked, reach: $('reach').checked};
      const job = await json('/api/runs', {method: 'POST', body: JSON.stringify(payload)});
      if (generation !== epoch) return;
      selected = job.id; active = job; updateButtons(); clearPlots(); await refresh();
    } catch (exception) { if (generation === epoch) error(message(exception)); }
  };
  $('stop').onclick = async () => {
    const generation = epoch;
    try {
      if (active) await json('/api/runs/' + encodeURIComponent(active.id) + '/stop', {method: 'POST'});
      if (generation === epoch) await refresh();
    } catch (exception) { if (generation === epoch) error(message(exception)); }
  };
  for (const kind of ['model', 'config']) {
    $('open-' + kind).onchange = async event => {
      const file = event.target.files[0];
      if (!file) return;
      if (file.size > (kind === 'model' ? 500000 : 100000)) { error('File is too large for the bridge.'); return; }
      $(kind).value = await file.text(); event.target.value = '';
    };
    $('download-' + kind).onclick = () => download(new Blob([$(kind).value], {type: 'text/plain;charset=utf-8'}), kind === 'model' ? 'model.model' : 'model.cfg');
  }
  window.addEventListener('pagehide', disconnect);
  setInterval(refresh, 1500);
})();
