export function validateBase(value) {
  const url = new URL(value);
  if (!['http:', 'https:'].includes(url.protocol) || !['127.0.0.1', 'localhost'].includes(url.hostname) ||
      url.username || url.password || url.search || url.hash || (url.pathname !== '/' && url.pathname !== '')) {
    throw new Error('Use a loopback bridge URL, for example http://127.0.0.1:8765 (no path or credentials).');
  }
  return url.origin;
}

export async function configureLocalConnection(c, location = window.location) {
  if (location.protocol !== 'http:' || !['127.0.0.1', 'localhost'].includes(location.hostname)) return;
  const input = c.$('bridge-url'), initial = input.value;
  try {
    const response = await fetch('/local-connection.json', {cache: 'no-store', credentials: 'omit',
      redirect: 'error', signal: AbortSignal.timeout(3000)});
    if (!response.ok) return;
    const config = await response.json();
    if (input.value === initial) input.value = validateBase(config.bridge_url);
  } catch (_) { /* Hosted or older frontends retain the editable default. */ }
}

export function setupConnection(c) {
  const {$, state} = c;
  c.request = async (path, options = {}, session = state.connection) => {
    if (!session) throw new Error('Connect to your local bridge first.');
    const headers = new Headers(options.headers || {});
    headers.set('Authorization', 'Bearer ' + session.token);
    if (options.body) headers.set('Content-Type', 'application/json');
    let response;
    try {
      response = await fetch(session.base + path, {...options, headers, credentials: 'omit', cache: 'no-store',
        redirect: 'error', signal: options.signal || AbortSignal.timeout(20000)});
    } catch (_) {
      throw new Error('Cannot reach the local bridge. Check that it is running, the allowed origin matches this page, and your browser allows local-network access. You can instead open the locally hosted UI.');
    }
    if (!response.ok) {
      let detail = 'HTTP ' + response.status;
      try { const body = await response.json(); detail += ': ' + (typeof body.detail === 'string' ? body.detail : JSON.stringify(body.detail || body)); } catch (_) { /* No structured response. */ }
      throw new Error(detail);
    }
    return response;
  };
  c.json = async (path, options, session) => (await c.request(path, options, session)).json();
  c.disconnect = () => {
    state.epoch += 1; state.connection = null; state.selected = state.active = null;
    $('token').value = '';
    $('connection-state').textContent = 'Disconnected. A running analysis is not cancelled by disconnecting.';
    for (const id of ['history', 'artifacts', 'results', 'progress-rows']) $(id).replaceChildren();
    $('progress-table').hidden = true;
    for (const id of ['log', 'progress', 'run-state', 'scenario']) $(id).textContent = '';
    $('progress-stage').textContent = 'No analysis selected';
    c.clearDocuments(); c.clearPlots(); c.updateButtons();
  };
  $('connect-form').onsubmit = async event => {
    event.preventDefault(); c.error('');
    const token = $('token').value.trim(), base = $('bridge-url').value.trim();
    c.disconnect(); const generation = state.epoch;
    $('connection-state').textContent = 'Connecting…';
    try {
      const session = {base: validateBase(base), token};
      if (!token) throw new Error('Enter the session token printed by stlmc-gui.');
      const bridge = await c.json('/api/bridge', undefined, session);
      if (generation !== state.epoch) return;
      if (bridge.protocol !== 1) throw new Error('Unsupported bridge protocol. Update the local bridge.');
      const health = await c.json('/api/health', undefined, session);
      if (generation !== state.epoch) return;
      if (!health.stlmc) throw new Error(health.error || 'STLmc is unavailable in the bridge environment.');
      const documents = await c.fetchDocuments(session);
      if (generation !== state.epoch) return;
      state.connection = session; c.populateDocuments(documents);
      $('connection-state').textContent = 'Connected to ' + session.base + ' · bridge ' + (bridge.version || 'protocol 1');
      if (health.visualization && !health.visualization.available) c.error('Verification is available, but HTML visualization is not installed. Run: stlmc-installer install --visualize html');
      c.updateButtons(); await c.refresh();
    } catch (exception) {
      if (generation !== state.epoch) return;
      c.disconnect(); $('connection-state').textContent = 'Disconnected. Connection or runtime check failed.';
      c.error(c.message(exception));
    }
  };
  $('disconnect').onclick = c.disconnect;
  window.addEventListener('pagehide', c.disconnect);
}
