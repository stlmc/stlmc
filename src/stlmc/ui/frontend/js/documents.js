export function setupDocuments(c) {
  const {$, state} = c;
  const buffers = {model: null, config: null};
  const loading = {model: 0, config: 0};
  const edits = {model: 0, config: 0};
  const pending = {model: 0, config: 0};
  const external = {model: null, config: null}, observed = {model: null, config: null};
  let watching = false, inventory = '';
  const selector = kind => $(kind === 'model' ? 'documents' : 'config-documents');
  const suffix = kind => kind === 'model' ? '.model' : '.cfg';
  function status(kind) {
    const saved = buffers[kind];
    const dirty = !saved || saved.text !== $(kind).value || saved.name !== $(kind + '-name').value;
    $(kind + '-status').textContent = external[kind] === 'removed' ? 'Removed on disk; buffer kept' :
      external[kind] === 'changed' ? 'Changed on disk; local edits kept. Reload or save as a new file.' :
      dirty ? 'Unsaved changes' : 'Saved';
    $(kind + '-status').classList.toggle('dirty', dirty || !!external[kind]);
  }
  function applyDocument(kind, doc, reset = true) {
    external[kind] = null;
    buffers[kind] = doc; $(kind).value = doc.text; $(kind + '-name').value = doc.name;
    status(kind); c.inputsChanged?.(kind, reset);
  }
  function confirmReplace(kind) {
    return !$(kind).value || (buffers[kind] && buffers[kind].text === $(kind).value && buffers[kind].name === $(kind + '-name').value)
      || window.confirm('Discard unsaved ' + kind + ' changes and load this file?');
  }
  function beginLoad(kind) {
    return {sequence: ++loading[kind], generation: state.epoch, revision: edits[kind],
      text: $(kind).value, name: $(kind + '-name').value};
  }
  function mayApply(kind, operation) {
    if (operation.sequence !== loading[kind] || operation.generation !== state.epoch) return false;
    if (operation.revision !== edits[kind] || operation.text !== $(kind).value || operation.name !== $(kind + '-name').value) {
      c.error('The ' + kind + ' was edited while the file was loading. Your edits were kept; load the file again to replace them.');
      return false;
    }
    return true;
  }
  c.fetchDocuments = session => Promise.all([c.json('/api/documents?kind=model', undefined, session), c.json('/api/documents?kind=cfg', undefined, session)]);
  c.populateDocuments = lists => {
    for (const [index, kind] of ['model', 'config'].entries()) {
      const previous = selector(kind).value;
      selector(kind).replaceChildren(new Option('Choose a ' + (kind === 'model' ? 'model' : 'configuration'), ''));
      for (const doc of lists[index]) selector(kind).append(new Option(doc.name, doc.name));
      if (lists[index].some(doc => doc.name === previous)) selector(kind).value = previous;
    }
  };
  c.watchDocuments = async () => {
    if (!state.connection || watching) return;
    watching = true;
    const session = state.connection, generation = state.epoch;
    try {
      const snapshot = await c.json('/api/documents/watch', undefined, session);
      if (generation !== state.epoch) return;
      const signature = JSON.stringify(snapshot);
      if (signature !== inventory) {
        c.populateDocuments([snapshot.model, snapshot.cfg]); inventory = signature;
      }
      for (const [kind, entries] of [['model', snapshot.model], ['config', snapshot.cfg]]) {
        const saved = buffers[kind], sequence = loading[kind];
        if (!saved || pending[kind] || saved.name !== $(kind + '-name').value) continue;
        const version = entries.find(entry => entry.name === saved.name)?.version ?? null;
        if (observed[kind]?.buffer === saved && observed[kind]?.version === version) continue;
        if (version === null) {
          external[kind] = 'removed'; status(kind);
          observed[kind] = {buffer: saved, version}; continue;
        }
        const doc = await c.json('/api/documents/' + encodeURIComponent(saved.name), undefined, session);
        if (generation !== state.epoch) return;
        if (buffers[kind] !== saved || loading[kind] !== sequence || pending[kind]) continue;
        if (doc.revision !== saved.revision) {
          if ($(kind).value === saved.text && $(kind + '-name').value === saved.name) {
            applyDocument(kind, doc, false);
          } else { external[kind] = 'changed'; status(kind); }
        } else { external[kind] = null; status(kind); }
        observed[kind] = {buffer: buffers[kind], version};
      }
      $('watch-state').textContent = 'Watching model/config folder · checks every 2 seconds';
    } catch (error) {
      if (generation === state.epoch) $('watch-state').textContent = 'File watch paused: ' + c.message(error) + ' — retrying automatically';
    } finally { watching = false; }
  };
  c.clearDocuments = () => {
    inventory = '';
    $('watch-state').textContent = 'File watch starts after connecting.';
    for (const kind of ['model', 'config']) {
      selector(kind).replaceChildren(new Option('Choose a document', ''));
      // Buffers stay editable, but revisions belong to the disconnected bridge.
      buffers[kind] = null; external[kind] = null; observed[kind] = null; status(kind);
      c.setDiagnostics?.(kind, []);
    }
  };
  for (const kind of ['model', 'config']) {
    const load = async () => {
      const generation = state.epoch, name = selector(kind).value;
      pending[kind] += 1;
      try {
        if (!name || !confirmReplace(kind)) return;
        const operation = beginLoad(kind);
        const doc = await c.json('/api/documents/' + encodeURIComponent(name));
        if (!mayApply(kind, operation)) return;
        applyDocument(kind, doc);
      } catch (exception) { if (generation === state.epoch) c.error(c.message(exception)); }
      finally { pending[kind] -= 1; }
    };
    $(kind === 'model' ? 'load-document' : 'load-config').onclick = load;
    $('save-' + kind).onclick = async () => {
      const generation = state.epoch, session = state.connection;
      pending[kind] += 1;
      try {
        const name = $(kind + '-name').value.trim();
        if (!name.endsWith(suffix(kind)) || !name || /[\\/]/.test(name)) throw new Error('Use a filename ending in ' + suffix(kind) + ', without directories.');
        const text = $(kind).value, saved = buffers[kind];
        const sequence = ++loading[kind];
        const doc = await c.json('/api/documents/' + encodeURIComponent(name), {method: 'PUT', body: JSON.stringify({text, revision: saved && saved.name === name ? saved.revision : null})}, session);
        if (generation !== state.epoch || sequence !== loading[kind] || $(kind + '-name').value.trim() !== name) return;
        buffers[kind] = doc; external[kind] = null; status(kind);
        const docs = await c.fetchDocuments(session);
        if (generation !== state.epoch || sequence !== loading[kind] || $(kind + '-name').value.trim() !== name) return;
        c.populateDocuments(docs); selector(kind).value = name;
      } catch (exception) { if (generation === state.epoch) c.error(c.message(exception)); }
      finally { pending[kind] -= 1; }
    };
    $(kind).oninput = () => { edits[kind] += 1; status(kind); c.inputsChanged?.(kind); };
    $(kind + '-name').oninput = () => { edits[kind] += 1; status(kind); };
    $('open-' + kind).onchange = async event => {
      const file = event.target.files[0]; if (!file) return;
      if (file.size > (kind === 'model' ? 500000 : 100000)) { c.error('File is too large for the bridge.'); return; }
      if (!file.name.endsWith(suffix(kind))) { c.error('Choose a ' + suffix(kind) + ' file.'); return; }
      if (!confirmReplace(kind)) { event.target.value = ''; return; }
      const operation = beginLoad(kind);
      pending[kind] += 1;
      try {
        const text = await file.text();
        if (!mayApply(kind, operation)) return;
        $(kind).value = text; $(kind + '-name').value = file.name; buffers[kind] = null; external[kind] = null; status(kind); c.inputsChanged?.(kind, true);
      } catch (exception) { if (operation.generation === state.epoch) c.error(c.message(exception)); }
      finally { pending[kind] -= 1; event.target.value = ''; }
    };
    $('download-' + kind).onclick = () => c.download(new Blob([$(kind).value], {type: 'text/plain;charset=utf-8'}), $(kind + '-name').value.trim() || 'untitled' + suffix(kind));
  }
}
