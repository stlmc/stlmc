export function setupDocuments(c) {
  const {$, state} = c;
  const buffers = {model: null, config: null};
  const loading = {model: 0, config: 0};
  const edits = {model: 0, config: 0};
  const selector = kind => $(kind === 'model' ? 'documents' : 'config-documents');
  const suffix = kind => kind === 'model' ? '.model' : '.cfg';
  function status(kind) {
    const saved = buffers[kind];
    const dirty = !saved || saved.text !== $(kind).value || saved.name !== $(kind + '-name').value;
    $(kind + '-status').textContent = dirty ? 'Unsaved changes' : 'Saved';
    $(kind + '-status').classList.toggle('dirty', dirty);
  }
  function applyDocument(kind, doc) {
    buffers[kind] = doc; $(kind).value = doc.text; $(kind + '-name').value = doc.name;
    status(kind); updateGoals();
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
  function updateGoals() {
    // Suggestions only: the solver parser remains authoritative. Do not offer
    // proposition aliases as selectable goal labels while editing a model.
    const clean = $('model').value.replace(/'''[\s\S]*?(?:'''|$)|#[^\n]*/g, '');
    const section = /\bgoal\s*:/.exec(clean);
    const goals = section ? clean.slice(section.index + section[0].length) : '';
    const labels = [...goals.matchAll(/\[\s*([A-Za-z][A-Za-z0-9]*)\s*\]\s*:/g)].map(match => match[1]);
    $('goal-labels').replaceChildren(...[...new Set(labels)].map(label => new Option(label, label)));
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
  c.clearDocuments = () => {
    for (const kind of ['model', 'config']) {
      selector(kind).replaceChildren(new Option('Choose a document', ''));
      // Buffers stay editable, but revisions belong to the disconnected bridge.
      buffers[kind] = null; status(kind);
    }
  };
  for (const kind of ['model', 'config']) {
    const load = async () => {
      const generation = state.epoch, name = selector(kind).value;
      try {
        if (!name || !confirmReplace(kind)) return;
        const operation = beginLoad(kind);
        const doc = await c.json('/api/documents/' + encodeURIComponent(name));
        if (!mayApply(kind, operation)) return;
        applyDocument(kind, doc);
      } catch (exception) { if (generation === state.epoch) c.error(c.message(exception)); }
    };
    $(kind === 'model' ? 'load-document' : 'load-config').onclick = load;
    $('save-' + kind).onclick = async () => {
      const generation = state.epoch, session = state.connection;
      try {
        const name = $(kind + '-name').value.trim();
        if (!name.endsWith(suffix(kind)) || !name || /[\\/]/.test(name)) throw new Error('Use a filename ending in ' + suffix(kind) + ', without directories.');
        const text = $(kind).value, saved = buffers[kind];
        const sequence = ++loading[kind];
        const doc = await c.json('/api/documents/' + encodeURIComponent(name), {method: 'PUT', body: JSON.stringify({text, revision: saved && saved.name === name ? saved.revision : null})}, session);
        if (generation !== state.epoch || sequence !== loading[kind] || $(kind + '-name').value.trim() !== name) return;
        buffers[kind] = doc; status(kind);
        const docs = await c.fetchDocuments(session);
        if (generation !== state.epoch || sequence !== loading[kind] || $(kind + '-name').value.trim() !== name) return;
        c.populateDocuments(docs); selector(kind).value = name;
      } catch (exception) { if (generation === state.epoch) c.error(c.message(exception)); }
    };
    $(kind).oninput = () => { edits[kind] += 1; status(kind); if (kind === 'model') updateGoals(); };
    $(kind + '-name').oninput = () => { edits[kind] += 1; status(kind); };
    $(kind).onkeydown = event => {
      // Shift+Tab always leaves the editor, so indentation never traps focus.
      if (event.key === 'Tab' && !event.shiftKey && !event.ctrlKey && !event.altKey && !event.metaKey) {
        event.preventDefault(); const editor = $(kind), start = editor.selectionStart, end = editor.selectionEnd;
        editor.setRangeText('  ', start, end, 'end'); editor.dispatchEvent(new Event('input'));
      }
    };
    $('open-' + kind).onchange = async event => {
      const file = event.target.files[0]; if (!file) return;
      if (file.size > (kind === 'model' ? 500000 : 100000)) { c.error('File is too large for the bridge.'); return; }
      if (!file.name.endsWith(suffix(kind))) { c.error('Choose a ' + suffix(kind) + ' file.'); return; }
      if (!confirmReplace(kind)) { event.target.value = ''; return; }
      const operation = beginLoad(kind);
      try {
        const text = await file.text();
        if (!mayApply(kind, operation)) return;
        $(kind).value = text; $(kind + '-name').value = file.name; buffers[kind] = null; status(kind); updateGoals();
      } catch (exception) { if (operation.generation === state.epoch) c.error(c.message(exception)); }
      finally { event.target.value = ''; }
    };
    $('download-' + kind).onclick = () => c.download(new Blob([$(kind).value], {type: 'text/plain;charset=utf-8'}), $(kind + '-name').value.trim() || 'untitled' + suffix(kind));
  }
}
