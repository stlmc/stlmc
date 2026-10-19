export function setupView(c) {
  const {$, state} = c;
  c.selectTab = name => {
    for (const tab of document.querySelectorAll('[data-tab]')) {
      const selected = tab.dataset.tab === name;
      tab.setAttribute('aria-selected', String(selected));
      tab.tabIndex = selected ? 0 : -1;
      $('panel-' + tab.dataset.tab).hidden = !selected;
    }
  };
  const tabs = [...document.querySelectorAll('[data-tab]')];
  for (const tab of tabs) {
    tab.onclick = () => c.selectTab(tab.dataset.tab);
    tab.onkeydown = event => {
      let index = tabs.indexOf(tab);
      if (event.key === 'ArrowRight') index = (index + 1) % tabs.length;
      else if (event.key === 'ArrowLeft') index = (index + tabs.length - 1) % tabs.length;
      else if (event.key === 'Home') index = 0;
      else if (event.key === 'End') index = tabs.length - 1;
      else return;
      event.preventDefault(); c.selectTab(tabs[index].dataset.tab); tabs[index].focus();
    };
  }
  $('editor-layout').onchange = () => { $('editors').dataset.layout = $('editor-layout').value; };
  c.updateButtons = () => {
    const connected = !!state.connection;
    $('run').disabled = !connected || !!state.active;
    $('stop').disabled = !connected || !state.active || state.active.state === 'stopping';
    for (const id of ['load-document', 'load-config', 'save-model', 'save-config']) $(id).disabled = !connected;
    $('runtime-state').textContent = connected ? 'Connected' : 'Disconnected';
    $('runtime-state').classList.toggle('connected', connected);
    $('activity').textContent = state.active ? (state.active.state === 'stopping' ? 'Stopping analysis…' : 'Analysis in progress') : 'Ready to run';
    $('activity').classList.toggle('running', !!state.active);
  };
  c.download = (blob, name) => {
    const url = URL.createObjectURL(blob), anchor = document.createElement('a');
    anchor.href = url; anchor.download = name;
    document.body.append(anchor); anchor.click(); anchor.remove();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
  };
  for (const kind of ['model', 'config']) installEditor($(kind), kind);
}

// A small, dependency-free presentation layer. The textarea remains the real
// editable/accessibility control; colored spans never interpret model HTML.
function installEditor(editor, kind) {
  const wrapper = document.createElement('div'); wrapper.className = 'code-editor';
  const gutter = document.createElement('pre'); gutter.className = 'line-numbers'; gutter.setAttribute('aria-hidden', 'true');
  const colors = document.createElement('pre'); colors.className = 'syntax-layer'; colors.setAttribute('aria-hidden', 'true');
  editor.setAttribute('aria-label', kind === 'model' ? 'Model' : 'Configuration (optional)');
  editor.parentNode.insertBefore(wrapper, editor); wrapper.append(gutter, colors, editor);
  const keywords = new Set(['mode', 'inv', 'flow', 'jump', 'init', 'proposition', 'goal', 'reach', 'const', 'extends', 'common', 'z3', 'dreal', 'yices', 'cvc5']);
  function highlight() {
    const text = editor.value, parts = document.createDocumentFragment();
    const pattern = /'''[\s\S]*?(?:'''|$)|#[^\n]*|"(?:\\.|[^"\\])*"|\b(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?\b|\b[A-Za-z_][A-Za-z_0-9]*\b|=>|->|>=|<=|!=|[+*=<>~&|]/g;
    let end = 0;
    for (const match of text.matchAll(pattern)) {
      if (match.index > end) parts.append(document.createTextNode(text.slice(end, match.index)));
      const token = match[0], span = document.createElement('span');
      span.textContent = token;
      span.className = 'syntax-' + (token.startsWith('#') || token.startsWith("'''") ? 'comment' : token.startsWith('"') ? 'string' : keywords.has(token) ? 'keyword' : /^(true|false|int|bool|real|inf|and|or|not)$/.test(token) ? 'builtin' : /^[\d.]/.test(token) ? 'number' : /^[A-Za-z_]/.test(token) ? 'variable' : 'operator');
      parts.append(span); end = match.index + token.length;
    }
    parts.append(document.createTextNode(text.slice(end) + '\n'));
    colors.replaceChildren(parts);
    gutter.textContent = Array.from({length: text.split('\n').length}, (_, index) => index + 1).join('\n');
    syncScroll();
  }
  function syncScroll() { colors.scrollTop = gutter.scrollTop = editor.scrollTop; colors.scrollLeft = editor.scrollLeft; }
  editor.addEventListener('input', highlight); editor.addEventListener('scroll', syncScroll);
  // Document loads replace .value without firing input. Refresh just the
  // presentation when the value changes; do not alter selection or undo state.
  let previous;
  setInterval(() => { if (previous !== editor.value) { previous = editor.value; highlight(); } }, 250);
  highlight();
}
