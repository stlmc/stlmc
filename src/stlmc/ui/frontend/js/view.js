import {installEditor} from './editor.js';

export function setupView(c) {
  const {$, state} = c;
  c.selectTab = name => {
    for (const tab of document.querySelectorAll('[data-tab]')) {
      const selected = tab.dataset.tab === name;
      tab.setAttribute('aria-selected', String(selected)); tab.tabIndex = selected ? 0 : -1;
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
  const editors = {};
  for (const kind of ['model', 'config']) editors[kind] = installEditor($(kind), kind);
  c.setDiagnostics = (kind, diagnostics) => editors[kind].setDiagnostics(diagnostics);
  $('editor-layout').onchange = () => {
    $('editors').dataset.layout = $('editor-layout').value;
    for (const editor of Object.values(editors)) editor.resize();
  };
  c.updateButtons = () => {
    const connected = !!state.connection && state.connectionHealth !== 'unreachable';
    $('run').disabled = !connected || !!state.active || !state.settingsReady;
    $('stop').disabled = !connected || !state.active || state.active.state === 'stopping';
    for (const id of ['load-document', 'load-config', 'save-model', 'save-config']) $(id).disabled = !connected;
    $('runtime-state').textContent = state.connectionHealth === 'connecting' ? 'Connecting…' :
      state.connectionHealth === 'unreachable' ? 'Connection lost' : connected ? 'Connected' : 'Disconnected';
    $('runtime-state').classList.toggle('connected', connected);
    $('clear-history').disabled = !connected || !(state.history || []).some(job => !['running', 'stopping'].includes(job.state));
    $('activity').textContent = state.active ? (state.active.state === 'stopping' ? 'Stopping analysis…' : 'Analysis in progress') : 'Ready to run';
    $('activity').classList.toggle('running', !!state.active);
  };
  c.download = (blob, name) => {
    const url = URL.createObjectURL(blob), anchor = document.createElement('a');
    anchor.href = url; anchor.download = name; document.body.append(anchor); anchor.click(); anchor.remove();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
  };
}
