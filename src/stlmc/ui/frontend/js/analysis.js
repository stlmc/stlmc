export function setupAnalysis(c) {
  const {$, state} = c;
  let refreshError = '';
  c.refresh = async () => {
    if (!state.connection || state.refreshing) return;
    state.refreshing = true; const session = state.connection, generation = state.epoch;
    let reached = false;
    try {
      const jobs = await c.json('/api/runs', undefined, session);
      if (generation !== state.epoch) return;
      reached = true;
      state.connectionHealth = 'connected'; state.history = jobs;
      state.active = jobs.find(job => ['running', 'stopping'].includes(job.state)) || null;
      if (!state.selected && jobs.length) state.selected = jobs[0].id;
      $('history').replaceChildren();
      for (const job of jobs) {
        const button = document.createElement('button'); button.type = 'button';
        button.textContent = new Date(job.started * 1000).toLocaleString() + ' · ' + job.state + (job.request.solver ? ' · ' + job.request.solver : '');
        button.setAttribute('aria-current', String(job.id === state.selected));
        button.onclick = () => { if (generation !== state.epoch) return; state.selected = job.id; c.clearPlots(); c.selectTab('results'); c.refresh(); };
        $('history').append(button);
      }
      c.updateButtons(); if (state.selected) await c.showRun(state.selected, session, generation);
      if (generation === state.epoch && refreshError && $('error').textContent === refreshError) c.error('');
      refreshError = '';
    } catch (exception) {
      if (generation === state.epoch) {
        refreshError = c.message(exception); c.error(refreshError);
        if (!reached) state.connectionHealth = 'unreachable';
        c.updateButtons();
      }
    }
    finally { state.refreshing = false; }
  };
  $('run-form').onsubmit = async event => {
    event.preventDefault(); c.error(''); const generation = state.epoch;
    $('run-failure').hidden = true;
    try {
      if (!await c.syncSettings()) return;
      const payload = {model: $('model').value, config: $('config').value,
        timeout: Number($('timeout').value), ...c.settingsPayload()};
      const job = await c.json('/api/runs', {method: 'POST', body: JSON.stringify(payload)});
      if (generation !== state.epoch) return;
      $('run-failure').hidden = true;
      for (const id of ['results', 'artifacts', 'progress-rows']) $(id).replaceChildren();
      for (const id of ['log', 'progress', 'scenario']) $(id).textContent = '';
      $('progress-table').hidden = true;
      $('run-state').textContent = 'Run ' + job.id + ' — running';
      state.selected = job.id; state.active = job; c.updateButtons(); c.clearPlots(); c.selectTab('results'); await c.refresh();
    } catch (exception) { if (generation === state.epoch) c.error(c.message(exception)); }
  };
  $('stop').onclick = async () => {
    const generation = state.epoch;
    try {
      if (state.active) await c.json('/api/runs/' + encodeURIComponent(state.active.id) + '/stop', {method: 'POST'});
      if (generation === state.epoch) await c.refresh();
    } catch (exception) { if (generation === state.epoch) c.error(c.message(exception)); }
  };
  $('clear-history').onclick = async () => {
    const ids = (state.history || []).filter(job => !['running', 'stopping'].includes(job.state)).map(job => job.id);
    if (!ids.length || !window.confirm('Permanently delete ' + ids.length + ' finished run(s), including logs and artifacts? Model/config files and running analyses will be kept.')) return;
    const generation = state.epoch;
    try {
      const result = await c.json('/api/runs/clear', {method: 'POST', body: JSON.stringify({run_ids: ids})});
      if (generation !== state.epoch) return;
      if (result.deleted.includes(state.selected)) {
        state.selected = null; c.clearPlots();
        for (const id of ['results', 'artifacts', 'progress-rows']) $(id).replaceChildren();
        for (const id of ['log', 'progress', 'run-state', 'scenario', 'progress-stage']) $(id).textContent = '';
        $('run-failure').hidden = true; $('progress-table').hidden = true;
      }
      await c.refresh();
      if (result.kept.length) c.error(result.kept.length + ' run(s) were kept because they may still be active.');
    } catch (error) { if (generation === state.epoch) c.error(c.message(error)); }
  };
}
