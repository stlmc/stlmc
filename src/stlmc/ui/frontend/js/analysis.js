export function setupAnalysis(c) {
  const {$, state} = c;
  let refreshError = '';
  c.refresh = async () => {
    if (!state.connection || state.refreshing) return;
    state.refreshing = true; const session = state.connection, generation = state.epoch;
    try {
      const jobs = await c.json('/api/runs', undefined, session);
      if (generation !== state.epoch) return;
      state.active = jobs.find(job => ['running', 'stopping'].includes(job.state)) || null;
      if (!state.selected && jobs.length) state.selected = jobs[0].id;
      $('history').replaceChildren();
      for (const job of jobs) {
        const button = document.createElement('button'); button.type = 'button';
        button.textContent = new Date(job.started * 1000).toLocaleString() + ' · ' + job.state + ' · ' + job.request.solver;
        button.setAttribute('aria-current', String(job.id === state.selected));
        button.onclick = () => { if (generation !== state.epoch) return; state.selected = job.id; c.clearPlots(); c.selectTab('results'); c.refresh(); };
        $('history').append(button);
      }
      c.updateButtons(); if (state.selected) await c.showRun(state.selected, session, generation);
      if (generation === state.epoch && refreshError && $('error').textContent === refreshError) c.error('');
      refreshError = '';
    } catch (exception) {
      if (generation === state.epoch) { refreshError = c.message(exception); c.error(refreshError); }
    }
    finally { state.refreshing = false; }
  };
  $('run-form').onsubmit = async event => {
    event.preventDefault(); c.error(''); const generation = state.epoch;
    try {
      const payload = {model: $('model').value, config: $('config').value, goal: $('goal').value.trim(),
        solver: $('solver').value, bound: Number($('bound').value), time_bound: Number($('time-bound').value),
        threshold: Number($('threshold').value), timeout: Number($('timeout').value),
        path_strategy: $('explicit').checked ? 'explicit' : 'symbolic', two_step: $('two-step').checked, reach: $('reach').checked};
      const job = await c.json('/api/runs', {method: 'POST', body: JSON.stringify(payload)});
      if (generation !== state.epoch) return;
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
}
