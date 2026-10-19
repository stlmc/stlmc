export function summarize(progress = {}, state, maximum, now = Date.now() / 1000) {
  const events = progress.events || [], rows = [];
  for (const event of events) {
    const data = event.data || {};
    if (event.event === 'bound_finished' && Object.hasOwn(data, 'bound')) rows.push({
      id: event.session + '-' + data.bound, goal: event.goal || 'Goal', bound: data.bound,
      query: String(data.result || 'unknown').toUpperCase(), seconds: Number(data.elapsed || 0),
    });
  }
  const latest = events.at(-1), active = ['running', 'stopping'].includes(state);
  if (!latest) return {rows, stage: active ? 'Preparing analysis — waiting for the first completed bound' : 'No completed bounds recorded', since: null, scenario: null};
  const data = latest.data || {}, goal = latest.goal || 'Goal';
  const started = [...events].reverse().find(event => event.event === 'run_started' && event.session === latest.session);
  const max = Number(started?.data?.max_bound ?? maximum);
  const scenario = progress.scenario?.session === latest.session ? progress.scenario.data : null;
  let stage;
  if (!active) stage = {completed: 'Analysis complete', cancelled: 'Analysis stopped', timed_out: 'Time limit reached', failed: 'Analysis failed', interrupted: 'Analysis interrupted'}[state] || state;
  else if (state === 'stopping') stage = 'Stopping analysis';
  else if (latest.event === 'run_finished') stage = 'Verification finished — preparing output';
  else if (latest.event === 'bound_finished' && (String(data.result).toLowerCase() === 'sat' || Number(data.bound) >= max)) stage = goal + ' — finalizing result';
  else {
    const bound = Math.max(latest.event === 'bound_finished' ? Number(data.bound) + 1 : 0, Number(scenario?.bound || 0));
    stage = goal + ' — preparing / checking bound ' + bound + ' of ' + max;
  }
  return {rows, stage, scenario, since: active ? Math.max(0, now - latest.time) : null};
}

export function renderProgress(c, job) {
  const {$} = c, progress = summarize(job.progress, job.state, job.request.bound);
  $('progress-stage').textContent = progress.stage + (progress.since === null ? '' : ' · ' + progress.since.toFixed(1) + 's since last bound update');
  $('scenario').textContent = progress.scenario ? 'Scenarios: ' + ['generated', 'completed', 'pending', 'active_workers'].map(key => (progress.scenario[key] || 0) + ' ' + key.replaceAll('_', ' ')).join(' · ') : '';
  $('progress-rows').replaceChildren();
  for (const row of progress.rows) {
    const tr = document.createElement('tr');
    for (const value of [row.goal, row.bound, row.query, row.seconds.toFixed(3) + 's']) {
      const td = document.createElement('td'); td.textContent = String(value); tr.append(td);
    }
    $('progress-rows').append(tr);
  }
  $('progress-table').hidden = !progress.rows.length;
  $('progress').textContent = JSON.stringify(job.progress || {}, null, 2);
}
