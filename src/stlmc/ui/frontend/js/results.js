import {renderProgress} from './progress.js';

export function failureSummary(job) {
  const titles = {failed: 'Analysis failed', timed_out: 'Analysis timed out',
    interrupted: 'Analysis was interrupted', cancelled: 'Analysis was cancelled'};
  if (!titles[job.state]) return null;
  let reason = '';
  if (job.termination_reason === 'timeout' || job.state === 'timed_out') {
    const limit = job.request?.timeout;
    reason = Number.isFinite(limit) ? 'The wall-clock time limit of ' + limit + ' seconds was reached.' :
      'The wall-clock time limit was reached.';
  } else if (job.termination_reason === 'user_stop') {
    reason = 'Analysis was stopped at your request.';
  } else if (job.termination_reason === 'server_shutdown') {
    reason = 'Analysis was interrupted because the GUI server was shutting down.';
  } else if (job.state === 'interrupted' || job.state === 'cancelled') {
    reason = 'The execution was interrupted; no termination cause was recorded.';
  }
  const lines = (job.log || '').replace(/\x1b\[[0-9;]*[A-Za-z]/g, '').trim().split('\n');
  const tail = lines.filter(line => line.trim()).slice(-8).join('\n').slice(-2000);
  return {title: titles[job.state], reason, detail: tail || 'No diagnostic output was recorded.',
    exit: job.exit_code == null ? '' : ' (exit code ' + job.exit_code + ')'};
}

export function setupResults(c) {
  const {$, state} = c;
  let plotSignature = '', plotUrls = [];
  c.clearPlots = () => {
    $('plots').replaceChildren(); plotUrls.forEach(url => URL.revokeObjectURL(url)); plotUrls = []; plotSignature = '';
    $('plot-empty').hidden = false;
  };
  const filePath = (run, name) => '/api/runs/' + encodeURIComponent(run) + '/files/' + encodeURIComponent(name);
  c.showRun = async (id, session, generation) => {
    const job = await c.json('/api/runs/' + encodeURIComponent(id), undefined, session);
    if (generation !== state.epoch || state.selected !== id) return;
    $('run-state').textContent = 'Run ' + id + ' — ' + job.state;
    const failure = failureSummary(job);
    $('run-failure').hidden = !failure;
    if (failure) {
      $('failure-title').textContent = failure.title + failure.exit;
      $('failure-summary').textContent = [failure.reason, failure.detail].filter(Boolean).join('\n\n');
      $('failure-log').onclick = () => c.selectTab('log');
      if (!state.active) $('activity').textContent = failure.title;
    }
    $('log').textContent = (job.log || '').replace(/\x1b\[[0-9;]*[A-Za-z]/g, '');
    renderProgress(c, job);
    $('results').replaceChildren();
    for (const result of job.results || []) {
      const card = document.createElement('article'); card.className = 'result-card';
      const title = document.createElement('h3'); title.textContent = result.status.toUpperCase(); card.append(title);
      const summary = document.createElement('p'); summary.textContent = [result.scope || 'bound ' + result.bound, Number(result.elapsed || 0).toFixed(3) + 's'].join(' · '); card.append(summary);
      const formula = document.createElement('p'); formula.className = 'formula'; formula.textContent = result.formula || ''; card.append(formula);
      if (result.guarantee) { const guarantee = document.createElement('p'); guarantee.textContent = result.guarantee; card.append(guarantee); }
      $('results').append(card);
    }
    for (const warning of job.visualization_errors || []) {
      const row = document.createElement('p'); row.className = 'warning'; row.textContent = warning; $('results').append(row);
    }
    if (!(job.results || []).length) { const row = document.createElement('p'); row.className = 'muted'; row.textContent = ['running', 'stopping'].includes(job.state) ? 'Analysis is running…' : 'No verification result. Inspect the execution log for details.'; $('results').append(row); }
    $('artifacts').replaceChildren();
    for (const name of job.files || []) {
      const button = document.createElement('button'); button.type = 'button'; button.textContent = 'Download ' + name;
      button.onclick = async () => {
        try {
          if (generation !== state.epoch) return;
          const blob = await (await c.request(filePath(id, name), {}, session)).blob();
          if (generation === state.epoch) c.download(blob, name);
        } catch (exception) { if (generation === state.epoch) c.error(c.message(exception)); }
      };
      $('artifacts').append(button);
    }
    const html = (job.files || []).filter(name => name.endsWith('.html')), signature = id + ':' + job.state + ':' + html.join('|');
    if (signature !== plotSignature) {
      c.clearPlots();
      for (const name of html) {
        const blob = await (await c.request(filePath(id, name), {}, session)).blob();
        if (generation !== state.epoch || state.selected !== id) return;
        const url = URL.createObjectURL(new Blob([blob], {type: 'text/html'})); plotUrls.push(url);
        const frame = document.createElement('iframe'); frame.title = name; frame.sandbox = 'allow-scripts'; frame.src = url; $('plots').append(frame);
      }
      plotSignature = signature;
      $('plot-empty').hidden = !!html.length;
    }
  };
}
