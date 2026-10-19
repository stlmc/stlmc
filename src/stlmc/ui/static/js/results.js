import {renderProgress} from './progress.js';

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
