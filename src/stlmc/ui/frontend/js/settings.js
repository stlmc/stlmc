// This is a form adapter, not a configuration parser. STLmc owns all defaults,
// inheritance, model parsing, and configuration semantics.
const fields = [
  ['solver', 'solver', 'solver'], ['bound', 'bound', 'bound', 'number'],
  ['time-bound', 'time-bound', 'time_bound', 'number'],
  ['threshold', 'threshold', 'threshold', 'number'], ['goal', 'goal', 'goal'],
  ['two-step', 'two-step', 'two_step', 'boolean'], ['reach', 'reach', 'reach', 'boolean'],
  ['explicit', 'path-strategy', 'path_strategy', 'path'],
];

export function setupSettings(c) {
  const {$, state} = c, edits = new Map();
  let sequence = 0, timer, baseline = {};
  const read = (id, type) => type === 'boolean' ? $(id).checked : type === 'path' ?
    ($(id).checked ? 'explicit' : 'symbolic') : type === 'number' ?
    ($(id).value === '' ? null : Number($(id).value)) : $(id).value;
  const decoded = (common, key, type) => type === 'boolean' ? common[key] === 'true' :
    type === 'number' ? (common[key] == null ? null : Number(common[key])) :
    key === 'goal' && common[key] === 'all' ? '' : common[key] ?? '';
  for (const [id, key, request, type] of fields) {
    $(id).addEventListener('input', () => {
      const value = read(id, type);
      if (state.settingsReady && value === baseline[key]) edits.delete(request);
      else edits.set(request, value);
    });
  }
  c.settingsPayload = () => Object.fromEntries(edits);
  c.syncSettings = async () => {
    clearTimeout(timer);
    if (!state.connection) return false;
    const current = ++sequence, generation = state.epoch;
    const model = $('model').value, config = $('config').value;
    state.settingsReady = false; c.updateButtons();
    $('settings-state').textContent = 'Reading settings with STLmc…';
    try {
      const info = await c.json('/api/inspect', {method: 'POST', body: JSON.stringify({model, config})});
      if (current !== sequence || generation !== state.epoch || model !== $('model').value || config !== $('config').value) return false;
      const diagnostics = info.diagnostics || [];
      for (const kind of ['model', 'config']) c.setDiagnostics?.(kind, diagnostics.filter(item => item.source === kind));
      if (!info.common) {
        $('settings-state').textContent = 'Configuration has an error. See the configuration editor.';
        c.updateButtons(); return false;
      }
      baseline = Object.fromEntries(fields.map(([, key, , type]) => [key, decoded(info.common, key, type)]));
      const solverValue = edits.get('solver') ?? baseline.solver;
      $('solver').replaceChildren(...info.solver_choices.map(value => new Option(value, value)));
      $('solver').value = solverValue;
      const goalValue = edits.get('goal') ?? baseline.goal;
      const goals = new Set(info.goals);
      // Preserve an explicitly configured combination/label: never silently
      // replace an unknown configured goal with "all".
      if (goalValue) goals.add(goalValue);
      $('goal').replaceChildren(new Option('All goals', ''), ...[...goals].map(label => new Option(label, label)));
      for (const [id, key, request, type] of fields) {
        const value = edits.has(request) ? edits.get(request) : baseline[key];
        if (type === 'boolean') $(id).checked = value;
        else if (type === 'path') $(id).checked = value === 'explicit';
        else $(id).value = value ?? '';
      }
      $('settings-state').textContent = info.model_error ? 'Model has an error. See the model editor.' :
        'Settings loaded from STLmc. Unchanged fields retain the configuration values.';
      state.settingsReady = !info.model_error;
      c.updateButtons(); return state.settingsReady;
    } catch (error) {
      if (current === sequence && generation === state.epoch) {
        $('settings-state').textContent = 'Configuration error: ' + c.message(error);
        state.settingsReady = false; c.updateButtons();
      }
      return false;
    }
  };
  c.inputsChanged = (kind, reset = false) => {
    c.setDiagnostics?.(kind, []);
    if (reset && kind === 'config') edits.clear();
    state.settingsReady = false; c.updateButtons();
    clearTimeout(timer); timer = setTimeout(() => c.syncSettings(), 350);
  };
}
