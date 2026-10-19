"""Present real printer events without inventing completion percentages."""


def summarize(progress, state, max_bound, now):
    events = progress.get('events', [])
    scenario = progress.get('scenario')
    rows = []
    latest = None
    active = state in {'running', 'stopping'}
    for event in events:
        data = event.get('data', {})
        if event['event'] == 'bound_finished' and 'bound' in data:
            rows.append({'id': '{}-{}'.format(event['session'], data['bound']),
                         'goal': event.get('goal') or 'Goal', 'bound': data['bound'],
                         'query': str(data.get('result', 'unknown')).upper(),
                         'seconds': float(data.get('elapsed', 0))})
        latest = event
    if latest is None:
        return dict(rows=rows, stage='Preparing analysis' if active else 'No bound progress recorded',
                    since=None, current=None, scenario=None)
    data = latest.get('data', {})
    goal = latest.get('goal') or 'Goal'
    maximum = max_bound
    for event in reversed(events):
        if event['event'] == 'run_started' and event['session'] == latest['session']:
            maximum = int(event['data'].get('max_bound', max_bound))
            break
    current = None
    if not active:
        stage = {'completed': 'Analysis complete', 'cancelled': 'Analysis stopped',
                 'timed_out': 'Time limit reached', 'failed': 'Analysis failed',
                 'interrupted': 'Analysis interrupted'}.get(state, state)
    elif state == 'stopping':
        stage = 'Stopping analysis'
    elif latest['event'] == 'run_finished':
        stage = 'Verification finished · preparing output'
    elif latest['event'] == 'bound_finished' and (str(data.get('result')).lower() == 'sat' or int(data['bound']) >= maximum):
        stage = '{} · finalizing result'.format(goal)
    else:
        current = int(data.get('bound', -1)) + 1 if latest['event'] == 'bound_finished' else 0
        if scenario and scenario.get('session') == latest['session']:
            candidate = int(scenario['data'].get('bound', current))
            current = max(current, candidate)
        stage = '{} · preparing / checking bound {} of {}'.format(goal, current, maximum)
    if not scenario or scenario.get('session') != latest['session']:
        scenario = None
    return dict(rows=rows, stage=stage, current=current,
                since=max(0, now - latest['time']) if active else None,
                scenario=scenario['data'] if scenario else None)
