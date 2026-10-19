import {setupView} from './js/view.js';
import {configureLocalConnection, setupConnection} from './js/connection.js';
import {setupDocuments} from './js/documents.js';
import {setupAnalysis} from './js/analysis.js';
import {setupResults} from './js/results.js';
import {setupSettings} from './js/settings.js';

const context = {
  $: id => document.getElementById(id),
  state: {connection: null, epoch: 0, selected: null, active: null, refreshing: false},
};
context.error = message => { context.$('error').textContent = message || ''; };
context.message = error => error instanceof Error ? error.message : String(error);
setupView(context);
setupSettings(context);
setupDocuments(context);
setupResults(context);
setupAnalysis(context);
context.$('connect').disabled = true;
await configureLocalConnection(context);
setupConnection(context);
context.$('connect').disabled = false;
if (context.state.authRequired === false) context.$('connect-form').requestSubmit();
setInterval(() => context.refresh(), 1500);
setInterval(() => context.watchDocuments(), 2000);
