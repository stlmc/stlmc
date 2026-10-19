import {EditorState, EditorView, keymap, lineNumbers, highlightActiveLine,
  highlightActiveLineGutter, drawSelection, defaultKeymap, history, historyKeymap,
  insertTab, StreamLanguage, syntaxHighlighting, HighlightStyle, setDiagnostics, tags} from './codemirror.js';

// Presentation only. The STLmc parser remains the source of syntax diagnostics.
const language = StreamLanguage.define({
  token(stream) {
    if (stream.eatSpace()) return null;
    if (stream.match(/#.*/)) return 'comment';
    if (stream.match(/"(?:[^"\\]|\\.)*"/)) return 'string';
    if (stream.match(/\b(?:true|false)\b/)) return 'bool';
    if (stream.match(/\b(?:mode|flow|inv|jump|init|goal|const|common|z3|yices|dreal|cvc5)\b/)) return 'keyword';
    if (stream.match(/\b\d+(?:\.\d*)?(?:[eE][+-]?\d+)?\b/)) return 'number';
    if (stream.match(/[A-Za-z_][\w-]*/)) return 'variableName';
    stream.next(); return null;
  },
});
const colors = HighlightStyle.define([
  {tag: tags.keyword, color: '#0000ff'}, {tag: tags.comment, color: '#008000'},
  {tag: tags.string, color: '#a31515'}, {tag: tags.number, color: '#098658'},
  {tag: tags.bool, color: '#0000ff'}, {tag: tags.variableName, color: '#001080'},
]);

export function installEditor(textarea, kind) {
  const nativeValue = Object.getOwnPropertyDescriptor(HTMLTextAreaElement.prototype, 'value');
  const host = document.createElement('div'); host.className = 'stlmc-editor';
  const problems = document.createElement('div'); problems.className = 'editor-problems';
  problems.id = kind + '-problems'; problems.hidden = true;
  problems.setAttribute('aria-live', 'polite');
  textarea.after(host, problems); textarea.hidden = true;
  let view;
  const extensions = [lineNumbers(), highlightActiveLine(), highlightActiveLineGutter(),
      drawSelection(), history(), language, syntaxHighlighting(colors),
      keymap.of([...defaultKeymap, ...historyKeymap, {key: 'Tab', run: insertTab}]),
      EditorState.tabSize.of(2),
      EditorView.contentAttributes.of({'aria-label': kind === 'model' ? 'Model editor' : 'Configuration editor',
        'aria-describedby': problems.id, spellcheck: 'false'}),
      EditorView.updateListener.of(update => {
        // Parser feedback may dispatch lint effects. Do not reenter a view
        // update from its own updateListener.
        if (update.docChanged) {
          nativeValue.set.call(textarea, update.state.doc.toString());
          queueMicrotask(() => textarea.dispatchEvent(new Event('input', {bubbles: true})));
        }
      }),
    ];
  view = new EditorView({parent: host, state: EditorState.create({doc: textarea.value, extensions})});
  // Preserve the shared document/settings interfaces without a second text buffer.
  Object.defineProperty(textarea, 'value', {
    configurable: true,
    get: () => view.state.doc.toString(),
    set: value => {
      const text = String(value);
      if (text === view.state.doc.toString()) return;
      nativeValue.set.call(textarea, text);
      // File loads start a fresh undo history, so Undo cannot restore another file.
      view.setState(EditorState.create({doc: text, extensions}));
    },
  });
  return {
    resize: () => view.requestMeasure(),
    setDiagnostics(items) {
      const diagnostics = (items || []).map(item => {
        const line = view.state.doc.line(Math.max(1, Math.min(view.state.doc.lines, item.line || 1)));
        const from = Math.min(line.to, line.from + Math.max(0, (item.column || 1) - 1));
        return {from, to: Math.min(line.to, from + 1), severity: 'error', message: item.message};
      });
      view.dispatch(setDiagnostics(view.state, diagnostics));
      view.contentDOM.setAttribute('aria-invalid', String(diagnostics.length > 0));
      problems.replaceChildren(); problems.hidden = !diagnostics.length;
      diagnostics.forEach(item => {
        const button = document.createElement('button'); button.type = 'button';
        const line = view.state.doc.lineAt(item.from);
        button.textContent = `Line ${line.number}, column ${item.from - line.from + 1}: ${item.message}`;
        button.onclick = () => {view.dispatch({selection: {anchor: item.from, head: item.to}, scrollIntoView: true}); view.focus();};
        problems.append(button);
      });
    },
  };
}
