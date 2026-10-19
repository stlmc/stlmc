# Workspace editor bundle

The workspace uses CodeMirror 6 (MIT). `package-lock.json` pins the editor and
transitive dependencies. The self-contained `frontend/js/codemirror.js` bundle
is checked in so building Python wheels requires neither Node.js nor a CDN.

To update the bundle, use Node.js 22 or later in this directory:

```sh
npm ci --ignore-scripts
npm run build
```

Commit the lockfile and regenerated bundle together. Preserve the bundled MIT
license notices. Then run `python tools/build_ui.py` from the repository root.
