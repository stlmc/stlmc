import {build} from 'esbuild';
import {readFile} from 'node:fs/promises';
import {fileURLToPath} from 'node:url';

process.chdir(fileURLToPath(new URL('.', import.meta.url)));
const lock = JSON.parse(await readFile('package-lock.json', 'utf8'));
const notices = [];
for (const [name, info] of Object.entries(lock.packages)) {
  if (!name || info.dev) continue;
  if (info.license !== 'MIT') throw new Error('Review non-MIT editor dependency: ' + name);
  const license = await readFile(name + '/LICENSE', 'utf8');
  notices.push(name.replace('node_modules/', '') + ' ' + info.version + '\n' + license);
}
await build({absWorkingDir: process.cwd(), entryPoints: ['entry.js'], bundle: true, format: 'esm', minify: true,
  legalComments: 'eof', banner: {js: '/*!\n' + notices.join('\n\n').replaceAll('*/', '* /') + '\n*/'},
  outfile: '../../src/stlmc/ui/frontend/js/codemirror.js'});
