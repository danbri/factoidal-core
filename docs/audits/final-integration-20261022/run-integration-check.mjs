// Local evidence runner. Not part of the package or its semantic implementation.
import { spawnSync } from 'node:child_process';
import { openSync, closeSync, existsSync, writeFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';

const [prefixArg, cwdArg, timeoutArg, command, ...args] = process.argv.slice(2);
if (!command) throw new Error('Usage: PREFIX CWD TIMEOUT_MS COMMAND [ARGS...]');
const prefix = resolve(prefixArg), cwd = resolve(cwdArg);
if (existsSync(prefix + '.log') || existsSync(prefix + '.json')) {
  throw new Error('Refusing to overwrite evidence: ' + prefix);
}
const fd = openSync(prefix + '.log', 'wx');
const started = new Date();
const identity = spawnSync('git', ['rev-parse', 'HEAD'], { cwd, encoding: 'utf8' });
const env = { ...process.env,
  PATH: dirname(process.execPath) + ':' + process.env.PATH,
  npm_config_cache: '/private/tmp/factoidal-public-pack-cache',
};
const result = spawnSync(command, args, {
  cwd, env, stdio: ['ignore', fd, fd],
  timeout: Number(timeoutArg), killSignal: 'SIGKILL',
});
closeSync(fd);
const report = {
  command: [command, ...args], cwd, node: process.version,
  source: identity.status === 0 ? identity.stdout.trim() : null,
  nodeBin: dirname(process.execPath), npmCache: env.npm_config_cache,
  started: started.toISOString(), elapsedMs: Date.now() - started,
  exit: result.status, signal: result.signal, error: result.error?.message ?? null,
};
writeFileSync(prefix + '.json', JSON.stringify(report, null, 2) + '\n', { flag: 'wx' });
console.log(JSON.stringify(report));
process.exitCode = result.status ?? 1;
