import { readFileSync } from 'node:fs';
import { check } from './check.mjs';
process.exit(check(readFileSync(process.argv[2], 'utf8'), console.log) ? 1 : 0);
