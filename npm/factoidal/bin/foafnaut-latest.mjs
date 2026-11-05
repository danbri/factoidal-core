#!/usr/bin/env node
// foafnaut with the latest channel; see foafnaut.mjs.
import { main } from './foafnaut.mjs';
await main(process.argv.slice(2), 'latest');
