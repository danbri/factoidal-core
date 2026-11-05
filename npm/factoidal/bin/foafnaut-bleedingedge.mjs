#!/usr/bin/env node
// foafnaut with the bleeding-edge channel; see foafnaut.mjs.
import { main } from './foafnaut.mjs';
await main(process.argv.slice(2), 'bleeding-edge');
