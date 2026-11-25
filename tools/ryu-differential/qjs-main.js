import * as std from 'qjs:std';
import { check } from './check.js';
std.exit(check(std.loadFile(scriptArgs[1]), print) ? 1 : 0);
