// Where the corpus (mlp-all-queries.json, with the Factoidal rewrites) lives:
// $MLP_CORPUS, else data/mlp-all-queries.json, else ../mlp-all-queries.json.
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const root = path.join(path.dirname(fileURLToPath(import.meta.url)), '..');
export const corpusPath = process.env.MLP_CORPUS
  || [path.join(root, 'data', 'mlp-all-queries.json'), path.join(root, '..', 'mlp-all-queries.json')].find(p => fs.existsSync(p));
