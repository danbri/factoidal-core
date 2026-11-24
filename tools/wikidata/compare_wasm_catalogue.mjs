#!/usr/bin/env node
// Compare the shipping Wasm API with a native audit. It makes no endpoint requests.
import { readFile } from 'node:fs/promises';
import { wikidataRewrite } from '../../npm/factoidal/index.mjs';

const [catalogueFile, ...rest] = process.argv.slice(2);
if (!catalogueFile || rest.length) {
  console.error('Usage: node tools/wikidata/compare_wasm_catalogue.mjs CATALOGUE.json');
  process.exitCode = 2;
} else {
  const { queries, language } = JSON.parse(await readFile(catalogueFile, 'utf8'));
  if (!Array.isArray(queries) || !queries.length || typeof language !== 'string' ||
      !queries.every(row => typeof row.lean_rewrite_status === 'string')) {
    throw new Error('Expected a nonempty catalogue generated with --with-lean.');
  }

  let javaRewrites = 0;
  let byteIdenticalWikimediaRewrites = 0;
  const differences = [];
  for (const row of queries) {
    const actual = await wikidataRewrite(row.classic_query, { language });
    if (actual.rewrite_status !== row.lean_rewrite_status || actual.rewritten_query !== row.lean_replacement_query) {
      differences.push(row.id);
    }
    if (row.rewrite_status === 'rewritten') {
      javaRewrites += 1;
      if (actual.rewritten_query === row.replacement_query) byteIdenticalWikimediaRewrites += 1;
    }
  }
  console.log(JSON.stringify({
    queries: queries.length, language, matchingNative: queries.length - differences.length,
    javaRewrites, byteIdenticalWikimediaRewrites, differences,
  }, null, 2));
  if (differences.length) process.exitCode = 1;
}
