// docs/_data/factoidalRelease.js — the published @factoidal/core release
// that the hub pages (docs/web/hub/*.md) load in the browser.
//
// A release bump is the one line `version` below. The pages in
// docs/web/hub/ set `factoidalEngine: "release"` (docs/web/hub/hub.11tydata.json),
// and docs/_includes/hub.njk then imports `browserUrl` instead of the
// same-origin copy of npm/factoidal/, and adds the CDN host to the page's
// script-src and connect-src. The package's browser.js loads its wasm from
// `l4-assets/` next to itself, so the engine bytes are the published ones.
// npm versions are immutable, so an exact version names exactly one set of
// files.
//
// The historical notebooks (docs/web/historical-fstar-notebooks/) keep the
// same-origin copy.
const version = "0.21.0";

if (!/^\d+\.\d+\.\d+$/.test(version)) {
  throw new Error(`factoidalRelease: version must be an exact x.y.z, got ${version}`);
}

const cdnHost = "https://cdn.jsdelivr.net";
const base = `${cdnHost}/npm/@factoidal/core@${version}/`;

module.exports = {
  version,
  cdnHost,
  base,
  browserUrl: `${base}browser.js`,
  npmUrl: `https://www.npmjs.com/package/@factoidal/core/v/${version}`,
};
