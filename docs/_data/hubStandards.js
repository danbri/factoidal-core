// docs/_data/hubStandards.js — the standards-support table of the hub
// index (docs/web/hub/index.md), built at site-build time from the newest
// scoreboard record in docs/web/hub/records/.
//
// A record is the JSON that tools/lean-scoreboard.sh writes with --json:
// one row per conformance runner, with the counts read from the runner's
// own summary line. No number on the hub index is written by hand. To
// refresh the table, run the scoreboard and commit its JSON (and the
// printed table) under docs/web/hub/records/ as
// lean-scoreboard-YYYY-MM-DD.json and .txt.
//
// The build fails when no record is found, so the table cannot silently
// disappear (anti-pattern 30 in CLAUDE.md: fail loudly on an empty walk).
const fs = require("fs");
const path = require("path");

const RECORD_DIR = path.join(__dirname, "..", "web", "hub", "records");

function score(row) {
  if (row.status !== "ok" && row.status !== "fail") {
    return { text: `not measured (${row.status})`, measured: false };
  }
  const n = (v) => (typeof v === "number" ? v : null);
  const pass = n(row.pass);
  const fail = n(row.fail);
  const other = n(row.other) || 0;
  const total = n(row.total);
  if (pass === null || fail === null || total === null) {
    return { text: row.raw_summary_line || "census, no verdicts", measured: true };
  }
  const parts = [`${pass} pass`, `${fail} fail`];
  if (other > 0) parts.push(`${other} other`);
  return { text: `${parts.join(", ")} (out of ${total})`, measured: true, clean: fail === 0 && other === 0 };
}

// The suite: the fixture path the runner was given, without the
// third_party/testing/ prefix; or the runner name when it takes none.
function suite(row) {
  const args = String(row.command || "").split(/\s+/).slice(1).filter((a) => !a.startsWith("-"));
  const fixture = args.find((a) => a.includes("/")) || "";
  const shortened = fixture.replace(/^third_party\/testing\//, "");
  return shortened ? `${row.runner}: ${shortened}` : row.runner;
}

module.exports = () => {
  const files = fs.existsSync(RECORD_DIR)
    ? fs.readdirSync(RECORD_DIR).filter((f) => /^lean-scoreboard-\d{4}-\d{2}-\d{2}\.json$/.test(f)).sort()
    : [];
  if (files.length === 0) {
    throw new Error(`hubStandards: no lean-scoreboard-YYYY-MM-DD.json record in ${RECORD_DIR}`);
  }
  const file = files[files.length - 1];
  const record = JSON.parse(fs.readFileSync(path.join(RECORD_DIR, file), "utf8"));
  const rows = (record.rows || []).map((row) => ({
    area: row.label ? `${row.spec_area} (${row.label})` : row.spec_area,
    suite: suite(row),
    note: row.note || "",
    ...score(row),
  }));
  if (rows.length === 0) throw new Error(`hubStandards: ${file} has no rows`);
  return {
    file,
    textFile: file.replace(/\.json$/, ".txt"),
    generated: record.generated_utc,
    date: String(record.generated_utc || "").slice(0, 10),
    gitHead: record.git_head,
    binaries: record.binaries_note || "",
    rows,
  };
};
