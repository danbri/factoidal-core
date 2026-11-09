// Data for the Web platform pages of the Hub (docs/web/hub/web-platform/ and below).
//
// foafnautPages: the title of each Foafnaut demo page, read from the demo manifest
// (labs/demos/foafnaut/pages/manifest.json), so an "Open in Foafnaut" link names the page
// as the demo index does. tools/build-demo-pages.py reads the same manifest for the feed.
//
// titleHtml and summaryHtml: the title and summary, escaped, with each styled name in a
// span whose aria-label is the plain name, as the demo page does it
// (spinal-tap-sparql.html: <span aria-label="Spinal Tap">Spın̈al Tap</span>).
const fs = require("fs");
const path = require("path");

const manifest = JSON.parse(fs.readFileSync(
  path.join(__dirname, "../../../../labs/demos/foafnaut/pages/manifest.json"), "utf8"));

// [shown, plain]: a name written in a styled form, and the name screen readers get.
const STYLED = [["Spın̈al Tap", "Spinal Tap"]];

const escape = (text) => String(text)
  .replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");

function styled(text) {
  let html = escape(text);
  for (const [shown, plain] of STYLED) {
    html = html.split(escape(shown)).join(`<span aria-label="${escape(plain)}">${escape(shown)}</span>`);
  }
  return html;
}

const foafnautPages = Object.fromEntries(
  manifest.pages.map((p) => [p.page, { title: p.title, html: styled(p.title) }]));

module.exports = {
  foafnautPages,
  eleventyComputed: {
    titleHtml: (data) => styled(data.title || ""),
    summaryHtml: (data) => (data.summary ? styled(data.summary) : ""),
  },
};
