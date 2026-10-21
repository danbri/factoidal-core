// docs/web/hub-redirects.11ty.js — keep the old hub post URLs working.
//
// Until 2026-10-20 the numbered hub posts lived at /web/hub/<slug>/. They
// moved, unchanged, to /web/historical-fstar-notebooks/<slug>/ when the hub
// was rewritten for the Lean 4 engine and the npm Dataset API. This
// template writes one small page per post (docs/.eleventy.js's `hubPosts`
// collection) at the old URL. The page sends the reader to the new URL with
// a meta refresh, and also gives a plain link for a client that ignores the
// refresh. The site is static (GitHub Pages), so an HTTP redirect is not
// available.
module.exports = class {
  data() {
    return {
      pagination: { data: "collections.hubPosts", size: 1, alias: "post" },
      eleventyExcludeFromCollections: true,
      eleventyComputed: {
        permalink: (data) => `web/hub/${data.post.fileSlug}/index.html`,
      },
    };
  }

  render(data) {
    const slug = data.post.fileSlug;
    const target = this.url(`/web/historical-fstar-notebooks/${slug}/`);
    const title = String(data.post.data.title || slug)
      .replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/"/g, "&quot;");
    return `<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta http-equiv="refresh" content="0; url=${target}">
<link rel="canonical" href="${target}">
<title>Moved: ${title}</title>
</head>
<body>
<p>This notebook moved to <a href="${target}">${title}</a> in the historical F* notebooks.</p>
</body>
</html>
`;
  }
};
