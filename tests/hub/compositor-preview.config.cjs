// Resource-bounded real Eleventy build of the app shell. Production uses the
// normal docs/.eleventy.js passthroughs; this omits unrelated historical assets.
module.exports = function(config) {
  config.ignores.add('web/historical-fstar-notebooks/**');
  for (const file of ['app.mjs','worker.mjs','pipeline.mjs','fixtures.mjs','assurance.mjs','style.css'])
    config.addPassthroughCopy(`web/hub/data-compositor/${file}`);
  for (const file of ['code-output.mjs','code-output.css'])
    config.addPassthroughCopy(`web/hub/assets/${file}`);
  config.addPassthroughCopy({'../third_party/shiki':'vendor/shiki'});
  if (process.env.COMPOSITOR_ENGINE_URL) config.addGlobalData('compositorPreviewEngineUrl', process.env.COMPOSITOR_ENGINE_URL);
  return {dir:{input:'.',includes:'_includes',data:'_data'},templateFormats:['njk'],pathPrefix:'/factoidal/'};
};
