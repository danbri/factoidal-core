import {readZip} from "./zip.ts";

Deno.test("Chrome document capture keeps the photographed document and its HTTP redirect", async () => {
  const chrome = Deno.env.get("CHROME");
  if (!chrome) throw new Error("Set CHROME to the Chrome executable");
  const dir = await Deno.makeTempDir();
  const server = Deno.serve({hostname: "127.0.0.1", port: 0, onListen: () => {}}, request => {
    switch (new URL(request.url).pathname) {
      case "/news":
        if (request.headers.get("user-agent")?.includes("Chrome/")) {
          return new Response(null, {status: 302, headers: {location: "/world"}});
        }
        return new Response("<title>Domestic page</title>", {headers: {"content-type": "text/html"}});
      case "/world":
        return new Response("<title>International page</title><iframe src='/other'></iframe>",
          {headers: {"content-type": "text/html; charset=utf-8", "set-cookie": "snapshot=omit"}});
      default:
        return new Response("<title>Embedded page</title>", {headers: {"content-type": "text/html"}});
    }
  });
  try {
    const origin = `http://127.0.0.1:${server.addr.port}`;
    const pages = `${dir}/pages.json`;
    await Deno.writeTextFile(pages, JSON.stringify({
      defaults: {viewport: "800x600"},
      pages: [{id: "variant", url: `${origin}/news`, site: "fixture"}],
    }));
    const run = async (label: string, options: string[]) => {
      const out = `${dir}/${label}`;
      const result = await new Deno.Command(Deno.execPath(), {
        args: ["run", "-A", new URL("./snapshot.ts", import.meta.url).pathname,
          "--chrome", chrome, "--pages", pages, "--out", out, ...options],
      }).output();
      if (!result.success) throw new Error(new TextDecoder().decode(result.stderr));
      const file = (await Array.fromAsync(Deno.readDir(`${out}/fixture`)))[0].name;
      const files = await readZip(await Deno.readFile(`${out}/fixture/${file}`));
      const decoder = new TextDecoder();
      const manifest = JSON.parse(decoder.decode(files.get("manifest.json")));
      const starting = manifest.entries.find((entry: {url: string}) => entry.url === `${origin}/news`);
      const final = manifest.entries.find((entry: {url: string}) => entry.url === `${origin}/world`);
      return {starting, final, files, manifest, decoder};
    };
    const normal = await run("normal", []);
    if (normal.starting.source !== "deno" || normal.starting.status !== 200 ||
      !normal.decoder.decode(normal.files.get(normal.starting.body)).includes("Domestic page")) {
      throw new Error("Default replay lost the plain fetch response");
    }
    const matched = await run("matched", ["--chrome-document"]);
    if (matched.starting.source !== "chrome" || matched.starting.status !== 302 ||
      !matched.starting.headers.some(([name, value]: [string,string]) => name.toLowerCase() === "location" &&
        new URL(value, `${origin}/news`).href === `${origin}/world`) ||
      matched.manifest.reference.document_url !== `${origin}/world` ||
      matched.final.source !== "chrome" || matched.final.status !== 200 ||
      matched.final.headers.some(([name]: [string,string]) => name.toLowerCase() === "set-cookie") ||
      !matched.decoder.decode(matched.files.get(matched.final.body)).includes("International page") ||
      !matched.files.get("reference.png")?.length) {
      throw new Error("Replay document or redirect does not match the reference");
    }
  } finally {
    await server.shutdown();
    await Deno.remove(dir, {recursive: true});
  }
});
