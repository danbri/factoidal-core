import { openPreview, previewCommand } from "./preview.ts";

Deno.test("preview passes the absolute image path as one argument without a shell", () => {
  const path = "/tmp/render with spaces;$(example).ppm";
  const command = previewCommand(path);
  if (command.command !== "/usr/bin/open" || command.args.length !== 1 || command.args[0] !== path) {
    throw new Error("Unexpected preview command");
  }
});

Deno.test("disabled and non-macOS previews perform no file or process I/O", async () => {
  const unexpected = () => { throw new Error("Unexpected preview I/O"); };
  for (const [os, disabled] of [["darwin", true], ["linux", false]] as const) {
    await openPreview("render.ppm", disabled, {
      os, realPath: unexpected, execute: unexpected, warn: unexpected,
    });
  }
});

Deno.test("preview failures warn while preserving successful render status", async () => {
  for (const throws of [false, true]) {
    const warnings: string[] = [];
    await openPreview("render.ppm", false, {
      os: "darwin", realPath: () => Promise.resolve("/tmp/render.ppm"),
      execute: () => {
        if (throws) throw new Error("preview unavailable");
        return Promise.resolve({ success: false, detail: "preview unavailable" });
      },
      warn: message => warnings.push(message),
    });
    if (warnings.length !== 1 || !warnings[0].includes("Image saved") || !warnings[0].includes("preview unavailable")) {
      throw new Error("Preview failure did not produce the expected warning");
    }
  }
});
