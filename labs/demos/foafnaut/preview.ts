export type PreviewCommand = { command: "/usr/bin/open"; args: string[] };
export function previewCommand(absolutePath: string): PreviewCommand {
  if (!absolutePath.startsWith("/")) throw new Error("Preview requires an absolute file path");
  return { command: "/usr/bin/open", args: [absolutePath] };
}

type PreviewHost = {
  os: string;
  realPath: (path: string) => Promise<string>;
  execute: (command: PreviewCommand) => Promise<{ success: boolean; detail?: string }>;
  warn: (message: string) => void;
};
const defaultHost: PreviewHost = {
  os: Deno.build.os,
  realPath: path => Deno.realPath(path),
  async execute({ command, args }) {
    const result = await new Deno.Command(command, { args, stdin: "null", stdout: "null", stderr: "piped" }).output();
    return { success: result.success, detail: new TextDecoder().decode(result.stderr).trim() };
  },
  warn: message => console.warn(message),
};

// The caller invokes this only after successful GPU checks and the file write.
// Preview is convenience I/O: failure never changes a successful render result.
export async function openPreview(path: string, disabled = false, host = defaultHost): Promise<void> {
  if (disabled || host.os !== "darwin") return;
  try {
    const command = previewCommand(await host.realPath(path));
    const result = await host.execute(command);
    if (!result.success) throw new Error(result.detail || "/usr/bin/open failed");
  } catch (error) {
    host.warn(`Image saved to ${path}; preview failed: ${String(error)}`);
  }
}
