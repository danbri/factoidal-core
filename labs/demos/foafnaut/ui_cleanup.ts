export type UIResources = {
  session?: { dispose(): void };
  device?: { destroy(): void };
  native?: { hide(): void };
};

// Keep cleanup independent: a failed session disposal must not leave a device
// or partially created native window alive. Preserve any original setup error.
export function cleanupUI(resources: UIResources, report: (message: string) => void = console.error): boolean {
  let success = true;
  const actions: [string, (() => void) | undefined][] = [
    ["session", resources.session && (() => resources.session!.dispose())],
    ["device", resources.device && (() => resources.device!.destroy())],
    ["window", resources.native && (() => resources.native!.hide())],
  ];
  for (const [name, action] of actions) {
    try { action?.(); }
    catch (error) { success = false; report(`UI ${name} cleanup failed: ${String(error)}`); }
  }
  return success;
}
