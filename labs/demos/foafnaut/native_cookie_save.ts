function delayCookieSave(save: () => void) {
  const timer = setTimeout(save, 1000);
  return () => clearTimeout(timer);
}

/** Coalesce jar changes for one second and write each snapshot in order. */
export function cookieSaveQueue(
  write: () => Promise<void>,
  onError: (error: unknown) => void,
  delay = delayCookieSave,
) {
  let cancelTimer: (() => void) | undefined;
  let queued = false;
  let tail = Promise.resolve();

  function enqueue() {
    cancelTimer = undefined;
    queued = true;
    tail = tail.then(() => {
      // A waiting write reads the latest jar when it starts.
      queued = false;
      return write();
    }).catch(onError);
  }

  return {
    schedule() {
      if (!queued) cancelTimer ??= delay(enqueue);
    },
    flush() {
      if (cancelTimer) {
        cancelTimer();
        enqueue();
      }
      return tail;
    },
  };
}
