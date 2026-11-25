import { cookieSaveQueue } from "./native_cookie_save.ts";

function assert(ok: boolean, message: string) {
  if (!ok) throw new Error(message);
}

function fakeTimer() {
  let pending: (() => void) | undefined;
  return {
    delay(save: () => void) {
      if (pending) throw new Error("a save timer is already armed");
      pending = save;
      return () => {
        pending = undefined;
      };
    },
    fire() {
      if (!pending) throw new Error("no save timer is armed");
      const save = pending;
      pending = undefined;
      save();
    },
    armed: () => pending !== undefined,
  };
}

function unexpectedFailure(error: unknown) {
  throw error;
}

Deno.test("quitting waits for a timer-fired cookie save", async () => {
  const timer = fakeTimer();
  const started = Promise.withResolvers<void>();
  const finish = Promise.withResolvers<void>();
  let saved = false;
  const queue = cookieSaveQueue(
    async () => {
      started.resolve();
      await finish.promise;
      saved = true;
    },
    unexpectedFailure,
    timer.delay,
  );

  queue.schedule();
  timer.fire();
  await started.promise;
  let quit = false;
  const quitting = queue.flush().then(() => {
    quit = true;
  });
  await Promise.resolve();
  assert(!quit, "quit returned while the cookie save was still running");
  finish.resolve();
  await quitting;
  assert(saved, "quit returned before the timer-fired save completed");
});

Deno.test("a second timer waits for the first write and saves the latest jar", async () => {
  const timer = fakeTimer();
  const started = Promise.withResolvers<void>();
  const finish = Promise.withResolvers<void>();
  let jar = "first";
  const attempts: string[] = [];
  let saved = "";
  const queue = cookieSaveQueue(
    async () => {
      const snapshot = jar;
      attempts.push(snapshot);
      if (attempts.length === 1) {
        started.resolve();
        await finish.promise;
      }
      saved = snapshot;
    },
    unexpectedFailure,
    timer.delay,
  );

  queue.schedule();
  timer.fire();
  await started.promise;
  jar = "second";
  queue.schedule();
  timer.fire();
  await Promise.resolve();
  assert(attempts.length === 1, "two cookie saves started at once");
  jar = "latest";
  queue.schedule();
  assert(!timer.armed(), "the waiting save already covers the latest jar");
  finish.resolve();
  await queue.flush();
  assert(
    attempts.join(",") === "first,latest",
    `unexpected saves: ${attempts.join(",")}`,
  );
  assert(saved === "latest", "the older write replaced the latest jar");
});

Deno.test("quit drains the pending timer behind the running save", async () => {
  const timer = fakeTimer();
  const firstStarted = Promise.withResolvers<void>();
  const finishFirst = Promise.withResolvers<void>();
  const secondStarted = Promise.withResolvers<void>();
  const finishSecond = Promise.withResolvers<void>();
  let writes = 0;
  const queue = cookieSaveQueue(
    async () => {
      writes++;
      if (writes === 1) {
        firstStarted.resolve();
        await finishFirst.promise;
      } else {
        secondStarted.resolve();
        await finishSecond.promise;
      }
    },
    unexpectedFailure,
    timer.delay,
  );

  queue.schedule();
  timer.fire();
  await firstStarted.promise;
  queue.schedule();
  queue.schedule();
  let quit = false;
  const quitting = queue.flush().then(() => {
    quit = true;
  });
  await Promise.resolve();
  assert(!timer.armed(), "quit left a save timer armed");
  assert(
    writes === 1,
    "quit started the second save before the first completed",
  );
  finishFirst.resolve();
  await secondStarted.promise;
  assert(!quit, "quit returned before the scheduled save completed");
  finishSecond.resolve();
  await quitting;
  await queue.flush();
  assert(writes === 2, "quit ran extra saves");
});

Deno.test("a failed cookie save is reported and later writes still run", async () => {
  const timer = fakeTimer();
  const fail = new Error("failed to replace the jar");
  const errors: unknown[] = [];
  let attempts = 0;
  let saved = false;
  const queue = cookieSaveQueue(() => {
    if (++attempts === 1) return Promise.reject(fail);
    saved = true;
    return Promise.resolve();
  }, (error) => {
    errors.push(error);
  }, timer.delay);

  queue.schedule();
  timer.fire();
  await queue.flush();
  assert(
    errors.length === 1 && errors[0] === fail,
    "the failed write was not reported once",
  );
  queue.schedule();
  await queue.flush();
  assert(saved && attempts === 2, "the failed write blocked the next save");
  assert(errors.length === 1, "the earlier failure was reported again");
});
