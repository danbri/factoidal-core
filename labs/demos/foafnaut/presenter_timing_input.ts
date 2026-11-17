// Benchmark-only preload. These are scheduled test inputs, not hardware events.
// Deadlines use ng_event_clock, the same clock the host uses for input latency.
// A blocked main thread cannot move a deadline: overdue events retain their intended
// timestamps. No worker calls Cocoa or writes the unsynchronised native event queue.
const enabled = Deno.env.get("PRESENTER_TIMING_INPUT") === "1";
if (enabled) {
  const count = Number(Deno.env.get("PRESENTER_TIMING_COUNT") ?? 120);
  const period = Number(Deno.env.get("PRESENTER_TIMING_PERIOD") ?? 16);
  const delay = Number(Deno.env.get("PRESENTER_TIMING_DELAY") ?? 1500);
  if (![count, period, delay].every(Number.isSafeInteger) || count < 1 || count > 200 || period < 1 || delay < 1)
    throw new Error("Invalid presenter timing input schedule");
  let clock: (() => number) | undefined;
  let origin: number | undefined;
  let sent = 0;
  const say = console.log.bind(console);
  say(JSON.stringify({type:"presenter-timing-epoch",timeOrigin:performance.timeOrigin}));
  console.log = (...args: unknown[]) => {
    say(...args);
    if (origin !== undefined || !clock || typeof args[0] !== "string" || !args[0].startsWith("{")) return;
    let record: Record<string, unknown>;
    try { record = JSON.parse(args[0]); } catch { return; }
    if (record.type !== "native-html-presented") return;
    origin = clock() + delay;
    say(JSON.stringify({type:"presenter-timing-schedule",t:performance.now(),first:origin,count,period,delay,
      from:"scheduled-input",to:"present-return",delta:-2}));
  };
  const realDlopen = Deno.dlopen.bind(Deno);
  // Generic FFI types cannot describe replacement of one symbol in an arbitrary library.
  const runtime = Deno as unknown as {dlopen: (...args: unknown[]) => unknown};
  runtime.dlopen = (...args: unknown[]) => {
    const library = (realDlopen as (...args: unknown[]) => unknown)(...args) as {
      symbols: Record<string, (...args: unknown[]) => unknown>;
    };
    const symbols = library.symbols;
    if (!symbols.ng_next_event) return library;
    if (!symbols.ng_event_clock) throw new Error("Timing requires ng_event_clock; rebuild the native window library");
    clock = () => Number(symbols.ng_event_clock());
    const wrapped = {...symbols, ng_next_event(buffer: Uint8Array) {
      // Preserve actual resize/window events and the native queue's ordering.
      if (symbols.ng_next_event(buffer)) return 1;
      if (origin === undefined || sent >= count) return 0;
      const due = origin + sent * period;
      if (clock!() < due) return 0;
      const view = new DataView(buffer.buffer,buffer.byteOffset,buffer.byteLength);
      view.setUint32(0,11,true); view.setInt32(4,-2,true); view.setInt32(8,0,true); view.setUint32(12,due,true);
      sent++;
      say(JSON.stringify({type:"presenter-timing-input",t:performance.now(),scheduled:due,index:sent}));
      return 1;
    }};
    return new Proxy(library,{get(target,key){if(key === "symbols")return wrapped;const value=Reflect.get(target,key,target);return typeof value==="function"?value.bind(target):value;}});
  };
  globalThis.addEventListener("unload",()=>say(JSON.stringify({type:"presenter-timing-input-end",count:sent,expected:count})));
}

// When requested, add the original workload to the replayed document bytes. This only
// changes a test input; every parsing, script and rendering decision remains in the engine.
const busyURL = Deno.env.get("PRESENTER_TIMING_BUSY_URL");
if (busyURL) {
  const script = await Deno.readTextFile(new URL("./fixtures/presenter/busy.js",import.meta.url));
  const realFetch = globalThis.fetch.bind(globalThis);
  globalThis.fetch = async (input, init) => {
    const response = await realFetch(input,init);
    const url = input instanceof Request ? input.url : String(input);
    if (url !== busyURL || !response.ok || !/html/i.test(response.headers.get("content-type") ?? "")) return response;
    const text = await response.text();
    const headers = new Headers(response.headers);
    headers.delete("content-length"); headers.delete("content-encoding");
    const result = new Response(text + "\n<script>\n" + script + "\n</script>",
      {status:response.status,statusText:response.statusText,headers});
    Object.defineProperty(result,"url",{value:response.url || url});
    console.log(JSON.stringify({type:"presenter-timing-busy-input",url}));
    return result;
  };
}
