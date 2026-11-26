// deno test labs/demos/foafnaut/tor-wasm/deno/ip-literal.test.ts
import { isIpLiteral } from "./ip-literal.ts";
const yes = ["127.0.0.1", "0.0.0.0", "255.255.255.255", "171.25.193.9", "::1", "2a00:da00:f460:1100::1",
  "::ffff:1.2.3.4", "FE80::1", "1:2:3:4:5:6:7:8"];
const no = ["", "localhost", "example.org", "a:b", ":::", "1:2:3:4:5:6:7:8:9", "256.1.1.1", "01.2.3.4",
  "1.2.3", "1.2.3.4.5", "1.2.3.04", "fe80::1%eth0", "[::1]", " 127.0.0.1", "127.0.0.1 ", "0x7f.0.0.1",
  "2130706433", "1.2.3.4:80", "::g"];
Deno.test("IP literals accepted", () => {
  for (const s of yes) if (!isIpLiteral(s)) throw new Error(`refused ${JSON.stringify(s)}`);
});
Deno.test("everything else refused (no name ever reaches a resolver)", () => {
  for (const s of no) if (isIpLiteral(s)) throw new Error(`accepted ${JSON.stringify(s)}`);
});
