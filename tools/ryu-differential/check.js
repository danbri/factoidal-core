// Compare `HEXBITS TEXT` lines (from `leanjs numfmt-diff N SEED OUT`) with this engine's
// Number::toString. Run by ../ryu-differential.sh under Node and under QuickJS-NG.
// Issue https://github.com/danbri/factoidal-core/issues/1076.
export function check(text, log) {
  const dv = new DataView(new ArrayBuffer(8));
  let n = 0, bad = 0;
  for (const line of text.split('\n')) {
    if (line === '') continue;
    const sp = line.indexOf(' ');
    dv.setBigUint64(0, BigInt('0x' + line.slice(0, sp)));
    const x = dv.getFloat64(0);
    const want = String(x);
    const got = line.slice(sp + 1);
    n++;
    if (want !== got) { bad++; if (bad <= 20) log('DIFF ' + line.slice(0, sp) + ' engine ' + want + ' leanjs ' + got); }
  }
  log('checked ' + n + ', differences ' + bad);
  return bad;
}
