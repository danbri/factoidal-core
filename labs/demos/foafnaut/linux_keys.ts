// SDL_Keycode is a Unicode character or an SDL scancode with bit 30 set.
// These named keys carry the virtual codes the existing shell edit ABI takes.
// Shortcut commands come from the engine's keyCommand("other", ...) operation.
const scan = (code:number) => 0x40000000 | code;
const named = new Map<number,[string, number]>([
  [8,["Backspace",51]], [9,["Tab",48]], [13,["Enter",36]], [27,["Escape",53]],
  [32,[" ",49]], [127,["Delete",117]], [scan(88),["Enter",76]], [scan(73),["Insert",114]],
  [scan(74),["Home",115]], [scan(75),["PageUp",116]], [scan(77),["End",119]],
  [scan(78),["PageDown",121]], [scan(79),["ArrowRight",124]], [scan(80),["ArrowLeft",123]],
  [scan(81),["ArrowDown",125]], [scan(82),["ArrowUp",126]],
]);
for (const [i, code] of [122,120,99,118,96,97,98,100,101,109,103,111].entries()) {
  named.set(scan(58 + i), [`F${i+1}`, code]);
}
export function linuxKey(symbol:number) {
  const special = named.get(symbol);
  if (special) return {key:special[0], code:special[1]};
  // Printable text arrives separately from SDL_TEXTINPUT after composition.
  // R also has a legacy virtual code in the desktop host's single-key reload.
  if (symbol >= 32 && symbol <= 0x10ffff) return {key:String.fromCodePoint(symbol), code:symbol===114?15:255};
  return {key:"Unidentified", code:255};
}
export function linuxModifier(bits:number) {
  return [bits&1?"shift":"", bits&8?"control":"", bits&4?"alt":"", bits&2?"command":""].filter(Boolean).join("+");
}
