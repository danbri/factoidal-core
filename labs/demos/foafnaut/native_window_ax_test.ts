// The window library's accessibility elements: it builds them from the engine's tree as given,
// tells the host when an accessibility client first asks, moves them with a scroll, and turns a
// press into a click at the element's centre. The tree here is written by hand in the engine's format
// (op accessibilityTree with mac: true); no engine runs.
import { libraryPath } from "./native_window.ts";

const AX_ASKED = 15, DOWN = 2, UP = 4;

function elements() {
  const lib = Deno.dlopen(libraryPath(), {
    ng_create_offscreen: { parameters: ["u32", "u32", "f64"], result: "pointer" },
    ng_next_event: { parameters: ["buffer"], result: "i32" },
    ng_pump: { parameters: [], result: "void" },
    ng_ax_wanted: { parameters: [], result: "i32" },
    ng_ax_set_tree: { parameters: ["buffer"], result: "i32" },
    ng_test_ax_dump: { parameters: [], result: "pointer" },
    ng_ax_set_view: { parameters: ["f64", "f64"], result: "void" },
    ng_test_ax_press: { parameters: ["i32"], result: "i32" },
    ng_free: { parameters: ["pointer"], result: "void" },
  });
  const s = lib.symbols, bytes = new Uint8Array(16), view = new DataView(bytes.buffer);
  const text = (value: string) => new TextEncoder().encode(value + "\0");
  const events = () => {
    const got: number[][] = [];
    while (s.ng_next_event(bytes)) got.push([view.getUint32(0, true), view.getInt32(4, true), view.getInt32(8, true)]);
    return got.filter(([kind]) => kind !== 1);
  };
  const dump = () => {
    const pointer = s.ng_test_ax_dump();
    if (!pointer) throw new Error("no dump");
    const out = new Deno.UnsafePointerView(pointer).getCString();
    s.ng_free(pointer);
    return out.split("\n").filter(Boolean).map((line) => line.split("\t"));
  };
  if (!s.ng_create_offscreen(800, 500, 2)) throw new Error("no off-screen window");
  s.ng_pump();
  // Nothing asked yet: no event, and the host has no reason to make a tree.
  if (events().length) throw new Error("an accessibility event before any client asked");
  // A malformed tree is refused and changes nothing.
  for (const bad of ["", "[]", "{\"nodes\":3}", "{"]) if (s.ng_ax_set_tree(text(bad)) !== -1) throw new Error(`took ${bad}`);
  const tree = (label: string, focused: boolean) => JSON.stringify({ top: 100, scroll: 40, nodes: [
    { id: 1073741825, depth: 0, fixed: true, box: [8, 20, 56, 56], ax: { role: "AXButton", label: "Back", press: true } },
    { id: 1, depth: 0, box: [0, 0, 1600, 2000], ax: { role: "AXWebArea", label: "Title" } },
    { id: 5, depth: 1, box: [20, 60, 400, 80], ax: { role: "AXHeading", label: "Hi", value: 2 } },
    { id: 6, depth: 2, box: [20, 60, 400, 80], ax: { role: "AXStaticText", value: "Hi" } },
    { id: 9, depth: 1, box: [20, 200, 200, 40], ax: { role: "AXButton", label, press: true, focused } },
    { id: 12, depth: 1, box: [20, 300, 40, 40], ax: { role: "AXCheckBox", subrole: "AXSwitch", label: "Dark", value: 1,
      enabled: false, press: 7 } },
    { id: 13, depth: 1, box: [20, 5000, 40, 40], ax: { role: "AXLink", label: "Far below", press: true } },
    { id: 9, depth: 1, ax: { role: "AXGroup", label: "a second entry of node 9 is left out" } },
    { depth: 9, id: 20, ax: { role: 4 } },
    "not a node",
  ] });
  if (s.ng_ax_set_tree(text(tree("Save", false))) !== 8) throw new Error("the tree was not taken");
  // The first question of a client is told to the host, once.
  const first = dump();
  dump();
  if (JSON.stringify(events()) !== JSON.stringify([[AX_ASKED, 0, 0]])) throw new Error("asking for the tree was not told once");
  if (s.ng_ax_wanted() !== 1) throw new Error("ng_ax_wanted is not set after a client asked");
  // Boxes: frame pixels to the view's points at scale 2, the page moved by top - scroll.
  const want = [
    // the chrome's node: window pixels as given, whatever the scroll
    ["0", "1073741825", "AXButton", "", "Back", "", "4,10,28,28", "1", "0"],
    ["0", "1", "AXWebArea", "", "Title", "", "0,30,800,1000", "0", "0"],
    ["1", "5", "AXHeading", "", "Hi", "2", "10,60,200,40", "0", "0"],
    ["2", "6", "AXStaticText", "", "", "Hi", "10,60,200,40", "0", "0"],
    ["1", "9", "AXButton", "", "Save", "", "10,130,100,20", "1", "0"],
    ["1", "12", "AXCheckBox", "AXSwitch", "Dark", "1", "10,180,20,20", "0", "0"],
    ["1", "13", "AXLink", "", "Far below", "", "10,2530,20,20", "1", "0"],
    // a depth with no parent at that level hangs below the last node; a role that is no text is a group
    ["2", "20", "AXGroup", "", "", "", "0,30,0,0", "0", "0"],
  ];
  if (JSON.stringify(first) !== JSON.stringify(want)) throw new Error(`elements ${JSON.stringify(first)}`);
  // A press of an assistive technology is a click at the centre of the box, in frame pixels; an
  // element that takes no press, one that is not on screen and a node that is not there refuse.
  if (s.ng_test_ax_press(9) !== 1) throw new Error("the button refused");
  if (s.ng_test_ax_press(5) !== 0 || s.ng_test_ax_press(12) !== 0 || s.ng_test_ax_press(13) !== 0 || s.ng_test_ax_press(77) !== 0)
    throw new Error("an element that takes no press took one");
  if (JSON.stringify(events()) !== JSON.stringify([[DOWN, 120, 280], [UP, 120, 280]])) throw new Error("the press was not a click at the centre");
  // A scroll with no new tree moves the elements; the far link comes on screen and takes a press.
  s.ng_ax_set_view(100, 4600);
  const scrolled = dump();
  if (scrolled[6][6] !== "10,250,20,20" || scrolled[0][6] !== "4,10,28,28") throw new Error("a scroll did not move the page's elements alone");
  if (s.ng_test_ax_press(1073741825) !== 1 || JSON.stringify(events()) !== JSON.stringify([[DOWN, 36, 48], [UP, 36, 48]]))
    throw new Error("the chrome's button refused");
  if (s.ng_test_ax_press(13) !== 1 || JSON.stringify(events()) !== JSON.stringify([[DOWN, 40, 520], [UP, 40, 520]]))
    throw new Error("the link on screen after the scroll refused");
  // The next tree: new label and the focus; a node that is gone is dropped.
  const next = JSON.stringify({ top: 100, scroll: 40, nodes: [
    { id: 1, depth: 0, box: [0, 0, 1600, 2000], ax: { role: "AXWebArea", label: "Title" } },
    { id: 9, depth: 1, box: [20, 200, 200, 40], ax: { role: "AXButton", label: "Saved", press: true, focused: true } },
  ] });
  if (s.ng_ax_set_tree(text(next)) !== 2) throw new Error("the second tree was not taken");
  const second = dump();
  if (JSON.stringify(second) !== JSON.stringify([["0", "1", "AXWebArea", "", "Title", "", "0,30,800,1000", "0", "0"],
    ["1", "9", "AXButton", "", "Saved", "", "10,130,100,20", "1", "1"]])) throw new Error(`second tree ${JSON.stringify(second)}`);
  if (s.ng_test_ax_press(13) !== 0) throw new Error("a dropped node still answers");
  if (events().length) throw new Error("an update made events");
}

if (import.meta.main) elements();
else Deno.test("the window library gives AppKit the engine's accessibility tree", async () => {
  if (Deno.build.os !== "darwin") return;
  const run = await new Deno.Command(Deno.execPath(), {
    args: ["run", "--no-check", "--no-config", "--allow-read", "--allow-ffi", "--unstable-ffi", new URL(import.meta.url).pathname],
    stdout: "piped", stderr: "piped",
  }).output();
  if (!run.success) throw new Error(new TextDecoder().decode(run.stderr));
});
