# Origin isolation: model and statement (2026-11-16)

Status: scoping. This record gives the model, the statement and the lemma plan for item 1 of the
[theorem pipeline](https://github.com/danbri/factoidal-core/issues/513). Nothing in the engine changes with it. The
generic part of the theorem (unwinding conditions give noninterference) was written as a standalone Lean file and its
check is reported under "What was checked"; everything else here is a statement to prove, not a result.

Code was read at `origin/main` `0ccd896a0` (2026-11-16). Paths are from `formal/lean4/L4Factoidal/` unless they start
with `labs/`, `tools/` or `formal/veil/`.

## The claim in one paragraph

A script of origin A cannot observe or change state that belongs to origin B: B's documents, B's storage, B's
cookies, and the answers of B's servers. The claim holds across frames, workers and navigation. It is a
noninterference theorem: take two runs of the engine that start from states which look the same to A, and in which
A's scripts make the same calls and A receives the same inputs; then the two end states look the same to A, whatever
B's documents, storage, cookies and servers held or did in each run. The same theorem read with B as the observer
gives integrity: a run in which B neither acts nor receives anything leaves B's state as it was, whatever A did.
The web platform lets some facts cross on purpose (a `postMessage`, a response that passes the CORS check, the size
of an image). Those crossings are named in one function, `released`, and the theorem is relative to it.

## 1. Prior art, and what each work proves

No earlier work proves origin isolation of a browser's own engine code. The works below prove properties of models,
of a small kernel in front of an unverified engine, or of monitors added to an engine.

**Models of the web platform**

- **[An Expressive Model for the Web Infrastructure: Definition and Application to the BrowserID SSO System](https://doi.org/10.1109/SP.2014.49)**:
  Fett, Küsters, Schmitz. IEEE S&P 2014. DOI `10.1109/SP.2014.49`. The Web Infrastructure Model (WIM): a
  Dolev-Yao style model, on paper, of browsers, servers, DNS and attackers (network, web and script attackers). The
  browser part has windows, documents, scripts as relations, cookies, web storage, `postMessage`, `XMLHttpRequest`,
  redirects, the `Origin` and `Referer` fields and HTTPS. What is proved: security properties of protocols run on
  the model (authentication and session integrity of BrowserID after fixes; later
  [OAuth 2.0](https://doi.org/10.1145/2976749.2978385), DOI `10.1145/2976749.2978385`). The proofs are manual. The
  same-origin policy is part of the model's definition of a browser; it is not a theorem about any browser code.
  Use for us: the attacker classes, and the list of browser state that a model must hold.
- **[WebSpec: Towards Machine-Checked Analysis of Browser Security Mechanisms](https://doi.org/10.1109/SP46215.2023.10179465)**:
  Veronese, Farinier, Bernardo, Tempesta, Squarcina, Maffei. IEEE S&P 2023. DOI `10.1109/SP46215.2023.10179465`.
  A browser model in Coq, with web invariants stated over traces. A compiler to SMT searches for bounded traces
  that break an invariant; a found trace is turned into a Web Platform Test and run on real browsers. It found an
  attack on the `__Host-` cookie prefix and an inconsistency in how Content Security Policy is inherited, and it
  has machine-checked Coq proofs that the proposed fixes restore the invariants in the model. What is not proved:
  anything about an implementation; the link to browsers is by generated tests. Code:
  [SecPriv/webspec](https://github.com/SecPriv/webspec) (no licence file, so read only). Use for us: the invariant
  list, and the pattern of turning a counterexample into a test.
- **[Featherweight Firefox: Formalizing the Core of a Web Browser](https://www.usenix.org/conference/webapps-10/featherweight-firefox-formalizing-core-web-browser)**:
  Bohannon, Pierce. USENIX WebApps 2010. A small-step operational model of a browser core as a reactive system:
  windows, pages as DOM trees, cookies, a script language with closures, `XMLHttpRequest`. It is a definition (also
  as an OCaml program). It proves no security theorem; the paper offers it as the base for such proofs.
- **[Reactive Noninterference](https://doi.org/10.1145/1653662.1653673)**: Bohannon, Pierce, Sjöberg, Weirich,
  Zdancewic. ACM CCS 2009. DOI `10.1145/1653662.1653673`. Defines noninterference for programs that take a stream of
  input events and give a stream of output events (the shape of a browser), in several strengths, and proves that a
  type system for a small reactive language enforces it. Use for us: the definition. Our theorem is the same idea
  with the events of an origin in place of security levels.
- **[Towards a Formal Foundation of Web Security](https://doi.org/10.1109/CSF.2010.27)**: Akhawe, Barth, Lam,
  Mitchell, Song. IEEE CSF 2010. DOI `10.1109/CSF.2010.27`. An Alloy model of browsers, servers, the network,
  origins, cookies, CORS and `Referer`, with a web attacker, a network attacker and a gadget attacker. Bounded model
  checking of five mechanisms found known and new flaws (among them in the `Origin` header proposal and in
  WebAuth). What is proved: nothing unbounded; a pass means no counterexample within the bound.
- **[Provably Sound Browser-Based Enforcement of Web Session Integrity](https://doi.org/10.1109/CSF.2014.33)**:
  Bugliesi, Calzavara, Focardi, Khan, Tempesta. IEEE CSF 2014. DOI `10.1109/CSF.2014.33`. A model in the style of
  Featherweight Firefox, and a proof that a browser-side policy gives session integrity, stated as reactive
  noninterference. A proof about a model and a policy, with an extension as the implementation.

**A verified kernel in front of an unverified engine**

- **[Establishing Browser Security Guarantees through Formal Shim Verification](https://www.usenix.org/conference/usenixsecurity12/technical-sessions/presentation/jang)**
  (Quark): Jang, Tatlock, Lerner. USENIX Security 2012. A small browser kernel written and proved in Coq. Each tab
  is an unverified WebKit process in a sandbox; all its network, cookie and screen access goes through the kernel.
  Proved, of the kernel's code: tab noninterference (no tab affects the kernel's dealings with another tab), cookie
  confidentiality and integrity by domain, and address bar integrity. What is not covered: anything inside a tab,
  so two origins in one tab (frames), the DOM, CORS and storage APIs are outside the theorems, and the sandbox is
  assumed. Code: [Conservatory/quark](https://github.com/Conservatory/quark) (GPL). Use for us: the nearest
  precedent for the shape of the theorem. Our reference monitor is the import boundary of the script engines, which
  is inside the engine and is Lean, so frames and storage are in reach.

**Information flow control added to browsers**

- **[Protecting Users by Confining JavaScript with COWL](https://www.usenix.org/conference/osdi14/technical-sessions/presentation/stefan)**:
  Stefan, Yang, Marchenko, Russo, Herman, Karp, Mazières. USENIX OSDI 2014. Labels on browsing contexts, and
  mandatory confinement of a context once it has read labelled data, built into Firefox and Chromium. The paper
  gives the design and measurements. It has no machine-checked proof of the implementations; the label model
  follows earlier proved designs. Use for us: a label for a context that depends on what it has read is the way to
  let cross-origin frames run scripts later without losing the theorem.
- **[Run-time Monitoring and Formal Analysis of Information Flows in Chromium](https://doi.org/10.14722/ndss.2015.23295)**:
  Bauer, Cai, Jia, Passaro, Stroucken, Tian. NDSS 2015. DOI `10.14722/ndss.2015.23295`. Coarse labels on pages,
  extensions, cookies, history and events in Chromium, with a formal model of the browser and a proof that the
  labelled model satisfies a noninterference property. The proof is of the model; the Chromium changes are tested.
- **[Information Flow Control in WebKit's JavaScript Bytecode](https://doi.org/10.1007/978-3-642-54792-8_9)**:
  Bichhawat, Rajani, Garg, Hammer. POST 2014. DOI `10.1007/978-3-642-54792-8_9`. And
  **[Information Flow Control for Event Handling and the DOM in Web Browsers](https://doi.org/10.1109/CSF.2015.32)**:
  Rajani, Bichhawat, Garg, Hammer. IEEE CSF 2015. DOI `10.1109/CSF.2015.32`. Fine-grained dynamic labels in WebKit's
  bytecode interpreter, then for event dispatch and the DOM, with proofs of termination-insensitive noninterference
  for formal models of the instrumented interpreter and event loop.
- **[FlowFox: a Web Browser with Flexible and Precise Information Flow Control](https://doi.org/10.1145/2382196.2382275)**:
  De Groef, Devriese, Nikiforakis, Piessens. ACM CCS 2012. DOI `10.1145/2382196.2382275`. Firefox with secure
  multi-execution: scripts run once per level, with inputs filtered. Noninterference follows from the technique's
  earlier proof; the Firefox build is tested.

**Method**

- **[Security Policies and Security Models](https://doi.org/10.1109/SP.1982.10014)**: Goguen, Meseguer. IEEE S&P
  1982. DOI `10.1109/SP.1982.10014`. Noninterference by purging the other party's events, and the unwinding method
  that reduces it to conditions on single steps.
- **[seL4: From General Purpose to a Proof of Information Flow Enforcement](https://doi.org/10.1109/SP.2013.35)**:
  Murray, Matichuk, Brassil, Gammie, Bourke, Seefried, Lewis, Gao, Klein. IEEE S&P 2013. DOI `10.1109/SP.2013.35`.
  Noninterference proved of a real system's code by unwinding, with declared channels and with timing excluded.
  The plan below has this structure: one generic theorem, and one pair of step lemmas per component.

What would be new here: the statement is about the code that runs (the Lean functions the engine is compiled
from), it covers frames and the storage and network APIs inside one page, and each crossing the platform allows
is a named Lean function that can be reviewed against the standards.

## 2. Where origin-sensitive state is today

One engine session is one top-level page. Its state is a Lean value. Every script engine (BubblePopJS, and
QuickJS-NG in BubblePopWASM) reaches the rest of the engine only through imports: the `foafnaut_dom` imports
(`WasmVM/Hosts/Dom.lean`, 25 of them, `Import.all`) and the `web_api` operations (`WasmVM/Hosts/WebApi.lean`).

| Area | Code | Proved today | Missing for the theorem |
|---|---|---|---|
| Origins, sandbox flags | `HTML/Frames.lean` | `sandboxed_no_access`, `scripts_need_allow`, `flags_inherit`, `frameFlags_narrows`, `nested_sandboxed_opaque`, `postMessage_star`, `postMessage_mismatch` | The identity of an opaque origin is `10^9 + element` per arena; two arenas can give the same number (noted in the frames record) |
| Frame documents | `WasmVM/Hosts/Dom.lean` (`frameAccessible`, `frameScriptsInRealm`, `sessionFrames`, `navigatedTo`, `writeFrameDocument`), `DomOps.lean` | `frameScriptsInRealm_sameOrigin`, `realmScripts_needs_access`, `sessionFrames_scripts`, `navigatedTo_frame`, `writeFrameDocument_needs_access` | A frame's document is grafted into the page's arena. Access is checked where a frame's document node is handed out (`node_info` 11, two places in `DomOps`). No check per operation that a node number belongs to a reachable document was found. See "Checks to make first" |
| Frame sessions, `postMessage` | `HTML/FrameSessions.lean`, `labs/demos/foafnaut/WebScripts.lean` (`pumpFrames`) | `exchange_frame`, `exchange_parent`, `exchange_isolated`, `exchange_out`, `exchange_data` (generic over the session type) | That `pumpFrames` is an instance of `exchange`; that the origin on a message is the sender's true origin (set by `Page.postToFrame`), as a theorem |
| Workers | `WasmVM/Hosts/LeanJSWorkers.lean`, `EventLoop/Agents.lean`, `Net/PageFetch.lean` (`Page.forWorker`) | `step_isolated`, `post_other` and their companions (an agent's step and posts change only the state they name), `forWorker_origin`, `workerHost_net_page`, `result_crossed`, `scriptAccepted_nosniff` | That the same-origin rule for a worker's script URL is decided in Lean and not only in `prelude.js`; no theorem that an operation of `Net.Xhr` never writes `State.page` (the workers record names it as `op_page`, not yet written) |
| Fetch, CORS, redirects | `Net/PageFetch.lean`, `Net/Xhr.lean`, `Net/FetchRules.lean` | `deliver_cross_origin_needs_cors`, `responseOf_opaque`, `deliver_noCors_opaque`, `plan_noCors_simple`, `plan_cross_unsafe_is_preflight`, `onAnswer_preflight_needs_ok`, `plan_wire_forbidden`, `plan_wire_cookie`, `preflight_no_cookie`, `redirectChain_no_cookie`, `site_same_origin`, `rawResponse_tainting`, `validate_request_keep` | The same facts in two-run form (section 5, lemma L6). That a refused answer gives the page a failure that does not depend on the answer. All need `hostCors = false` |
| Element requests | `Net/Subresource.lean` | `start_wire`, `answer_wire`, `start_mixed`, `after_style_type`, `scriptBlocked_breaker` | An opaque answer leaves the engine with a flag (`Out.done … hidden`). No theorem follows the flag to its users: canvas read-back, `cssRules`, error text of a cross-origin script |
| Web Storage | `Net/Storage.lean` | `op_partition`, `op_answer_local`, `op_noninterference`, `op_opaque` | That the origin passed is the caller's (`WebApi.run` passes the session's page origin; stated in a comment, not proved) |
| IndexedDB, caches, file system, locks, buckets, `StorageManager` | `ClientStorage/Core.lean` and the modules on it | `act_partition`, `act_answer_local`, `act_noninterference`, `act_opaque`, `actQuota_partition`, `route_origin`, `opFor_noninterference`, `op_local`, and one partition theorem per API | The same caller-origin glue as Web Storage |
| Cookies | `Net/Cookies.lean`, `ClientStorage/CookieStore.lean` | `visible_host`, `visible_not_httpOnly`, `visible_secure`, `set_keeps_host`, `setFromHeader_keeps_host`, `sent_host`, `sent_cross_site`, `storeCookies_needs_credentials` | Two-run form. Whether a bound on the jar lets one host's cookies push out another's |
| Blob URLs | `Net/BlobUrls.lean` | `resolve_origin`, `revoke_other`, `add_other`, `add_bounds` | The bounds (`maxEntries`, `maxHeld`) are per session, not per origin |
| History, navigation | `HTML/SessionHistory.lean`, `Dom.navigatedTo`, `labs/demos/foafnaut/WebHistory.lean`, `WebRoute.lean` | `canRewrite_origin`, `traverse_entries`, `navigatedTo_frame` | A top-level navigation starts a new session with no engine state carried over; this is how the hosts are written, not a theorem. `window.name` and `:visited` need a check |
| Referrer, fetch metadata, CSP, secure contexts | `Net/ReferrerPolicy.lean`, `Net/CspPolicy.lean`, `Net/SecureContext.lean` | `determine_no_credentials`, `strict_cross_origin_no_path`, `determine_chain`, `plan_wire_referer`, `blocksRequest_append` | None for the theorem; they bound what a request tells another origin's server |
| Addresses | `Net/Egress.lean`, `Net/PageFetch.lean` | `egress_refuses_special`, `mayConnect_local_needs_local_page`, `emit_reach`, `onAnswer_resolve_special` | None; they are the network part of the assumptions |
| Host boundary | `HostContract/Model.lean`, `HostContract/Trace.lean` (issue [458](https://github.com/danbri/factoidal-core/issues/458), pull request [459](https://github.com/danbri/factoidal-core/pull/459)) | `violations_nil_iff`, `refused_without_cap`, `recorded_disagreements_nil` under assumptions A1 to A5 | `relaxFields` lists `hostCors`, `address`, `network`, `navigations`, `liberal`, `scripting`: the theorem must say which a target may set. A host assumption that each answer goes to the wire it answers |
| System models | `formal/veil/FoafnautModels/` (issue [498](https://github.com/danbri/factoidal-core/issues/498)) | `HttpConnections`: a connection is used for one origin, partition and address, and a response goes to the request that owns it; `Glue.lean`: per-page event loops composed with a component theorem | No model with origins as labels yet |

What follows from this inventory:

1. **Between top-level pages there is no shared engine state today.** Storage, cookies and blob URLs are in memory
   for one session. Isolation between two tabs is then a host assumption (the host gives each session only its own
   bytes) and nothing more. The storage partition theorems start to carry weight when storage persists.
2. **Inside one page, origin B's state is present in four forms**: the document of a cross-origin frame (in the
   page's arena, with no script of its own); a sandboxed frame's session (opaque origin, own heap and arena); the
   answers of B's servers to the page's requests; and cookies of B's host set by credentialed requests.
3. **A same-origin frame shares the page's realm, and a worker has its owner's origin.** Both are inside one
   origin, so they need no isolation, only a correct label.
4. **Decisions written in `prelude.js` are not part of the trusted base.** The prelude runs in the page's realm
   with the page's scripts. The model below treats the whole realm as the attacker's, so a rule counts only when a
   Lean import enforces it.
5. **Heap isolation between sessions needs no memory-safety assumption.** A session is a Lean value and the script
   engines are pure Lean functions on it ([safety map](2026-11-13-foafnaut-safety-map.md)): one session cannot
   name another session's heap. This is the part other browsers get from process boundaries.

## 3. The model

Lean-style pseudocode. Names follow the code where code exists.

```lean
namespace L4Factoidal.Isolation
open HTML.Frames (Origin)          -- tuple (scheme, host, port) | opaque id

/-- Something that runs script. Its origin is fixed for its life and is given by the engine. -/
inductive AgentKind | pageRealm | frameSession (el : Nat) | worker (id : Nat)

structure Agent where
  kind   : AgentKind
  origin : Origin        -- Dom.pageOrigin; a fresh opaque origin (Frames.frameOf); the owner's (forWorker_origin)
  heap   : Heap          -- JavaScript heap, event loop, timers. Private. Wholly under the script's control
  inbox  : List Message  -- delivered, not yet read

structure Doc where
  root    : Nat          -- its document node
  origin  : Origin       -- Dom.docFrame
  url     : String
  history : SessionHistory.History

structure State where
  agents    : List Agent
  dom       : Arena                          -- nodes; each node names its document (`.doc`)
  docs      : List Doc                       -- the page's document and every frame's
  frames    : List (Nat × Frames.Frame × Nat) -- iframe element, frame record, document
  areas     : Net.Storage.Store              -- by (origin, kind)
  sheds     : ClientStorage.Sheds            -- IndexedDB, caches, files, locks, buckets: by storage key
  jar       : Cookies.Jar                    -- by host
  blobs     : BlobUrls.Store                 -- by the origin that made each URL
  transfers : List (AgentId × PageFetch.Transfer)  -- requests in flight, with the agent that made each
  outbox    : List Message                   -- posted, not yet delivered
  host      : HostFacts                      -- viewport, clock, entropy, settings
```

**Labels.** Every part of the state has an owner. An agent: its origin. A node: the origin of its document. A
storage area or shelf: the origin of its key. A blob URL: the origin that made it. A transfer: the origin of the
agent that made it. A cookie: its host (cookies do not know ports or schemes, as the standard has it; the theorem
says nothing between two origins of one host). A message in the outbox: its sender. `host` facts are public.

**The view of an origin.** `view o s` is `s` with everything not owned by `o` removed:

```lean
def view (o : Origin) (s : State) : View :=
  { agents    := s.agents.filter (·.origin = o)                 -- whole heaps and inboxes
    nodes     := s.dom.restrict (fun n => (docOf s n).origin = o)
    frames    := for each iframe element in such a document: Dom.frameBits (reachable, scripts, forms)
                 and whether it has loaded; never its document
    areas     := fun k => if k.origin = o then s.areas.area k else default
    sheds     := the same, by storage key
    cookies   := s.jar.filter (·.host = hostOf o)
    blobs     := s.blobs.filter (·.origin = o)
    transfers := the transfers of o's agents, each without answer bytes not yet released
    outbox    := s.outbox.filter (senderOrigin · = o)
    host      := s.host }
```

`s₁ ≈[o] s₂` means `view o s₁ = view o s₂` (low equivalence for `o`).

**Events.** Each event carries the origin it acts for. A step is enabled only when that origin is the true one;
the engine supplies it, and no import takes an origin from script.

```lean
inductive Event
  | call    (a : AgentId) (o : Origin) (imp : Import) (args : Args)
      -- an agent makes one import call: any `foafnaut_dom` import or `web_api` operation, any arguments
  | answer  (t : TransferId) (o : Origin) (ans : PageFetch.Answer)
      -- the host gives the network's answer to a wire of transfer `t`, made by an agent of origin `o`
  | deliver (m : Message) (o : Origin)
      -- the engine moves a posted message to the inbox of its target, of origin `o`
  | host    (i : HostInput)
      -- input at a node, a clock reading for an agent, a resize, entropy, the bytes of a frame navigation,
      -- a top-level navigation
  | sched   (a : AgentId) (o : Origin)
      -- the engine lets an agent run a task
```

The attacker's script is not modelled as a program. An agent of origin A may make **any** sequence of import
calls. This covers every script, a changed prelude, and any error in the JavaScript engines that stays inside the
realm's own heap.

**What an origin sees of an event.**

```lean
def vis (o : Origin) : Event → Option Vis
  | .call a o' imp args => if o' = o then some (.call a imp args) else none
  | .answer t o' ans    => if o' = o then some (.answer t (released t ans)) else none
  | .deliver m o'       => if o' = o then some (.deliver m) else none
  | .host i             => (i.partFor o).map .host    -- input at o's nodes, o's clock readings, public facts
  | .sched a o'         => if o' = o then some (.sched a) else none

def purge (o : Origin) (es : List Event) : List Vis := es.filterMap (vis o)
```

**The crossings the platform allows** are in `released` and in `HostInput.partFor`. They are the security policy,
and they are what a reviewer reads against the standards:

```lean
def released (t : Transfer) (ans : Answer) : Released :=
  if t.same then .all ans                        -- same origin
  else if isRedirect ans then .redirect           -- only that it happened, and only in redirect mode "manual"
  else if t.noCors then .opaque (public ans)      -- D2, D3 below
  else if corsOk t ans then .cors (exposed t ans) -- status, the CORS-exposed fields, the body
  else .failed                                    -- one failure, with nothing of `ans` in it
```

- D1. A message another origin posted to `o` (`deliver`): its data and the sender's true origin.
- D2. For an element request in mode "no-cors": that it succeeded or failed, and for an image its size.
- D3. A cross-origin classic script or style sheet that passes `Subresource.typeOk`: running or applying it in
  the embedding realm releases what it does there. This is the platform's rule, not a choice of ours.
- D4. For a frame of another origin: that it exists, its `frameBits`, and that its document loaded.
- D5. Public host facts: viewport, settings.

**Steps and runs.** `step : State → Event → State → Prop` is the engine: `call` is `Hosts.Dom.call` and
`WebApi.run` on the agent's session; `answer` is `PageFetch.onAnswer` (with `Net.Xhr` and `Net.Subresource`);
`deliver` and `sched` are `FrameSessions.exchange` and `EventLoop.Agents.step`; `host` is the document operations
of `labs/demos/foafnaut/WebDocument.lean` and `WebScripts.lean`. `Run s es s'` is the closure. `Inv s` says the
state is well formed: every node's document is listed, every frame record narrows its container's
(`SandboxFlags.Narrows`), opaque origins are distinct, tables are within their bounds.

## 4. The statement

```lean
/-- Origin isolation. Two runs from well-formed states that look the same to `o`, in which `o` makes the same
calls and receives the same inputs in the same order, end in states that look the same to `o`. -/
theorem origin_isolation (o : Origin)
    (r₁ : Run s₁ es₁ s₁') (r₂ : Run s₂ es₂ s₂')
    (hi₁ : Inv s₁) (hi₂ : Inv s₂) (hn₁ : NativePolicy s₁) (hn₂ : NativePolicy s₂)
    (hview : s₁ ≈[o] s₂)
    (hin : purge o es₁ = purge o es₂) :
    s₁' ≈[o] s₂'

/-- Confidentiality, read from it with o := A: every answer A's calls get is in A's heaps, which are in A's
view. So nothing A's scripts compute depends on B's documents, storage, cookies or unreleased answers. -/

/-- Integrity, with o := B: a run in which B makes no call and receives nothing leaves B's view as it was. -/
theorem origin_integrity (o : Origin) (r : Run s es s') (hi : Inv s) (hn : NativePolicy s)
    (hquiet : purge o es = []) : s' ≈[o] s

/-- What A can make B's server see (the server is outside the model). Every wire sent for an agent of origin A
to a URL of another origin is: a simple request in mode "no-cors"; or a CORS preflight, with no cookie; or a
request that an earlier preflight of the same transfer allowed. Cookies go with it only as `SameSite` and the
credentials mode allow. -/
theorem cross_origin_wires (h : step s (.call a A imp args) s') (w : Wire) (hw : w ∈ wiresOf s' \ wiresOf s)
    (hx : ¬ sameOrigin (originOfUrl w.url) A) : AllowedCrossWire s a w
```

`origin_isolation` and `origin_integrity` follow from two conditions on single steps, by a generic theorem that
does not mention browsers:

```lean
structure Unwinding (S : Sys State Event) (O : Observer State Event View Vis) : Prop where
  local_respect   : ∀ s e s', S.inv s → S.step s e s' → O.vis e = none → O.view s' = O.view s
  step_consistent : ∀ s₁ s₂ e₁ e₂ s₁' s₂', S.inv s₁ → S.inv s₂ → O.view s₁ = O.view s₂ →
      S.step s₁ e₁ s₁' → S.step s₂ e₂ s₂' → O.vis e₁ = O.vis e₂ → O.vis e₁ ≠ none →
      O.view s₁' = O.view s₂'

theorem noninterference (h : Unwinding S O) :
    S.Run s₁ es₁ s₁' → S.Run s₂ es₂ s₂' → S.inv s₁ → S.inv s₂ →
    O.view s₁ = O.view s₂ → O.purge es₁ = O.purge es₂ → O.view s₁' = O.view s₂'
theorem run_invisible (h : Unwinding S O) :
    S.Run s es s' → S.inv s → O.purge es = [] → O.view s' = O.view s
```

So the work is: for each kind of event and each part of the state, prove local respect (an event of another
origin does not change my view) and step consistency (my event does the same thing in two states I cannot tell
apart). Section 5 lists these.

### Assumptions

- **H1, the host.** Assumptions A3 to A5 of `HostContract/Trace.lean`: the builds compute the Lean functions; the
  host calls from one thread, passes answers on unaltered and does not end the engine mid-call. Added here, **A6**:
  the host gives each answer to the wire it answers (by `id`), gives a session only its own bytes, and states the
  page's URL and address truthfully. A6 can be tested by the trace checker; it cannot be proved in Lean.
- **H2, no relaxation.** `NativePolicy`: `hostCors = false`, and none of the `relaxFields` of the host contract is
  set. On the Hub `hostCors` is true and the CORS check is the outer browser's; there the theorem holds only with
  the outer browser's check as a further assumption.
- **N1, the network.** The attacker may run any server, at any origin but the victim's, and may answer DNS in any
  way (`Egress.choose` pins the address). TLS is the host's and is trusted. An origin with scheme `http` is the
  network attacker's: the theorem makes no claim for it against an attacker on the path.
- **T1, time.** A clock reading is an input of the agent that reads it. The theorem says nothing about how long
  anything takes. A later, stronger form bounds the channel: `Page.ScriptClock` counts interpreter steps, so a
  clock that only that agent's steps move is within reach.
- **T2, progress and shared bounds.** The theorem does not say that an origin gets to run. It is first stated with
  per-session tables treated as unbounded (transfers `maxLive`, blob URLs `maxEntries`, cookie jar, address pins);
  lemma L10 then removes this, table by table.
- **T3, hardware.** One process holds all origins of a page. The theorem is about the Lean semantics. It makes no
  claim against attacks that read memory through speculative execution. Page scripts are interpreted, not compiled
  to native code; this must be looked at again when a native tier arrives (pipeline item 3).
- **D, declared crossings.** D1 to D5 above. The theorem is relative to `released` and `partFor` as written.
- **Scope today.** Cross-origin frames run no script unless they are sandboxed `srcdoc` frames with a session of
  their own. When cross-origin frames get sessions, the model needs no change: they are agents with their origin.

### Checks to make first

These came out of the inventory. Each is a question with a cheap test; none is a confirmed fault.

- C1. **Node numbers of a cross-origin frame's document.** The frame's document is in the page's arena, and a
  script names nodes by number. Under the model's attacker (any import call, any argument), does any
  `foafnaut_dom` import read or write a node of a document that `frameAccessible` refuses? Test: a page with a
  cross-origin frame; from a script, call the imports directly with node numbers above the page's own.
- C2. **Canvas read-back.** No origin-clean flag was found by text search in `PageCanvas/` or in the prelude's
  `getImageData`. If an opaque image can be drawn to a canvas, can its pixels be read?
  Result (issue 524): yes, and more. A canvas that drew another origin's image answered its pixels to
  `getImageData`, `toDataURL`, `toBlob`, `convertToBlob`, through other canvases, patterns, `ImageBitmap`s and
  `OffscreenCanvas`, and to WebGL `texImage2D` (whose prelude reads the pixels back). Separately, an image
  element's request put the image's bytes, of any origin, into the page's realm (the prelude read the natural
  size from them), where a page that replaced `Uint8Array` read them. Fixed in the engine: `PageCanvas.Taint`
  (origin-clean flags of canvases, bitmaps and patterns, kept by `Run.stepT`), `Store.refuses` and the refusals of
  `Wire.call` and `Wire.callWords` (the prelude maps them to `SecurityError`), `Net.PageFetch.Page.imageClean`
  (an image is clean when `data:` or of the page's origin), the record of opaque answers to same-origin image
  URLs (a redirect to another origin) in the lab's `Engine.subresource`, and `Net.Xhr.imageRaw` (an image
  element's request gives the realm the natural size, never the bytes). Theorems in `PageCanvas/Theorems.lean`
  (section 3) and `Net.Xhr.imageRaw_noninterference`; the checks C2, C2b, C2c and C2d of
  `origin_isolation_test.ts` must pass. Still open: the bytes of a classic script of another origin reach the
  realm the same way (`Xhr.raw` for destination `script`), and a `VideoFrame`'s pixels come from the media host
  into the realm with no origin-clean flag.
- C3. **Failure text.** Does the failure a page gets for a refused cross-origin answer carry anything of the
  answer (a status, a field)?
- C4. **Rules only in `prelude.js`.** The same-origin test for `new Worker(url)` and the refusal of
  `document.domain` are in the prelude. Is each also enforced by a Lean import?
- C5. `window.name` across a navigation, and what `getComputedStyle` answers for a `:visited` link.

- C1b (2026-11-16). **A nested frame's URL.** A frame's `src` was parsed against the page's URL, not
  against its own node document (HTML §4.8.5), so a frame inside another origin's frame document asked
  the embedder for a document of the page's origin, which then ran in the page's realm and could walk
  the other origin's frame nodes. Fixed by `Hosts.Dom.frameBase` (pull request
  [549](https://github.com/danbri/factoidal-core/pull/549)); `origin_isolation_test.ts` C1b.
- C6 (2026-11-16). **Classic scripts of another origin.** Their bytes reached the page's realm (the
  prelude decoded them). Fixed by `Net.Xhr.scriptRaw` and `takeScript` and the native `runFetched`
  (pull request [547](https://github.com/danbri/factoidal-core/pull/547)); errors are muted.

### Follow-up: network for a cross-origin frame's own session

A frame of another origin whose scripts may run gets a script session of its own
(`WebScripts.crossFrameSessions`), started with `network := false` and `hostLoads := false`: nothing
in the embedder answers that session's requests or loads its frames. So such a frame cannot fetch,
make an `XMLHttpRequest`, load a nested frame or post to a server. WPT shows it:
`html/semantics/embedded-content/the-iframe-element/cross_origin_parentage.sub.html` subtest 2 needs
the grandchild (in a frame of another origin) to post to `stash.py`. Before pull request 529 that
subtest passed only by the C1b fault (the grandchild ran in the page's realm).

What the work needs:

1. A `Net.Xhr.State` per frame session, with that frame's `PageFetch.Page` (its origin, address and
   secure flag; `Page.forFrame`, as `Page.forWorker`), its own cookie jar view (the same jar, by
   host) and its own `held` bound.
2. The turn's `netRequests` and `navigations` tagged with the session they belong to (a frame's
   iframe element number), and the embedder's answers routed back by that tag (`action net` and
   `action frame` with a `frame` field). The routing is engine state, so a theorem can say that an
   answer reaches only the session that asked (`HTML.FrameSessions.exchange` extended by network
   events; the `HttpConnections` Veil model already states this for connections).
3. Limits: a bound on the number of frame sessions with network (today `maxFrameSessions`), on
   requests in flight per session, and the nesting depth of frames.
4. Theorems: a frame session's requests carry its own origin (`Page.forFrame_origin`), and an
   operation of one session's `Net.Xhr` state never changes another's (`op_page` of the workers
   record, generalised to sessions).
5. Checks: a new origin isolation check that a cross-origin frame's fetch has its own origin in the
   `Origin` field and that its answer never appears in the page's realm; the WPT subtest above as the
   end-to-end test.

Cost: about 6 to 10 hours of agent time and one cloud build; the page pays nothing while it has no
cross-origin frame with scripts.

## 5. Lemmas, by module, ranked by cost

Rows are in order of cost, cheapest first. Cost is agent time (wall clock of one agent), plus Lean build waits
where stated. "Have" lists theorems that already carry most of the proof.

| # | Lemma | Module | Have | Cost |
|---|---|---|---|---|
| L0 | `noninterference`, `run_invisible`: unwinding gives the theorem (generic) | new `Isolation/Unwinding.lean` | Written standalone (see "What was checked") | 0.5 h to add to the tree |
| L1 | Blob URLs: local respect and step consistency | `Net/BlobUrls` | `resolve_origin`, `revoke_other`, `add_other` | 1 h |
| L2 | Storage: the same pair for Web Storage and every `ClientStorage` API, and `WebApi.run` passes the agent's origin as the key | `Net/Storage`, `ClientStorage/*`, `WasmVM/Hosts/WebApi` | `op_partition`, `op_answer_local`, `act_partition`, `act_answer_local`, `route_origin`, one partition theorem per API | 2 to 3 h |
| L3 | Workers: a worker's label is its owner's origin; its steps touch its own state; its script URL is checked in Lean | `Hosts/LeanJSWorkers`, `EventLoop/Agents`, `Net/PageFetch` | `step_isolated`, `post_other`, `forWorker_origin`, `workerHost_net_page`, `result_crossed` | 2 to 3 h |
| L4 | `cross_origin_wires` | `Net/PageFetch`, `Net/Cookies` | `plan_noCors_simple`, `plan_cross_unsafe_is_preflight`, `plan_wire_cookie`, `preflight_no_cookie`, `sent_cross_site`, `plan_wire_forbidden` | 2 to 3 h |
| L5 | Host contract: assumption A6 as a checked property of traces (answer ids match wires; no session sees another's id); `NativePolicy` from `relaxFields` | `HostContract/Model`, `HostContract/Trace` | `violations_nil_iff`, `refused_without_cap` | 2 to 3 h |
| L6 | **Fetch release.** Two answers with the same `released t` give the page the same response and leave the transfer the same in the page's view; a refused answer gives `.failed` with nothing of the answer | `Net/PageFetch` (`onAnswer`, `responseOf`, `corsOk`) | `deliver_cross_origin_needs_cors`, `deliver_noCors_opaque`, `responseOf_opaque`, `onAnswer_preflight_needs_ok`, `onAnswer_redirect_error` | 3 to 5 h |
| L7 | Cookies: what `document.cookie` and the Cookie Store answer depends only on the cookies of the page's host; a `Set-Cookie` for host B changes no cookie of host A | `Net/Cookies`, `ClientStorage/CookieStore` | `visible_host`, `set_keeps_host`, `setFromHeader_keeps_host`, `sent_host` | 3 to 4 h |
| L8 | Navigation and history: `navigatedTo` relabels only the frame it names; `pushState` keeps the origin; a top-level navigation gives a state whose view is empty for every origin but the new page's | `HTML/SessionHistory`, `Hosts/Dom`, lab `WebHistory`, `WebRoute` | `canRewrite_origin`, `navigatedTo_frame`, `traverse_entries` | 3 to 5 h |
| L9 | A Veil module with origins as labels: agents, messages and transfers as a transition system, with the component lemmas as glue; model-checked on a small instance | `formal/veil/FoafnautModels/` | the `Glue.lean` pattern, `HttpConnections` | 3 to 4 h |
| L10 | Shared bounds: each per-session table is bounded per origin, or its bound cannot be seen from another origin | `Net/Xhr`, `Net/Subresource`, `Net/BlobUrls`, `Net/Cookies`, `ClientStorage/Budget` | `actQuota_partition`, `add_bounds`, `notePin_bounded` | 3 to 4 h to list, then 1 to 2 h a table |
| L11 | Messages: `pumpFrames` is `exchange`; the origin on a delivered message is the sender's; delivery obeys `postMessageDelivers` | `HTML/FrameSessions`, `HTML/Frames`, `labs/demos/foafnaut/WebScripts.lean`, `Hosts/Page` (`postToFrame`) | `exchange_isolated`, `exchange_out`, `exchange_data`, `postMessage_mismatch` | 4 to 6 h |
| L12 | `Net.Xhr.op` and `fetch`: no operation changes `State.page`; each transfer is made with the agent's own `Page` | `Net/Xhr` | `rawResponse_tainting`, `ownUrl_same`, `blobOf_own` | 4 to 6 h |
| L13 | Element requests: an opaque answer (`hidden`) reaches no import that returns bytes to script; the declared crossings D2 and D3 are all that is released | `Net/Subresource`, `PageCanvas/`, style and script loading in the lab | `after_style_type`, `scriptBlocked_breaker` | 6 to 10 h, plus an engine fix if check C2 finds one |
| L14 | **DOM confinement.** Every `foafnaut_dom` import, with any arguments, reads and writes only nodes of documents the calling agent may reach, plus the declared frame facts (D4) | `WasmVM/Hosts/Dom` (`call`), `DomOps`, `Page` | `frameAccessible` and its theorems, `call_writes_within`, `call_store` | 6 to 10 h for a guard at the entry of `call` with its theorem; 15 to 25 h for a footprint proof of every operation |
| L15 | Composition: `Unwinding` for the whole `step`, from the rows above; then `origin_isolation` by L0 | new `Isolation/Model.lean`, `Isolation/Theorem.lean` | all of the above | 8 to 12 h |

Total: about 55 to 100 hours of agent time, in pieces that can run in parallel after L0, plus three or four
cloud builds (about 1.5 h each). The order of value is not the order of cost: L14 and L13 are the two where the
inventory suggests the engine may have to change, so their checks (C1, C2) come first.

Performance: every guard added must cost nothing for a page with no frame. For L14 the guard is one test of
`s.frames.isEmpty` on that path. Each lemma hand-back gives render timings before and after.

## 6. First steps

1. **Checks C1 to C5** as tests that fail or pass today, with an issue for each that fails (about 2 h in all,
   no Lean build: they run against a release engine).
2. **Lemma L6, Fetch release** (3 to 5 h of agent time, one module build of `Net/PageFetch` under the build lock,
   then one cloud build). Define `released` next to `onAnswer`. Prove
   `onAnswer_released : released t a₁ = released t a₂ → pageSide (onAnswer t a₁) = pageSide (onAnswer t a₂)` for
   a transfer in the main phase with `hostCors = false`, and the same for the preflight phase. The existing
   theorems give each branch; the new work is the single two-run statement and the review of `released` against
   the Fetch Standard. This is the lemma "Fetch delivers a cross-origin response body to a script only if CORS
   passes" in the form the theorem needs.
3. **Lemma L14, DOM confinement, first cut** (6 to 10 h, one cloud build). After C1: add to `Hosts.Dom.call` one
   test that each node argument belongs to a reachable document (skipped when the session has no frame), and prove
   `call_confined : ∀ imp args, nodesTouched (call imp args s) ⊆ reachable s`. This is the lemma "a frame's DOM
   operations only touch its own document", stated for the page's realm and for each frame session.
4. L0 goes into the tree with the first of these (it has no imports).

Each of these gets its own issue when work starts, linked from the pipeline table, as the pipeline asks.

## What was checked

- The generic theorem of section 4 (`Unwinding`, `run_invisible`, `noninterference`, with an invariant kept by
  steps) is a standalone Lean file with no imports, not yet in the tree (its text is in the issue for this item).
  `lean` v4.33.1 accepts it with no error and no `sorry`; `#print axioms noninterference` gives `propext` and
  `Quot.sound` only. One linter warning (an unused simp argument).
- Every DOI above was resolved against Crossref on 2026-11-16 and its title and authors compared.
- Theorem names in section 2 were read from the source at `0ccd896a0`. Their statements were read for
  `Net/PageFetch` (CORS and opaque responses), `Net/Storage`, `HTML/FrameSessions` and `HTML/Frames`; for the other
  modules the names and their comments were read, not the proofs.
- Nothing was built or run against the engine. C1 to C5 are questions, not findings.
