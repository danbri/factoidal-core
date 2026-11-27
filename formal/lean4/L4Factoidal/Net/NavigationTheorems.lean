/-
L4Factoidal.Net.NavigationTheorems — Tor mode for the loads of a document that page scripts do
not make: the top-level navigation with its redirects (`Net.Navigation`) and the requests of a
document's elements (`Net.Subresource`). Issue https://github.com/danbri/factoidal-core/issues/1060;
record: section 21a of `docs/designissues/2026-11-25-foafnaut-tor-onion-routing.md`.

Every theorem is over the engine's answer to the host. None says that the host obeys the wire
(that it sends a `tor` wire through its Tor client and resolves nothing): that is host glue,
tested, not proved.
-/
import L4Factoidal.Net.Navigation
import L4Factoidal.Net.Subresource

namespace L4Factoidal.Net.NavigationTheorems
open L4Factoidal.WHATWG
open L4Factoidal.Net.PageFetch

/-! ## `PageFetch`: a step keeps the transfer's page -/

/-- Kind: lemma. Says: a request that `onAnswer` tells the host to make belongs to a transfer
with the same page. -/
theorem onAnswer_page (t t' : Transfer) (a : Answer) (w : Wire) (h : onAnswer t a = .send t' w) :
    t'.page = t.page := by
  unfold onAnswer at h
  split at h
  · split at h
    · exact (plan_send_allowed _ _ _ h).2.2.2
    · split at h
      · exact (plan_send_allowed _ _ _ h).2.2.2
      · simp at h
  · split at h
    · simp at h
    · split at h
      · exact (emit_reach h).2
      · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · split at h
            · simp at h
            · split at h
              · simp at h
              · split at h
                · simp at h
                · split at h
                  · simp at h
                  · split at h
                    · simp at h
                    · split at h
                      · simp at h
                      · exact (plan_send_allowed _ _ _ h).2.2.2
          · simp at h

theorem ofUrl_tor (url : String) (hc : Bool) (addr : String) (tor : Bool) :
    (Page.ofUrl url hc addr tor).tor = tor := by
  unfold Page.ofUrl; cases URL.parseUrl url <;> rfl

theorem ofUrl_origin_tor (url : String) (hc : Bool) (addr : String) (tor : Bool) :
    (Page.ofUrl url hc addr tor).origin = (Page.ofUrl url).origin := by
  unfold Page.ofUrl; cases URL.parseUrl url <;> rfl

/-! ## Navigation -/

namespace Nav
open L4Factoidal.Net.Navigation

theorem navPage_tor (url : String) (tor : Bool) : (navPage url tor).tor = tor := ofUrl_tor url false "" tor

/-- Kind: definition fact. Says: the partition of a navigation (its page's origin) is the origin
of its first URL, in either mode. -/
theorem navPage_origin (url : String) (tor : Bool) : (navPage url tor).origin = (Page.ofUrl url).origin :=
  ofUrl_origin_tor url false "" tor

theorem navWire_fields (i : String) (s : Nat) (f : Bool) (m : String) (w : Wire) :
    (navWire i s f m w).resolve = w.resolve ∧ (navWire i s f m w).address = w.address ∧
      (navWire i s f m w).tor = w.tor ∧ (navWire i s f m w).partition = w.partition ∧
      (navWire i s f m w).url = w.url := by
  unfold navWire; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Every live entry's transfer has the entry's page. -/
def Inv (tab : Table) : Prop := ∀ x ∈ tab.live, x.2.t.page = x.2.page

/-- Kind: lemma. Says: `after` tells the host to make exactly the request of a `send` step (with
a navigation's header fields), and the entry it keeps has the page it had and the step's transfer. -/
theorem after_wire (tab : Table) (id : Nat) (e : Entry) (last : Option Answer) (st : Step)
    (tab' : Table) (id' : Nat) (w : Wire) (h : after tab id e last st = (tab', .wire id' w)) :
    ∃ t w0 site, st = .send t w0 ∧ w = navWire e.initiator site (t.redirects == 0) t.method w0 ∧
      tab'.live = (id, { e with t, farthest := site }) :: tab.live ∧ id' = id := by
  unfold after at h
  split at h
  · rename_i t w0
    simp only [Prod.mk.injEq, Out.wire.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨t, w0, _, rfl, h3.symm, by rw [← h1], h2.symm⟩
  · simp at h
  · split at h <;> simp at h

/-- Kind: lemma. Says: the table after `after` keeps the invariant when the step's transfer has
the entry's page. -/
theorem after_inv (tab : Table) (id : Nat) (e : Entry) (last : Option Answer) (st : Step)
    (hi : Inv tab) (hs : ∀ t w, st = .send t w → t.page = e.page) : Inv (after tab id e last st).1 := by
  unfold after
  split
  · rename_i t w
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact hs t w rfl
    · exact hi x hx
  · exact hi
  · split <;> exact hi

theorem start_cases (tab : Table) (url method initiator : String) (policy : ReferrerPolicy.Policy)
    (body : Option ByteArray) (bodyType : String) (tor : Bool) :
    (∃ id why, start tab url method initiator policy body bodyType tor = ({ tab with next := tab.next + 1 }, .fail id why)) ∨
    start tab url method initiator policy body bodyType tor =
      after { tab with next := tab.next + 1 } tab.next
        { t := request tab.next (navPage url tor) method url body bodyType initiator policy, page := navPage url tor, initiator } none
        (plan (request tab.next (navPage url tor) method url body bodyType initiator policy)) := by
  unfold start
  simp only
  split
  · exact Or.inl ⟨_, _, rfl⟩
  · split
    · exact Or.inl ⟨_, _, rfl⟩
    · split
      · exact Or.inl ⟨_, _, rfl⟩
      · split
        · exact Or.inl ⟨_, _, rfl⟩
        · exact Or.inr rfl

/-- Kind: lemma. Says: a `start` that tells the host to make a request does so for the plan of
the navigation's first transfer, whose page is `navPage url tor`. -/
theorem start_send (tab : Table) (url method initiator : String) (policy : ReferrerPolicy.Policy)
    (body : Option ByteArray) (bodyType : String) (tor : Bool) (tab' : Table) (id : Nat) (w : Wire)
    (h : start tab url method initiator policy body bodyType tor = (tab', .wire id w)) :
    ∃ t' w0, plan (request tab.next (navPage url tor) method url body bodyType initiator policy) = .send t' w0 ∧
      w0.url = url ∧ wireReach (navPage url tor) w0 = true ∧
      ∃ site, navWire initiator site (t'.redirects == 0) t'.method w0 = w := by
  rcases start_cases tab url method initiator policy body bodyType tor with ⟨_, _, he⟩ | he
  · rw [he] at h; simp at h
  · rw [he] at h
    obtain ⟨t', w0, site, hst, hw, -, -⟩ := after_wire _ _ _ _ _ _ _ _ h
    obtain ⟨-, hu, hr, -⟩ := plan_send_allowed _ _ _ hst
    exact ⟨t', w0, hst, by rw [hu]; rfl, hr, site, hw.symm⟩

/-- Kind: privacy theorem (Tor mode, first request). Says: every request that a Tor-mode
navigation's `start` tells the host to make is not resolve-only (the host resolves no name),
names no address, is marked `tor`, and carries as its partition the origin of the navigation's
URL, which is not `"null"`. Does not say: that the host routes it through Tor. -/
theorem start_tor (tab : Table) (url method initiator : String) (policy : ReferrerPolicy.Policy)
    (body : Option ByteArray) (bodyType : String) (tab' : Table) (id : Nat) (w : Wire)
    (h : start tab url method initiator policy body bodyType true = (tab', .wire id w)) :
    w.resolve = false ∧ w.address = "" ∧ w.tor = true ∧ w.partition = (Page.ofUrl url).origin ∧
      w.partition ≠ "null" := by
  obtain ⟨t', w0, -, -, hr, site, hw⟩ := start_send _ _ _ _ _ _ _ _ _ _ _ h
  obtain ⟨h1, h2, h3, h4, h5⟩ := wireReach_tor (navPage_tor url true) hr
  obtain ⟨f1, f2, f3, f4, -⟩ := navWire_fields initiator site (t'.redirects == 0) t'.method w0
  rw [← hw, f1, f2, f3, f4, h4, ← navPage_origin url true]
  exact ⟨h1, h2, h3, rfl, h5⟩

/-- Kind: policy theorem (direct mode, first request). Says: a direct-mode navigation's first
request is not marked `tor`, has no partition, and does not name an onion service. -/
theorem start_direct (tab : Table) (url method initiator : String) (policy : ReferrerPolicy.Policy)
    (body : Option ByteArray) (bodyType : String) (tab' : Table) (id : Nat) (w : Wire)
    (h : start tab url method initiator policy body bodyType false = (tab', .wire id w)) :
    w.tor = false ∧ w.partition = "" ∧ onionUrl w.url = false := by
  obtain ⟨t', w0, -, -, hr, site, hw⟩ := start_send _ _ _ _ _ _ _ _ _ _ _ h
  obtain ⟨h1, h2, h3⟩ := wireReach_direct (navPage_tor url false) hr
  obtain ⟨-, -, f3, f4, f5⟩ := navWire_fields initiator site (t'.redirects == 0) t'.method w0
  rw [← hw, f3, f4, f5]
  exact ⟨h1, h2, h3⟩

/-- Kind: lemma. Says: `start` never says done (a `data:` or `blob:` URL answered in the engine
is a failure for a navigation). -/
theorem start_not_done (tab : Table) (url method initiator : String) (policy : ReferrerPolicy.Policy)
    (body : Option ByteArray) (bodyType : String) (tor : Bool) (tab' : Table) (id st : Nat) (ty u : String) (n : Nat) :
    start tab url method initiator policy body bodyType tor ≠ (tab', .done id st ty u n) := by
  intro h
  rcases start_cases tab url method initiator policy body bodyType tor with ⟨_, _, he⟩ | he
  · rw [he] at h; simp at h
  · rw [he] at h
    unfold after at h
    split at h
    · simp at h
    · simp at h
    · simp at h

/-- Kind: policy theorem (RFC 7686 §2). Says: in direct mode a navigation to an onion service
fails before the host is told anything. -/
theorem start_onion_direct (tab : Table) (url method initiator : String) (policy : ReferrerPolicy.Policy)
    (body : Option ByteArray) (bodyType : String) (ho : onionUrl url = true) :
    ∃ tab' id why, start tab url method initiator policy body bodyType false = (tab', .fail id why) := by
  match hs : start tab url method initiator policy body bodyType false with
  | (tab', .fail id why) => exact ⟨tab', id, why, rfl⟩
  | (tab', .wire id w) =>
    obtain ⟨t', w0, -, hu, hr, -⟩ := start_send _ _ _ _ _ _ _ _ _ _ _ hs
    have := (wireReach_direct (navPage_tor url false) hr).2.2
    rw [hu, ho] at this
    cases this
  | (tab', .done id st ty u n) => exact absurd hs (start_not_done _ _ _ _ _ _ _ _ _ _ _ _ _ _)

/-- Kind: invariant. Says: `start` keeps every live navigation's transfer on its entry's page. -/
theorem start_inv (tab : Table) (url method initiator : String) (policy : ReferrerPolicy.Policy)
    (body : Option ByteArray) (bodyType : String) (tor : Bool) (hi : Inv tab) :
    Inv (start tab url method initiator policy body bodyType tor).1 := by
  rcases start_cases tab url method initiator policy body bodyType tor with ⟨_, _, he⟩ | he
  · rw [he]; exact hi
  · rw [he]
    exact after_inv _ _ _ _ _ hi fun t w hs => (plan_send_allowed _ _ _ hs).2.2.2

/-- Kind: invariant. Says: `answer` keeps every live navigation's transfer on its entry's page. -/
theorem answer_inv (tab : Table) (id : Nat) (a : Answer) (hi : Inv tab) : Inv (answer tab id a).1 := by
  unfold answer
  split
  · exact hi
  · rename_i i e he
    have hm := List.mem_of_find?_eq_some he
    have hif : Inv { tab with live := tab.live.filter (·.1 != id) } := fun x hx => hi x ((List.mem_filter.mp hx).1)
    exact after_inv _ _ _ _ _ hif fun t w hs => (onAnswer_page _ _ _ _ hs).trans (hi _ hm)

theorem cancel_inv (tab : Table) (id : Nat) (hi : Inv tab) : Inv (cancel tab id) :=
  fun x hx => hi x ((List.mem_filter.mp hx).1)

/-- Kind: lemma. Says: a wire `answer` gives belongs to a live navigation `e`: it passes
`wireReach` for `e`'s page, and the entry kept for the next hop has the same page. -/
theorem answer_wire (tab : Table) (id : Nat) (a : Answer) (tab' : Table) (id' : Nat) (w : Wire)
    (hi : Inv tab) (h : answer tab id a = (tab', .wire id' w)) :
    ∃ e, (id, e) ∈ tab.live ∧ wireReach e.page w = true ∧
      ∃ e', (id, e') ∈ tab'.live ∧ e'.page = e.page := by
  unfold answer at h
  split at h
  · simp at h
  · rename_i i e he
    have hm := List.mem_of_find?_eq_some he
    have hid : i = id := by simpa using List.find?_some he
    subst hid
    obtain ⟨t, w0, site, hst, hw, hl, -⟩ := after_wire _ _ _ _ _ _ _ _ h
    have hr := onAnswer_reach _ _ _ _ hst
    rw [hi _ hm] at hr
    refine ⟨e, hm, ?_, { e with t, farthest := site }, by rw [hl]; exact List.mem_cons_self, rfl⟩
    obtain ⟨g1, g2, g3, g4, g5⟩ := navWire_fields e.initiator site (t.redirects == 0) t.method w0
    have hrw : wireReach e.page w = wireReach e.page w0 := by
      rw [hw]; simp only [wireReach, torReach, directReach, g1, g2, g3, g4, g5]
    rw [hrw]; exact hr

/-- Kind: privacy theorem (Tor mode, every redirect hop). Says: every request that `answer`
tells the host to make for a Tor-mode navigation is not resolve-only, names no address, is
marked `tor`, and carries the partition of its navigation's page, which is not `"null"`. Does
not say: that the host routes it through Tor. -/
theorem answer_tor (tab : Table) (id : Nat) (a : Answer) (tab' : Table) (id' : Nat) (w : Wire)
    (hi : Inv tab) (h : answer tab id a = (tab', .wire id' w)) :
    ∃ e, (id, e) ∈ tab.live ∧ (e.page.tor = true →
      w.resolve = false ∧ w.address = "" ∧ w.tor = true ∧ w.partition = e.page.origin ∧ w.partition ≠ "null") := by
  obtain ⟨e, hm, hr, -⟩ := answer_wire _ _ _ _ _ _ hi h
  refine ⟨e, hm, fun ht => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := wireReach_tor ht hr
  exact ⟨h1, h2, h3, h4, by rw [h4]; exact h5⟩

/-- Kind: policy theorem (direct mode, every redirect hop). Says: a request that `answer` tells
the host to make for a direct-mode navigation is not marked `tor`, has no partition, and names
no onion service. -/
theorem answer_direct (tab : Table) (id : Nat) (a : Answer) (tab' : Table) (id' : Nat) (w : Wire)
    (hi : Inv tab) (h : answer tab id a = (tab', .wire id' w)) :
    ∃ e, (id, e) ∈ tab.live ∧ (e.page.tor = false → w.tor = false ∧ w.partition = "" ∧ onionUrl w.url = false) := by
  obtain ⟨e, hm, hr, -⟩ := answer_wire _ _ _ _ _ _ hi h
  exact ⟨e, hm, fun ht => wireReach_direct ht hr⟩

/-- Kind: privacy theorem (one circuit set per navigation). Says: a hop that `answer` gives for a
Tor-mode navigation has the partition of the navigation's page, and the entry kept for its next
hop has that same page; with `start_tor` (the first hop's partition is the origin of the first
URL, `navPage_origin`) and `start_inv`/`answer_inv`, every hop of one navigation carries the
same partition, the origin of its first URL. Does not say: that the Tor client keeps partitions
apart (tested, not proved). -/
theorem answer_partition (tab : Table) (id : Nat) (a : Answer) (tab' : Table) (id' : Nat) (w : Wire)
    (hi : Inv tab) (h : answer tab id a = (tab', .wire id' w)) :
    ∃ e, (id, e) ∈ tab.live ∧ (e.page.tor = true → w.partition = e.page.origin) ∧
      ∃ e', (id, e') ∈ tab'.live ∧ e'.page = e.page := by
  obtain ⟨e, hm, hr, hk⟩ := answer_wire _ _ _ _ _ _ hi h
  exact ⟨e, hm, fun ht => (wireReach_tor ht hr).2.2.2.1, hk⟩

end Nav

/-! ## Subresources in Tor mode -/

namespace Sub
open L4Factoidal.Net.Subresource

/-- Kind: privacy theorem (Tor mode, first request). Says: every request that an element's
`start` tells the host to make for a Tor-mode page is not resolve-only, names no address, is
marked `tor`, and carries the page's origin, which is not `"null"`, as its partition. -/
theorem start_tor (tab : Table) (page : Page) (kind url referrer : String) (policy : ReferrerPolicy.Policy)
    (cors : Option Bool) (tab' : Table) (id : Nat) (w : Wire) (hp : page.tor = true)
    (h : start tab page kind url referrer policy cors = (tab', .wire id w)) :
    w.resolve = false ∧ w.address = "" ∧ w.tor = true ∧ w.partition = page.origin ∧ w.partition ≠ "null" := by
  obtain ⟨t, ht⟩ := start_send _ _ _ _ _ _ _ _ _ _ h
  obtain ⟨h1, h2, h3, h4, h5⟩ := plan_tor _ _ _ hp ht
  exact ⟨h1, h2, h3, h4, by rw [h4]; exact h5⟩

/-- Kind: privacy theorem (Tor mode, every redirect hop). Says: every request that `answer`
tells the host to make for an element of a Tor-mode page is not resolve-only, names no address,
is marked `tor`, and carries that page's origin, which is not `"null"`, as its partition. -/
theorem answer_tor (tab : Table) (id : Nat) (a : Answer) (tab' : Table) (id' : Nat) (w : Wire)
    (h : answer tab id a = (tab', .wire id' w)) :
    ∃ t, (id, t) ∈ tab.live ∧ (t.page.tor = true →
      w.resolve = false ∧ w.address = "" ∧ w.tor = true ∧ w.partition = t.page.origin ∧ w.partition ≠ "null") := by
  obtain ⟨t, hm, hr⟩ := Subresource.answer_wire _ _ _ _ _ _ h
  refine ⟨t, hm, fun ht => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := wireReach_tor ht hr
  exact ⟨h1, h2, h3, h4, by rw [h4]; exact h5⟩

/-- Kind: policy theorem (direct mode). Says: an element of a direct-mode page never gets a wire
marked `tor`, with a partition, or naming an onion service. -/
theorem start_direct (tab : Table) (page : Page) (kind url referrer : String) (policy : ReferrerPolicy.Policy)
    (cors : Option Bool) (tab' : Table) (id : Nat) (w : Wire) (hp : page.tor = false)
    (h : start tab page kind url referrer policy cors = (tab', .wire id w)) :
    w.tor = false ∧ w.partition = "" ∧ onionUrl w.url = false := by
  obtain ⟨-, -, -, hr⟩ := Subresource.start_wire _ _ _ _ _ _ _ _ _ _ h
  exact wireReach_direct hp hr

/-- Kind: definition fact. Says: the page that op `subresource` builds with `"tor": true` is in
Tor mode (`Page.ofUrl` keeps its `tor` argument). -/
theorem op_page_tor (doc addr : String) (hc : Bool) : (Page.ofUrl doc hc addr true).tor = true :=
  ofUrl_tor doc hc addr true

end Sub

#print axioms onAnswer_page
#print axioms ofUrl_tor
#print axioms ofUrl_origin_tor
#print axioms Nav.navPage_tor
#print axioms Nav.navPage_origin
#print axioms Nav.navWire_fields
#print axioms Nav.after_wire
#print axioms Nav.after_inv
#print axioms Nav.start_cases
#print axioms Nav.start_send
#print axioms Nav.start_tor
#print axioms Nav.start_direct
#print axioms Nav.start_not_done
#print axioms Nav.start_onion_direct
#print axioms Nav.start_inv
#print axioms Nav.answer_inv
#print axioms Nav.cancel_inv
#print axioms Nav.answer_wire
#print axioms Nav.answer_tor
#print axioms Nav.answer_direct
#print axioms Nav.answer_partition
#print axioms Sub.start_tor
#print axioms Sub.answer_tor
#print axioms Sub.start_direct
#print axioms Sub.op_page_tor

end L4Factoidal.Net.NavigationTheorems
