import L4Factoidal.Net.Xhr

namespace L4Factoidal.Net.Xhr

open L4Factoidal.Net.PageFetch

/-- Kind: XHR object table invariant.
Says: setting a handle updates exactly that handle's existing slot.
Does not say: that setting an absent handle allocates a slot. -/
private theorem get_set_same (s : State) (handle : Nat) (x : Xhr) :
    (s.set handle x).get? handle = (s.get? handle).map (fun _ => x) := by
  unfold State.get? State.set
  split
  · rfl
  · change (s.xhrs.set! (handle - 1) x)[handle - 1]? =
      (s.xhrs[handle - 1]?).map (fun _ => x)
    rw [Array.set!, Array.getElem?_setIfInBounds]
    by_cases hin : handle - 1 < s.xhrs.size <;> simp [hin]

/-- Kind: XHR error-state invariant.
Says: the request-error transition for a detached transfer leaves no
realm response at its handle.
Does not say: which callback or other events are queued. -/
private theorem requestError_no_response (s : State) (handle : Nat) (x : Xhr) (reason : String) :
    ((requestError s handle { x with transfer := none } reason).get? handle).bind Xhr.response =
      none := by
  have hset : ∃ next : Xhr,
      requestError s handle { x with transfer := none } reason = s.set handle next ∧
        next.response = none := by
    exact ⟨_, rfl, rfl⟩
  obtain ⟨next, hstate, hresponse⟩ := hset
  rw [hstate, get_set_same]
  cases s.get? handle with
  | none => rfl
  | some _ => exact hresponse

/-- Kind: asynchronous realm response, Fetch and integrity correspondence.
Says: when the host answer completes a matched non-raw XHR transfer and
the actual transition exposes a response on its handle, that response came
from the submitted Fetch step. The Fetch release predicate and the integrity
check both passed for that answer and response.
Does not say: that an error callback has a response, that the host supplied
authentic bytes, that the digest is collision-free, or that sync, deferred
or raw element responses follow this particular path. -/
theorem give_realm_response_released (s : State) (id handle callback : Nat) (a : Answer)
    (t : Transfer) (x : Xhr) (r : Response)
    (hws : s.sockets.findIdx? (·.id == id) = none)
    (hlive : s.live.find? (·.1 == id) = some (id, handle, t))
    (hx : s.get? handle = some x) (hraw : x.raw = false) (hmain : t.phase = .main)
    (hcb : (give s id a).2 = some callback)
    (hresp : ((give s id a).1.get? handle).bind Xhr.response = some r) :
    let submitted := { t with jar := t.storeCookies s.cookies a }
    ∃ t', onAnswer submitted a = .deliver t' r ∧ released submitted a = some a ∧
      Integrity.okFor x.integrity r.tainting r.body = true := by
  simp only [give, hws, hlive, hx] at hcb hresp
  dsimp only
  let finished : State :=
    { s with
      cookies := t.storeCookies s.cookies a
      live := s.live.filter (·.1 != id) }
  have errorHere :
      ((requestError finished handle { x with transfer := none } "error").get? handle).bind
        Xhr.response ≠ some r := by
    intro exposed
    have impossible := (requestError_no_response finished handle x "error").symm.trans exposed
    cases impossible
  cases hanswer : onAnswer { t with jar := t.storeCookies s.cookies a } a with
  | fail reason =>
    simp only [hanswer] at hresp
    exact False.elim (errorHere hresp)
  | send sent wire =>
    simp only [hanswer] at hcb hresp
    let noted := ({ s with cookies := t.storeCookies s.cookies a } : State).notePin sent
    generalize hchecked :
      (if sent.redirects != t.redirects then cspRequest noted "connect-src" sent.url true
        else (noted, false)) = checked at hcb hresp
    obtain ⟨checked, blocked⟩ := checked
    by_cases hb : blocked = true
    · simp only [hb, if_true] at hresp
      rw [requestError_no_response] at hresp
      cases hresp
    · simp only [hb] at hcb
      cases hcb
  | deliver t' delivered =>
    simp only [hanswer, hraw, Bool.false_eq_true, if_false, Bool.false_and] at hresp
    simp only [hraw] at errorHere
    split at hresp
    · exact False.elim (errorHere hresp)
    · rename_i hint
      split at hresp
      · exact False.elim (errorHere hresp)
      · have hpass : Integrity.okFor x.integrity delivered.tainting delivered.body = true := by
          cases hok : Integrity.okFor x.integrity delivered.tainting delivered.body
          · exact False.elim (hint (by simp [hok]))
          · rfl
        have hrealm : x.forRealm delivered = delivered := by
          simp [Xhr.forRealm, Xhr.hidesScript, hraw]
        let next : Xhr :=
          { (x.withAnswer delivered) with
            transfer := none
            uploadComplete := true
            events := x.events ++ responseEvents x (x.forRealm delivered) }
        have previous : finished.get? handle = some x := hx
        have hget := get_set_same finished handle next
        rw [previous] at hget
        change ((finished.set handle next).get? handle).bind Xhr.response = some r at hresp
        rw [hget] at hresp
        change some (x.forRealm delivered) = some r at hresp
        rw [hrealm] at hresp
        cases hresp
        exact ⟨t', rfl, deliver_released _ _ _ _ hmain hanswer, hpass⟩

#print axioms give_realm_response_released

end L4Factoidal.Net.Xhr
