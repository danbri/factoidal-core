import L4Factoidal.HTTP.Wire

namespace L4Factoidal.HTTP.Wire

open L4Factoidal.HTTP

/-- Kind: chunk decoder trailer invariant.
Says: a successful trailer scan publishes exactly the accumulated payload.
Does not say: that the payload fits any particular limit. -/
private theorem chunk_trailer_payload {b acc body : ByteArray} {fuel pos endPos : Nat}
    (h : decodeChunked.trailer b fuel pos acc = .ok (some (body, endPos))) :
    body = acc := by
  induction fuel generalizing pos with
  | zero => cases h
  | succ fuel ih =>
    simp only [decodeChunked.trailer] at h
    split at h
    · cases h
    · split at h
      · cases h
        rfl
      · exact ih h

/-- Kind: chunk decoder accumulator invariant.
Says: after a bounded initial payload, every successful chunk decoding result
fits the configured body limit.
Does not say: that the trailer or transfer coding overhead fits that limit. -/
private theorem chunk_go_body_bound {b acc body : ByteArray} {limit fuel pos endPos : Nat}
    (hacc : acc.size ≤ limit)
    (h : decodeChunked.go b limit fuel pos acc = .ok (some (body, endPos))) :
    body.size ≤ limit := by
  induction fuel generalizing pos acc with
  | zero => cases h
  | succ fuel ih =>
    simp only [decodeChunked.go] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rw [chunk_trailer_payload h]
          exact hacc
        · split at h
          · cases h
          · rename_i hlimit
            split at h
            · cases h
            · split at h
              · cases h
              · apply ih _ h
                rw [ByteArray.size_append, ByteArray.size_extract]
                omega

/-- Kind: chunk decoder resource bound.
Says: the actual chunk decoder returns at most the configured number of
payload bytes on success.
Does not say: that the input buffer or the decoder's peak allocation fits that limit. -/
theorem decodeChunked_body_bound {b body : ByteArray} {pos limit endPos : Nat}
    (h : decodeChunked b pos limit = .ok (some (body, endPos))) :
    body.size ≤ limit :=
  chunk_go_body_bound (Nat.zero_le limit) h

/-- Kind: request body decoding provenance.
Says: a request emitted by UTF-8 decoding carries the decoded payload in its
text field and leaves its raw byte override empty.
Does not say: that the original wire buffer contained only that payload. -/
private theorem decoded_body_of_finish {payload : ByteArray}
    {seed req : Request} {endPos consumed bodyLimit : Nat} {keep keepAlive : Bool}
    (hsize : payload.size ≤ bodyLimit)
    (h : (match String.fromUTF8? payload with
      | none => Frame.reject 400 "request content is not UTF-8"
      | some text => Frame.request { seed with body := text, bytes := none } endPos keep) =
      .request req consumed keepAlive) :
    ∃ body : ByteArray, String.fromUTF8? body = some req.body ∧
      body.size ≤ bodyLimit ∧ req.bytes = none := by
  split at h
  · cases h
  · rename_i text hdecoded
    cases h
    exact ⟨payload, hdecoded, hsize, rfl⟩

/-- Kind: HTTP wire framing and delivered request resource bound.
Says: a successful frame has a header terminator within the configured
header bound and an actual payload whose UTF-8 decode is the body of the
delivered request. The payload fits the configured body limit for both
Content-Length and chunked transfer. The request uses the text body.
Does not say: that socket buffering, trailer bytes or total on-wire request
size fit the body limit, or that the caller accepted the request semantically. -/
theorem frameRequest_body_bound {b : ByteArray} {headLimit bodyLimit consumed : Nat}
    {req : Request} {keepAlive : Bool}
    (h : frameRequest b headLimit bodyLimit = .request req consumed keepAlive) :
    (∃ headEnd, findHeadEnd b = some headEnd ∧ headEnd ≤ headLimit) ∧
    (∃ payload : ByteArray, String.fromUTF8? payload = some req.body ∧
      payload.size ≤ bodyLimit ∧ req.bytes = none) := by
  cases hhead : findHeadEnd b with
  | none =>
    simp only [frameRequest, hhead] at h
    split at h <;> cases h
  | some headEnd =>
    simp only [frameRequest, hhead] at h
    split at h
    · cases h
    · rename_i hlarge
      refine ⟨⟨headEnd, rfl, Nat.le_of_not_gt hlarge⟩, ?_⟩
      split at h
      · cases h
      · rename_i head htext
        cases hparse : parseHead head with
        | error why => cases why; simp [hparse] at h
        | ok parsed =>
          rcases parsed with ⟨method, path, qs, version, headers⟩
          simp only [hparse] at h
          let seed : Request := { method, path, queryStr := qs, version, headers }
          split at h
          · split at h
            · cases h
            · split at h
              · cases h
              · cases h
              · rename_i body endPos hchunk
                exact decoded_body_of_finish (seed := seed) (decodeChunked_body_bound hchunk) h
          · split at h
            · cases h
            · exact decoded_body_of_finish (seed := seed) (Nat.zero_le bodyLimit) h
            · rename_i len _
              split at h
              · cases h
              · rename_i hbody
                split at h
                · cases h
                · have hsize : (b.extract (headEnd + 4) (headEnd + 4 + len)).size ≤ bodyLimit := by
                    rw [ByteArray.size_extract]
                    omega
                  exact decoded_body_of_finish (seed := seed) hsize h

#print axioms decodeChunked_body_bound
#print axioms frameRequest_body_bound

end L4Factoidal.HTTP.Wire
