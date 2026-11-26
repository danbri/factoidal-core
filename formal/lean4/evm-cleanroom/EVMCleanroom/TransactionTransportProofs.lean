import EVMCleanroom.TransactionCodec

/-!
# Transaction JSON preparse resource boundaries

The statements name the actual scanner and shared native-codec entry. They
establish bounded scanner counters and the continuation boundary, without
claiming a formal refinement or general allocation bound for Lean's JSON parser.
-/

namespace EVMCleanroom.TransactionTransport

/-- Kind: executable structural-step invariant.
    Says: every successful structural step preserves the nesting bound and
    resets numeric counters to zero or a one-byte numeric start.
    Does not say: that opening and closing delimiters form valid JSON. -/
theorem structural_bounded (state next : ScanState) (byte : UInt8)
    (hDepth : state.depth ≤ maxDepth) (h : structural state byte = .ok next) :
    next.depth ≤ maxDepth ∧ next.numberBytes ≤ maxNumberBytes ∧ next.exponent ≤ maxExponent := by
  unfold structural at h
  dsimp only at h
  split at h
  · cases h
    exact ⟨hDepth, Nat.zero_le _, Nat.zero_le _⟩
  split at h
  · split at h
    · cases h
    · rename_i hRoom
      cases h
      change state.depth + 1 ≤ maxDepth ∧ 0 ≤ maxNumberBytes ∧ 0 ≤ maxExponent
      exact ⟨by omega, Nat.zero_le _, Nat.zero_le _⟩
  split at h
  · cases h
    exact ⟨Nat.le_trans (Nat.sub_le _ _) hDepth, Nat.zero_le _, Nat.zero_le _⟩
  split at h
  · cases h
    change state.depth ≤ maxDepth ∧ 1 ≤ maxNumberBytes ∧ 0 ≤ maxExponent
    exact ⟨hDepth, by decide, Nat.zero_le _⟩
  · cases h
    exact ⟨hDepth, Nat.zero_le _, Nat.zero_le _⟩

/-- Kind: executable lexical-step invariant.
    Says: every successful byte step preserves all three scanner bounds,
    including quoted, escaped and numeric bytes.
    Does not say: that arbitrary unbounded caller-created states are safe. -/
theorem step_bounded (state next : ScanState) (byte : UInt8)
    (hDepth : state.depth ≤ maxDepth) (hNumber : state.numberBytes ≤ maxNumberBytes)
    (hExponent : state.exponent ≤ maxExponent) (h : step state byte = .ok next) :
    next.depth ≤ maxDepth ∧ next.numberBytes ≤ maxNumberBytes ∧ next.exponent ≤ maxExponent := by
  unfold step at h
  dsimp only at h
  split at h
  · split at h
    · cases h
      exact ⟨hDepth, hNumber, hExponent⟩
    split at h
    · cases h
      exact ⟨hDepth, hNumber, hExponent⟩
    split at h
    · cases h
      exact ⟨hDepth, hNumber, hExponent⟩
    · cases h
      exact ⟨hDepth, hNumber, hExponent⟩
  · split at h
    · by_cases hNumberBound : state.numberBytes + 1 > maxNumberBytes
      · simp only [if_pos hNumberBound] at h
        cases h
      · simp only [if_neg hNumberBound] at h
        let exponent := if state.exponentMode && digit byte then
          state.exponent * 10 + (byte.toNat - 48) else state.exponent
        change (if exponent > maxExponent then Except.error "json-exponent-limit" else
          Except.ok { state with
            numberBytes := state.numberBytes + 1
            exponent := exponent
            exponentMode := state.exponentMode || byte == 69 || byte == 101 }) = Except.ok next at h
        by_cases hExponentBound : exponent > maxExponent
        · simp only [if_pos hExponentBound] at h
          cases h
        · simp only [if_neg hExponentBound] at h
          cases h
          exact ⟨hDepth, Nat.le_of_not_gt hNumberBound, Nat.le_of_not_gt hExponentBound⟩
    · exact structural_bounded state next byte hDepth h

/-- Kind: executable error persistence.
    Says: once the scanner has refused, feeding any further byte preserves
    the exact error without invoking the lexical step.
    Does not say: that the finite outer fold stops traversing its input. -/
theorem feed_error (reason : String) (byte : UInt8) :
    feed (.error reason) byte = .error reason := rfl

/-- Kind: executable fold-step invariant.
    Says: feeding a bounded successful state or any prior refusal can only
    yield another bounded successful state or a refusal.
    Does not say: that every input byte can be accepted. -/
theorem feed_bounded (result : Except String ScanState) (byte : UInt8)
    (hPrior : ∀ state, result = .ok state →
      state.depth ≤ maxDepth ∧ state.numberBytes ≤ maxNumberBytes ∧ state.exponent ≤ maxExponent)
    (next : ScanState) (h : feed result byte = .ok next) :
    next.depth ≤ maxDepth ∧ next.numberBytes ≤ maxNumberBytes ∧ next.exponent ≤ maxExponent := by
  cases result with
  | error reason => cases h
  | ok state =>
    obtain ⟨hDepth, hNumber, hExponent⟩ := hPrior state rfl
    exact step_bounded state next byte hDepth hNumber hExponent h

/-- Kind: actual scanner resource invariant.
    Says: scanning any finite byte array from the real empty initial state
    can return only depths at most 64, numeric spans at most 96 bytes and
    exponent magnitudes at most 78.
    Does not say: that successful scanning establishes JSON grammar validity
    or a complete runtime memory bound. -/
theorem scan_bounded (bytes : ByteArray) (next : ScanState) (h : scan bytes = .ok next) :
    next.depth ≤ maxDepth ∧ next.numberBytes ≤ maxNumberBytes ∧ next.exponent ≤ maxExponent := by
  let P := fun result : Except String ScanState => ∀ state, result = .ok state →
    state.depth ≤ maxDepth ∧ state.numberBytes ≤ maxNumberBytes ∧ state.exponent ≤ maxExponent
  have hLoop (i : Nat) : ∀ j result, P result →
      P (ByteArray.foldlM.loop (m := Id) (fun state byte => pure (feed state byte))
        bytes bytes.size (Nat.le_refl _) i j result) := by
    induction i with
    | zero =>
      intro j result hResult
      unfold ByteArray.foldlM.loop
      split <;> exact hResult
    | succ i ih =>
      intro j result hResult
      unfold ByteArray.foldlM.loop
      split
      · next hPosition =>
        exact ih (j + 1) (feed result bytes[j]) (fun state hState =>
          feed_bounded result bytes[j] hResult state hState)
      · exact hResult
  have hInitial : P (.ok {}) := by
    intro state hState
    cases hState
    exact ⟨by decide, by decide, by decide⟩
  have hComplete : P (scan bytes) := by
    simpa [scan, ByteArray.foldl, ByteArray.foldlM, Id.run] using hLoop bytes.size 0 (.ok {}) hInitial
  exact hComplete next h

/-- Kind: exact nesting refusal.
    Says: an unquoted array or object opener at the depth limit is rejected
    by the actual byte step before the JSON parser is selected.
    Does not say: that mismatched delimiters are accepted by JSON parsing. -/
theorem step_depth_limit (state : ScanState) (byte : UInt8)
    (hQuoted : state.quoted = false) (hOpen : byte = 91 ∨ byte = 123)
    (hDepth : maxDepth ≤ state.depth) : step state byte = .error "json-nesting-limit" := by
  rcases hOpen with rfl | rfl <;>
    simp [step, structural, numericByte, digit, hQuoted, hDepth]

/-- Kind: exact numeric-token refusal.
    Says: another numeric byte at the token-span limit produces the token
    refusal, independently of whether that spelling would be valid JSON.
    Does not say: that quoted decimal strings have this numeric-token limit. -/
theorem step_number_limit (state : ScanState) (byte : UInt8)
    (hQuoted : state.quoted = false) (hNumeric : numericByte byte = true)
    (hSpan : maxNumberBytes ≤ state.numberBytes) :
    step state byte = .error "json-number-token-limit" := by
  have hPositive : 0 < maxNumberBytes := by decide
  have hActive : state.numberBytes ≠ 0 := by omega
  have hLimit : state.numberBytes + 1 > maxNumberBytes := by omega
  simp [step, hQuoted, hNumeric, hActive, hLimit]

/-- Kind: exact exponent refusal.
    Says: an exponent digit whose updated magnitude exceeds 78 produces the
    exponent refusal when the token itself still fits its byte allowance.
    Does not say: that malformed numeric spelling passes the JSON grammar. -/
theorem step_exponent_limit (state : ScanState) (byte : UInt8)
    (hQuoted : state.quoted = false) (hActive : state.numberBytes ≠ 0)
    (hMode : state.exponentMode = true) (hDigit : digit byte = true)
    (hSpan : state.numberBytes + 1 ≤ maxNumberBytes)
    (hExponent : maxExponent < state.exponent * 10 + (byte.toNat - 48)) :
    step state byte = .error "json-exponent-limit" := by
  simp [step, numericByte, hQuoted, hActive, hMode, hDigit, Nat.not_lt.mpr hSpan, hExponent]

/-- Kind: exact accepted exponent step.
    Says: a digit within both numeric bounds updates the actual scanner's
    magnitude and byte count exactly, retaining the structural state.
    Does not say: that a complete valid JSON number has been parsed. -/
theorem step_exponent_exact (state : ScanState) (byte : UInt8)
    (hQuoted : state.quoted = false) (hActive : state.numberBytes ≠ 0)
    (hMode : state.exponentMode = true) (hDigit : digit byte = true)
    (hSpan : state.numberBytes + 1 ≤ maxNumberBytes)
    (hExponent : state.exponent * 10 + (byte.toNat - 48) ≤ maxExponent) :
    step state byte = .ok { state with
      numberBytes := state.numberBytes + 1
      exponent := state.exponent * 10 + (byte.toNat - 48)
      exponentMode := true } := by
  simp [step, numericByte, hQuoted, hActive, hMode, hDigit,
    Nat.not_lt.mpr hSpan, Nat.not_lt.mpr hExponent]

/-- Kind: quoted-byte correspondence.
    Says: an escaped byte inside a string clears only the escape flag, even
    when that byte is a quote, bracket, slash or digit.
    Does not say: that every escape spelling is valid JSON. -/
theorem step_quoted_escaped (state : ScanState) (byte : UInt8)
    (hQuoted : state.quoted = true) (hEscaped : state.escaped = true) :
    step state byte = .ok { state with escaped := false } := by
  simp [step, hQuoted, hEscaped]

/-- Kind: quoted-byte correspondence.
    Says: an unescaped backslash in a string sets the actual scanner's escape
    flag without changing depth or numeric counters.
    Does not say: which following escape spellings the JSON parser accepts. -/
theorem step_quoted_escape (state : ScanState)
    (hQuoted : state.quoted = true) (hEscaped : state.escaped = false) :
    step state 92 = .ok { state with escaped := true } := by
  simp [step, hQuoted, hEscaped]

/-- Kind: quoted-byte correspondence.
    Says: an unescaped closing quote leaves string mode and preserves all
    structural and numeric counters.
    Does not say: that the enclosing JSON document is complete. -/
theorem step_quoted_close (state : ScanState)
    (hQuoted : state.quoted = true) (hEscaped : state.escaped = false) :
    step state 34 = .ok { state with quoted := false } := by
  simp [step, hQuoted, hEscaped]

/-- Kind: quoted-byte correspondence.
    Says: other unescaped string bytes leave the scanner state unchanged;
    string-contained openers and exponent digits cannot consume those limits.
    Does not say: that control characters are valid unescaped JSON characters. -/
theorem step_quoted_literal (state : ScanState) (byte : UInt8)
    (hQuoted : state.quoted = true) (hEscaped : state.escaped = false)
    (hSlash : byte ≠ 92) (hQuote : byte ≠ 34) : step state byte = .ok state := by
  simp [step, hQuoted, hEscaped, hSlash, hQuote]

/-- Kind: executable parser-continuation refusal.
    Says: any continuation, of any result type, receives the same scanner
    refusal; the executable match selects its error branch before the parser.
    Does not say: that the compiler/runtime's evaluation strategy is proved. -/
theorem parseWith_refused {α : Type} (parser : String → Except String α)
    (text reason : String) (h : check text = .error reason) :
    parseWith parser text = .error reason := by
  simp [parseWith, h]

/-- Kind: executable parser continuation.
    Says: after successful resource admission, the actual helper returns
    exactly the supplied parser's result, retaining its grammar decisions.
    Does not say: that resource admission itself establishes valid JSON. -/
theorem parseWith_checked {α : Type} (parser : String → Except String α)
    (text : String) (h : check text = .ok ()) : parseWith parser text = parser text := by
  simp [parseWith, h]

/-- Kind: shared native-codec refusal boundary.
    Says: the public parseJSON used by all three transaction CLIs returns the
    actual byte-scanner refusal before selecting Lean.Json.parse.
    Does not say: that the standard parser itself is resource-verified. -/
theorem parseJSON_scan_refused (text reason : String)
    (h : scan text.toUTF8 = .error reason) :
    TransactionCodec.parseJSON text = .error reason := by
  simp only [TransactionCodec.parseJSON, parseWith, check, h]

/-- Kind: shared native-codec correspondence.
    Says: safe input reaches exactly the original Lean.Json.parse, including
    its normal decimal/exponent spellings and malformed-input errors.
    Does not say: that any particular input satisfies the later schema. -/
theorem parseJSON_checked (text : String) (h : check text = .ok ()) :
    TransactionCodec.parseJSON text = Lean.Json.parse text := by
  exact parseWith_checked Lean.Json.parse text h

#print axioms structural_bounded
#print axioms step_bounded
#print axioms feed_error
#print axioms feed_bounded
#print axioms scan_bounded
#print axioms step_depth_limit
#print axioms step_number_limit
#print axioms step_exponent_limit
#print axioms step_exponent_exact
#print axioms step_quoted_escaped
#print axioms step_quoted_escape
#print axioms step_quoted_close
#print axioms step_quoted_literal
#print axioms parseWith_refused
#print axioms parseWith_checked
#print axioms parseJSON_scan_refused
#print axioms parseJSON_checked

end EVMCleanroom.TransactionTransport
