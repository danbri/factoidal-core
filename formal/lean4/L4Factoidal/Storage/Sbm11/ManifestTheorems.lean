/-
L4Factoidal.Storage.Sbm11.ManifestTheorems — the SBM11 manifest round trip.

* `getArtifact_artifactBytes`: one artifact record.
* `decodeManifest_encodeManifest?`: `encodeManifest? m = some bytes →
  decodeManifest bytes = some m`. The only hypothesis is the encoder's
  admission.
* `decodeManifest_admitted`: a manifest that decodes is admitted.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.Manifest
import L4Factoidal.Storage.ShardManifestTheorems
import L4Factoidal.Storage.Sbm11.ColumnTheorems

namespace L4Factoidal.Storage.Sbm11.Manifest

open L4Factoidal (two32 two64)
open L4Factoidal.Storage.ShardManifest (encodeString decodeString takeExact byteArrayOfList fitsU32
  encodeChunkedRef decodeChunkedRef decodeString_encodeString takeExact_append
  decodeChunkedRef_encodeChunkedRef byteArrayOfList_toList length_toList takeExact_of_length)
open L4Factoidal.Storage.Sbm11.Column (put64 get64 put32 get32 get64_put64 get32_put32)

theorem getArtifact_artifactBytes (a : Artifact) (h : artifactAdmitted a = true) (rest : List UInt8) :
    getArtifact (artifactBytes a ++ rest) = some (a, rest) := by
  simp only [artifactAdmitted, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hrole, hfile⟩, _⟩, hbytes⟩, hsha⟩, hv⟩, htotal⟩, hcb⟩, hcc⟩ := h
  have hroot : a.merkle.root.size = 32 := by
    unfold ChunkedArtifact.valid at hv
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv
    exact hv.1.2
  have h32 : a.sha256.toList.length = 32 := by rw [length_toList]; exact hsha
  unfold getArtifact artifactBytes
  simp only [List.append_assoc]
  rw [decodeString_encodeString _ _ hrole]
  simp only [bind, Option.bind]
  rw [decodeString_encodeString _ _ hfile]
  dsimp only
  rw [get64_put64 _ hbytes]
  dsimp only
  rw [takeExact_of_length _ _ _ h32]
  dsimp only
  rw [decodeChunkedRef_encodeChunkedRef _ _ _ hcb hcc hroot htotal]
  dsimp only
  rw [byteArrayOfList_toList]

theorem getArtifactsGo_artifacts : ∀ (as : List Artifact) (acc : List Artifact) (rest : List UInt8),
    (∀ a ∈ as, artifactAdmitted a = true) →
    getArtifactsGo as.length ((as.map artifactBytes).flatten ++ rest) acc = some (acc.reverse ++ as, rest) := by
  intro as
  induction as with
  | nil => intro acc rest _; simp [getArtifactsGo]
  | cons a as ih =>
    intro acc rest hf
    simp only [List.map_cons, List.flatten_cons, List.append_assoc, List.length_cons, getArtifactsGo]
    rw [getArtifact_artifactBytes a (hf a (by simp))]
    dsimp only
    rw [ih (a :: acc) rest (fun x hx => hf x (by simp [hx]))]
    simp

theorem decodeManifest_magic (rest : List UInt8) :
    decodeManifest (83 :: 66 :: 77 :: 48 :: 11 :: rest) = decodeManifestTail rest := by
  unfold decodeManifest
  dsimp only
  rw [if_pos (show ([83, 66, 77, 48, 11] : List UInt8) = manifestMagic from rfl)]

/-- The manifest round trip. The only hypothesis is the encoder's admission. -/
theorem decodeManifest_encodeManifest? (m : Manifest) (bs : List UInt8)
    (h : encodeManifest? m = some bs) : decodeManifest bs = some m := by
  unfold encodeManifest? at h
  split at h
  · rename_i hadm
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨layout, sourceBytes, sha, quads, terms, artifacts⟩ := m
    have hadm' := hadm
    simp only [manifestAdmitted, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hadm'
    obtain ⟨⟨⟨⟨⟨⟨⟨_, hlay⟩, hsb⟩, hsha⟩, hq⟩, ht⟩, hroles⟩, hall⟩ := hadm'
    have h32 : sha.toList.length = 32 := by rw [length_toList]; exact hsha
    have hcount : artifacts.length < 4294967296 := by
      have := congrArg List.length hroles
      simp only [List.length_map] at this
      have h10 : roles.length = 10 := rfl
      omega
    have he := getArtifactsGo_artifacts artifacts [] [] (fun a ha => List.all_eq_true.mp hall a ha)
    simp only [List.append_nil, List.reverse_nil, List.nil_append] at he
    have hf : decodeFields (put64 sourceBytes ++ (sha.toList ++ (put64 quads ++ (put64 terms ++
        (put32 artifacts.length ++ (List.map artifactBytes artifacts).flatten))))) =
        some { sourceBytes, sha := sha.toList, quads, terms, artifacts } := by
      -- `split` on each `match`: `dsimp only` or `simp only` after the
      -- `takeExact` rewrite did not return in 100 s (2026-10-12)
      generalize sha.toList = shaL at h32 ⊢
      unfold decodeFields
      simp only [get64_put64 _ hsb]
      rw [takeExact_of_length _ _ _ h32]
      split
      · rename_i heq; cases heq
      · rename_i sha' r3 heq
        simp only [Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        rw [get64_put64 _ hq]
        split
        · rename_i heq; cases heq
        · rename_i q' r4 heq
          simp only [Option.some.injEq, Prod.mk.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          rw [get64_put64 _ ht]
          split
          · rename_i heq; cases heq
          · rename_i t' r5 heq
            simp only [Option.some.injEq, Prod.mk.injEq] at heq
            obtain ⟨rfl, rfl⟩ := heq
            rw [get32_put32 _ hcount]
            split
            · rename_i heq; cases heq
            · rename_i c' r6 heq
              simp only [Option.some.injEq, Prod.mk.injEq] at heq
              obtain ⟨rfl, rfl⟩ := heq
              rw [he]
    have hmb : manifestBytes { layout, sourceBytes, sourceSha256 := sha, quads, terms, artifacts } =
        83 :: 66 :: 77 :: 48 :: 11 :: (encodeString layout ++ (put64 sourceBytes ++ (sha.toList ++
          (put64 quads ++ (put64 terms ++ (put32 artifacts.length ++
            (List.map artifactBytes artifacts).flatten)))))) := by
      simp only [manifestBytes, manifestMagic, List.cons_append, List.nil_append, List.append_assoc]
    rw [hmb, decodeManifest_magic]
    unfold decodeManifestTail
    rw [decodeString_encodeString _ _ hlay]
    split
    · rename_i heq; cases heq
    · rename_i lay r1 heq
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      rw [hf]
      split
      · rename_i heq; cases heq
      · rename_i f heq
        simp only [Option.some.injEq] at heq
        subst heq
        unfold admitManifest
        rw [byteArrayOfList_toList, if_pos hadm]
  · cases h

theorem admitManifest_admitted (m m' : Manifest) (h : admitManifest m' = some m) :
    manifestAdmitted m = true := by
  unfold admitManifest at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq] at h
    subst h
    exact hc
  · cases h

/-- A manifest that decodes is admitted. -/
theorem decodeManifest_admitted (bs : List UInt8) (m : Manifest) (h : decodeManifest bs = some m) :
    manifestAdmitted m = true := by
  unfold decodeManifest decodeManifestTail at h
  repeat' split at h
  all_goals first | cases h | exact admitManifest_admitted _ _ h

end L4Factoidal.Storage.Sbm11.Manifest
