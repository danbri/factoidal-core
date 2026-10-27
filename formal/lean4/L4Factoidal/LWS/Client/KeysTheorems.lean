/-
L4Factoidal.LWS.Client.KeysTheorems — the identifier `Keys` makes names the
key it was made from. https://github.com/danbri/factoidal/issues/1065

`Authz.multikeyJwk?` is how the authorization server reads the key of a
`did:key` subject (`Authz.SubjectToken`). For a multikey made here:

* `multikeyJwk?_ed25519`: an Ed25519 public key of 32 bytes is read back as
  that key, for every `Authz.Crypto`.
* `multikeyJwk?_p256`: a P-256 public key `x || y` is read back as `x` and
  `y`, for every `Authz.Crypto` whose point decompression undoes the
  compression `compressP256` makes of that key (the hypothesis `hdec`, which
  is a property of the HACL\* primitive; it says nothing about the multikey).
-/
import L4Factoidal.LWS.Client.Keys
import L4Factoidal.VC.Theorems

namespace L4Factoidal.LWS.Client

open L4Factoidal.VC.Multibase L4Factoidal.Authz

theorem drop_z (s : String) : (("z" ++ s).drop 1).copy = s := by
  apply String.toList_injective
  simp [String.toList_copy_drop]

theorem multikeyJwk?_ed25519 (C : Crypto) (pk : Bytes) (h : pk.length = 32) :
    multikeyJwk? C (ed25519PublicKeyToMultikey pk) = some (.okp ⟨pk.toArray⟩) := by
  unfold multikeyJwk? ed25519PublicKeyToMultikey multibaseEncodeBase58btc
  simp [drop_z, base58Decode?_base58Encode, ed25519PubPrefix, h]

theorem size_single (b : UInt8) : (ByteArray.mk #[b]).size = 1 := rfl

theorem compressP256_size (xy : ByteArray) (hsz : xy.size = 64) : (compressP256 xy).size = 33 := by
  simp [compressP256, ByteArray.size_append, ByteArray.size_extract, hsz, size_single]

theorem ofByteArray_toArray (c : ByteArray) : (⟨(ofByteArray c).toArray⟩ : ByteArray) = c := by
  cases c
  simp [ofByteArray]

theorem multikeyJwk?_p256 (C : Crypto) (xy : ByteArray) (hsz : xy.size = 64)
    (hdec : C.p256Decompress (compressP256 xy) = some xy) :
    multikeyJwk? C (p256PublicKeyToMultikey xy) = some (.ec (xy.extract 0 32) (xy.extract 32 64)) := by
  have hlen : (ofByteArray (compressP256 xy)).length = 33 := by
    have := compressP256_size xy hsz
    show (compressP256 xy).data.toList.length = 33
    rw [Array.length_toList]
    exact this
  unfold multikeyJwk? p256PublicKeyToMultikey multibaseEncodeBase58btc
  simp [drop_z, base58Decode?_base58Encode, p256PubPrefix]
  refine ⟨hlen, xy, ?_, rfl, rfl⟩
  rw [ofByteArray_toArray]
  exact hdec

end L4Factoidal.LWS.Client
