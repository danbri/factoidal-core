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

theorem cid_multibaseDecode_z (bs : Bytes) :
    L4Factoidal.CID.multibaseDecode? ("z" ++ base58Encode bs) = some (.base58btc, bs) := by
  unfold L4Factoidal.CID.multibaseDecode?
  have : ("z" ++ base58Encode bs).toList = 'z' :: (base58Encode bs).toList := by
    simp [String.toList_append]
  rw [this]
  simp only
  rw [String.ofList_toList, base58Decode?_base58Encode]
  rfl

/-- A Multikey of a CID 1.0 §2.2.2 header and the length of its type
decodes to that type and key. -/
theorem decodePublicMultikey_encode (kt : L4Factoidal.CID.KeyType) (key : Bytes)
    (h : key.length = kt.publicLength) :
    L4Factoidal.CID.decodePublicMultikey ("z" ++ base58Encode (kt.publicHeader ++ key)) = .ok (kt, key) := by
  unfold L4Factoidal.CID.decodePublicMultikey
  rw [cid_multibaseDecode_z]
  cases kt <;>
    simp [L4Factoidal.CID.header2?, L4Factoidal.CID.KeyType.publicHeader, L4Factoidal.CID.KeyType.all,
      L4Factoidal.CID.KeyType.publicLength, h] at h ⊢

theorem multikeyJwk?_ed25519 (C : Crypto) (pk : Bytes) (h : pk.length = 32) :
    multikeyJwk? C (ed25519PublicKeyToMultikey pk) = some (.okp ⟨pk.toArray⟩) := by
  have := decodePublicMultikey_encode .ed25519 pk h
  unfold multikeyJwk? ed25519PublicKeyToMultikey multibaseEncodeBase58btc
  simp only [ed25519PubPrefix, L4Factoidal.CID.KeyType.publicHeader] at *
  rw [this]
  rfl

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
  have hd := decodePublicMultikey_encode .p256 (ofByteArray (compressP256 xy)) hlen
  unfold multikeyJwk? p256PublicKeyToMultikey multibaseEncodeBase58btc
  simp only [p256PubPrefix, L4Factoidal.CID.KeyType.publicHeader] at *
  rw [hd]
  simp only [materialJwk?]
  rw [ofByteArray_toArray, hdec]
  rfl

end L4Factoidal.LWS.Client
