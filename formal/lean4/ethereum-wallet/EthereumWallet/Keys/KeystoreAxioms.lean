import EthereumWallet.Keys.KeystoreJson
/- Axiom report for the keystore half, imported by `EthereumWallet/Keys.lean` so that the build log carries it.
   Every line must list only propext, Classical.choice, Quot.sound. -/
open EthereumWallet.Keys
#print axioms check_over_limit
#print axioms scrypt_refuses_over_limit
#print axioms scrypt_refuses_large_n
#print axioms check_ok_bound
#print axioms scrypt_ok_bound
#print axioms scrypt_ok_size
#print axioms scrypt_check_error
#print axioms scrypt_refuses_zero_r
#print axioms scrypt_refuses_zero_p
#print axioms scrypt_refuses_bad_n
#print axioms scrypt_refuses_dkLen
#print axioms xorKs_size
#print axioms uint8_xor_cancel
#print axioms xorKs_xorKs
#print axioms aes128Ctr_refuses_key
#print axioms aes128Ctr_refuses_iv
#print axioms aes128Ctr_size
#print axioms aes128Ctr_involutive
#print axioms Json.parseBytes_tooLarge
#print axioms jsonPush_tooDeep
#print axioms decryptWithKey_mac_mismatch
#print axioms decrypt_mac_mismatch
#print axioms decrypt_ok_mac
#print axioms decrypt_refuses_version
#print axioms decrypt_refuses_cipher
#print axioms decrypt_refuses_iv
#print axioms deriveKey_refuses_other
#print axioms deriveKey_refuses_prf
#print axioms deriveKey_pbkdf2_refuses_dkLen
#print axioms deriveKey_pbkdf2_refuses_iterations
#print axioms deriveKey_scrypt_check_error
#print axioms deriveKey_scrypt_over_limit
#print axioms deriveKey_scrypt_refuses_dkLen
#print axioms decrypt_scrypt_over_limit
#print axioms ctDiffFrom_self
#print axioms ctEqBytes_self
#print axioms decryptWithKey_encryptWithKey
#print axioms encrypt_refuses_iv
#print axioms encrypt_refuses_secret
