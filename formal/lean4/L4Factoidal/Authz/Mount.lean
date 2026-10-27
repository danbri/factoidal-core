/-
L4Factoidal.Authz.Mount — an authorization server that shares its issuer
with one LWS storage, on one port (`lws-serve --authz`).

The issuer is the storage root without its trailing slash, as Touchstone's
target contract asks ("Has its authorization server's issuer at
LWS_PUBLIC_URL"). The two endpoints that the metadata names go under the
storage root's `.well-known/`, beside the storage's own services
(`/.well-known/lws-storage`, `lws-subscriptions/`, `lws-type-index`, ...),
so no name that a client can give a storage resource is taken from it. The
names `lws-token` and `lws-jwks` are this server's choice: the LWS drafts fix
only the metadata path (`/.well-known/lws-configuration`), and a client finds
the endpoints in the metadata.

`owns` (`L4Factoidal.Authz.Server`) decides which requests the host gives to
the authorization server; every other request goes to the storage.
-/
import L4Factoidal.Authz.Server
import L4Factoidal.LWS.Binding

namespace L4Factoidal.Authz

def mountedTokenPath : String := "/.well-known/lws-token"
def mountedJwksPath : String := "/.well-known/lws-jwks"

/-- `cfg` with the issuer, the resource and the endpoint paths of an
authorization server that shares its issuer with the storage at `baseIri`.
`storageIri` is the audience of the storage's tokens
(`L4Factoidal.LWS.storageIri`). -/
def mountedOn (cfg : AuthzConfig) (baseIri storageIri : String) : AuthzConfig :=
  { cfg with issuer := trimSlash baseIri, resources := [storageIri]
             tokenPath := mountedTokenPath, jwksPath := mountedJwksPath }

/-- Every path that `endpointOf?` names. -/
def endpointPaths (cfg : AuthzConfig) : List String :=
  let ip := issuerPath cfg.issuer
  [ lwsConfigurationPath cfg.issuer, oauthMetadataPath cfg.issuer
  , "/.well-known/lws-configuration", "/.well-known/oauth-authorization-server"
  , ip ++ cfg.jwksPath, cfg.jwksPath, ip ++ cfg.tokenPath, cfg.tokenPath ]

/-- `endpointOf?` names only the paths of `endpointPaths`: a request for any
other path is the storage's. -/
theorem endpointOf?_mem (cfg : AuthzConfig) (p : String) (e : Endpoint)
    (h : endpointOf? cfg p = some e) : p ∈ endpointPaths cfg := by
  dsimp only [endpointOf?] at h
  simp only [endpointPaths, List.mem_cons, List.not_mem_nil, or_false]
  split at h
  · rename_i hc
    simp only [Bool.or_eq_true, beq_iff_eq] at hc
    rcases hc with ((hc | hc) | hc) | hc <;> simp [hc]
  · split at h
    · rename_i hc
      simp only [Bool.or_eq_true, beq_iff_eq] at hc
      rcases hc with hc | hc <;> simp [hc]
    · split at h
      · rename_i hc
        simp only [Bool.or_eq_true, beq_iff_eq] at hc
        rcases hc with hc | hc <;> simp [hc]
      · cases h

theorem owns_mem (cfg : AuthzConfig) (target : String) (h : owns cfg target = true) :
    (target.splitOn "?").headD target ∈ endpointPaths cfg := by
  unfold owns at h
  match hm : endpointOf? cfg ((target.splitOn "?").headD target) with
  | some e => exact endpointOf?_mem cfg _ e hm
  | none => simp [hm] at h

end L4Factoidal.Authz
