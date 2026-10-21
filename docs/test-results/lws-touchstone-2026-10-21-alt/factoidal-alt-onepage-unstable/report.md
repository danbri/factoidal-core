# Touchstone conformance report

**CONFORMANT**: only MUST tests decide conformance (definitions/EXECUTION.md section 9), and 0 failed or ended cantTell. SHOULD and MAY failures are advisory: 0. Inapplicable MUST tests are coverage this run did not have: 8.

| | |
|---|---|
| target | factoidal-alt-onepage-unstable |
| base URL | `http://127.0.0.1:41945/` |
| run | `cdc3b6df` |
| started | 2026-10-21T22:39:25.481696436Z |

## Results

| passed | failed | cantTell | inapplicable |
|---:|---:|---:|---:|
| 212 | 0 | 0 | 9 |

## Requirement coverage by level

| level | in catalog | covered | failing |
|---|---:|---:|---:|
| MUST | 214 | 205 | 0 |
| SHOULD | 25 | 20 | 0 |
| MAY | 33 | 18 | 0 |

49 catalog requirements bind only clients, receivers, identity providers or other specifications, which a server run cannot break, so coverage leaves them out.

## Tests

| test | level | outcome | duration |
|---|---|---|---:|
| `core/discovery#discovery-get-links-storageDescription` | MUST | passed | 492 ms |
| `core/discovery#discovery-link-storage-on-data-resource` | MUST | passed | 586 ms |
| `core/discovery#discovery-storage-description` | MUST | passed | 567 ms |
| `core/discovery#discovery-storage-description-default-media-type` | MUST | passed | 480 ms |
| `core/discovery#discovery-unauthorized-response-headers` | MUST | passed | 626 ms |
| `core/discovery#discovery-storage-root-is-container` | MUST | passed | 674 ms |
| `core/discovery#discovery-storage-description-ids-are-uris` | MUST | passed | 588 ms |
| `core/containers#getContainer` | MUST | passed | 756 ms |
| `core/containers#createContainer` | MUST | passed | 965 ms |
| `core/containers#createContainer-type-link` | SHOULD | passed | 556 ms |
| `core/containers#getContainer-containmentIntegrity` | MUST | passed | 1505 ms |
| `core/containers#container-total-items-accurate` | SHOULD | passed | 1553 ms |
| `core/containers#contained-resource-type-values` | MUST | passed | 2085 ms |
| `core/containers#contained-resource-format` | MUST | passed | 1231 ms |
| `core/containers#contained-resource-size-modified` | SHOULD | passed | 1583 ms |
| `core/containers#container-conneg` | MUST | passed | 1681 ms |
| `core/containers#container-conneg-vary` | SHOULD | passed | 574 ms |
| `core/containers#container-conneg-weighted` | MUST | passed | 393 ms |
| `core/containers#container-head-parity` | MUST | passed | 594 ms |
| `core/containers#delete-empty-container` | MUST | passed | 1143 ms |
| `core/containers#delete-non-empty-container-409` | MUST | passed | 1148 ms |
| `core/containers#delete-container-recursive` | MAY | passed | 1182 ms |
| `core/containers#delete-container-recursive-deep` | MAY | passed | 1505 ms |
| `core/containers#containment-hierarchy-consistent` | MUST | passed | 1533 ms |
| `core/containers#container-lws-profile-ld-json` | MUST | passed | 1232 ms |
| `core/containers#container-lws-profile-turtle` | MUST | passed | 1398 ms |
| `core/data_resources#createDataResource` | MUST | passed | 627 ms |
| `core/data_resources#createDataResource-type-link` | SHOULD | passed | 512 ms |
| `core/data_resources#create-post-twice-distinct` | SHOULD | passed | 892 ms |
| `core/data_resources#create-in-missing-container-rejected` | MUST | passed | 609 ms |
| `core/data_resources#create-in-missing-container-404` | SHOULD | passed | 541 ms |
| `core/data_resources#create-server-managed-links-protected` | MUST | passed | 1099 ms |
| `core/data_resources#readDataResource` | MUST | passed | 639 ms |
| `core/data_resources#data-resource-head-parity` | MUST | passed | 778 ms |
| `core/data_resources#data-resource-range-request` | MUST | passed | 767 ms |
| `core/data_resources#data-resource-range-unsatisfiable` | SHOULD | passed | 638 ms |
| `core/data_resources#data-resource-accept-ranges` | MAY | passed | 617 ms |
| `core/data_resources#updateDataResource` | MUST | passed | 984 ms |
| `core/data_resources#patch-json-patch-baseline` | MUST | passed | 990 ms |
| `core/data_resources#patch-json-patch-atomic` | MUST | passed | 833 ms |
| `core/data_resources#deleteDataResource` | MUST | passed | 1072 ms |
| `core/data_resources#post-to-non-container-405` | SHOULD | passed | 838 ms |
| `core/data_resources#error-problem-details` | SHOULD | passed | 539 ms |
| `core/conditional_requests#conditional-get-304` | SHOULD | passed | 818 ms |
| `core/conditional_requests#conditional-get-container-304` | SHOULD | passed | 730 ms |
| `core/conditional_requests#conditional-get-stale-validator-200` | MUST | passed | 1509 ms |
| `core/conditional_requests#conditional-put-stale-if-match-412` | MUST | passed | 1892 ms |
| `core/conditional_requests#conditional-delete-stale-if-match-412` | SHOULD | passed | 1371 ms |
| `core/conditional_requests#update-changes-strong-etag` | MUST | passed | 869 ms |
| `core/conditional_requests#delete-updates-parent-strong-etag` | MUST | passed | 1363 ms |
| `core/conditional_requests#conditional-get-if-modified-since-304` | SHOULD | passed | 1238 ms |
| `core/conditional_requests#conditional-get-if-unmodified-since-412` | SHOULD | passed | 1237 ms |
| `core/linksets#getLinkset` | MUST | passed | 1223 ms |
| `core/linksets#linkset-advertises-patch` | MUST | passed | 1270 ms |
| `core/linksets#linkset-conditional-412` | MUST | passed | 1005 ms |
| `core/linksets#linkset-put-405-when-unsupported` | MUST | inapplicable | 1002 ms |
| `core/linksets#linkset-removed-with-resource` | MUST | passed | 1344 ms |
| `core/linksets#linkset-ready-at-create` | MUST | passed | 923 ms |
| `core/linksets#linkset-up-not-redirected` | MUST | passed | 1041 ms |
| `core/linksets#linkset-patch-stays-linkset` | MUST | passed | 1055 ms |
| `core/linksets#linkset-patch-json-patch` | SHOULD | passed | 1192 ms |
| `core/linksets#linkset-patch-preserves-server-links` | MUST | passed | 1203 ms |
| `core/moving#discovery-move-capability` | MUST | passed | 615 ms |
| `core/moving#move-data-resource` | MUST | passed | 1349 ms |
| `core/moving#move-updates-container-etags` | MUST | passed | 1431 ms |
| `core/moving#move-keeps-identifier-content-and-links` | MUST | inapplicable | 1308 ms |
| `core/moving#move-invalid-destination-refused` | MUST | passed | 1696 ms |
| `core/moving#move-container` | MUST | passed | 1447 ms |
| `core/moving#move-container-into-itself-refused` | MUST | passed | 1355 ms |
| `core/moving#move-container-refused-without-container-support` | MUST | inapplicable | 644 ms |
| `core/moving#move-refused-without-capability` | MUST | inapplicable | 715 ms |
| `core/moving#move-needs-create-in-destination` | MUST | passed | 1790 ms |
| `core/moving#move-needs-delete-of-resource` | MUST | passed | 1581 ms |
| `core/moving#move-notification` | MUST | passed | 3275 ms |
| `core/storage_authorization#getContainer-private-unauthorized` | MUST | passed | 434 ms |
| `core/storage_authorization#protected-resource-metadata` | MUST | passed | 483 ms |
| `core/storage_authorization#protected-resource-metadata-data-resource` | MUST | passed | 948 ms |
| `core/storage_authorization#storage-root-same-origin` | MUST | passed | 536 ms |
| `core/storage_authorization#getContainer-authenticated-owner` | MUST | passed | 368 ms |
| `core/storage_authorization#createDataResource-unauthorized` | MUST | passed | 436 ms |
| `core/storage_authorization#updateDataResource-unauthorized` | MUST | passed | 623 ms |
| `core/storage_authorization#deleteDataResource-unauthorized` | MUST | passed | 708 ms |
| `core/storage_authorization#authz-non-owner-read-rejected` | MUST | passed | 398 ms |
| `core/storage_authorization#authz-non-owner-write-rejected` | MUST | passed | 994 ms |
| `core/storage_authorization#authz-non-owner-delete-rejected` | MUST | passed | 1046 ms |
| `core/storage_authorization#authz-expired-token-rejected` | MUST | passed | 672 ms |
| `core/storage_authorization#authz-token-bad-signature-rejected` | MUST | passed | 476 ms |
| `core/storage_authorization#authz-token-alg-none-rejected` | MUST | passed | 665 ms |
| `core/storage_authorization#authz-token-unknown-key-rejected` | MUST | passed | 1115 ms |
| `core/storage_authorization#authz-token-wrong-audience-rejected` | MUST | passed | 721 ms |
| `core/storage_authorization#authz-token-wrong-issuer-rejected` | MUST | passed | 443 ms |
| `core/storage_authorization#authz-token-not-yet-valid-rejected` | MUST | passed | 511 ms |
| `core/storage_authorization#authz-token-issued-in-future-rejected` | MUST | passed | 900 ms |
| `core/authorization_server#authz-server-metadata-well-known` | MUST | passed | 475 ms |
| `core/authorization_server#authz-metadata-subject-token-types` | SHOULD | passed | 292 ms |
| `core/authorization_server#authz-metadata-subject-token-types-are-uris` | MUST | passed | 612 ms |
| `core/authorization_server#authz-metadata-subject-identifier-types` | SHOULD | passed | 464 ms |
| `core/authorization_server#authz-token-exchange-valid` | MUST | passed | 872 ms |
| `core/authorization_server#authz-token-exchange-invalid-resource` | MUST | passed | 835 ms |
| `core/authorization_server#authz-token-exchange-missing-resource` | MUST | passed | 634 ms |
| `core/authorization_server#authz-token-exchange-missing-subject-token` | MUST | passed | 669 ms |
| `core/authorization_server#authz-issued-token-accepted-by-storage` | MUST | passed | 779 ms |
| `core/access_grants#access-grant-endpoint-is-container` | MUST | passed | 674 ms |
| `core/access_grants#access-grant-create` | MUST | passed | 783 ms |
| `core/access_grants#access-grant-revoke` | SHOULD | passed | 1058 ms |
| `core/access_grants#getContainer-public-read` | MUST | passed | 752 ms |
| `core/access_grants#readDataResource-public-read` | MUST | passed | 759 ms |
| `core/access_grants#access-grant-authenticated-agent` | MUST | passed | 860 ms |
| `core/access_grants#access-grant-extra-properties-accepted` | MAY | passed | 705 ms |
| `core/access_grants#access-grant-inbox-notified` | SHOULD | passed | 2430 ms |
| `core/access_grants#access-request-create` | MUST | passed | 434 ms |
| `core/access_grants#access-grant-document-shape` | MUST | passed | 613 ms |
| `core/access_grants#access-grant-incomplete-refused` | MUST | passed | 1115 ms |
| `core/access_grants#access-grant-constraints-all-satisfied` | MUST | passed | 641 ms |
| `core/access_grants#access-grant-left-operands-accepted` | MUST | passed | 839 ms |
| `core/access_grants#access-grant-constraint-format` | MUST | passed | 661 ms |
| `core/access_grants#access-grant-constraint-type` | MUST | passed | 550 ms |
| `core/access_grants#access-grant-constraint-client` | MUST | passed | 656 ms |
| `core/access_grants#container-listing-filtered-metadata` | MAY | passed | 711 ms |
| `core/notifications#notification-service-advertised` | MUST | passed | 378 ms |
| `core/notifications#subscription-create` | MUST | passed | 405 ms |
| `core/notifications#subscription-missing-type-refused` | MUST | passed | 344 ms |
| `core/notifications#subscription-unadvertised-type-refused` | MUST | passed | 339 ms |
| `core/notifications#subscription-missing-topic-refused` | MUST | passed | 339 ms |
| `core/notifications#subscription-unreadable-topic-refused` | MUST | passed | 635 ms |
| `core/notifications#subscription-after-revocation-refused` | MUST | passed | 603 ms |
| `core/notifications#notification-delivered-create` | MUST | passed | 2338 ms |
| `core/notifications#notification-delivered-update` | MUST | passed | 2482 ms |
| `core/notifications#notification-delivered-delete` | MUST | passed | 2505 ms |
| `core/notifications#notification-not-delivered-for-unreadable-resource` | MUST | passed | 2827 ms |
| `core/notifications#notification-stops-after-revocation` | MUST | passed | 4705 ms |
| `core/notifications#notification-actor-omitted` | SHOULD | passed | 2359 ms |
| `core/notifications#notification-delivered-in-subcontainer` | MUST | passed | 2390 ms |
| `core/notifications#notification-scope-data-resource-only` | MUST | passed | 2584 ms |
| `core/pagination#pagination-first-page` | MUST | inapplicable | 476 ms |
| `core/pagination#pagination-next-page` | MUST | inapplicable | 446 ms |
| `core/pagination#pagination-single-page` | MUST | passed | 437 ms |
| `core/pagination#pagination-last-page` | MUST | inapplicable | 371 ms |
| `core/pagination#pagination-totalitems-all-pages` | SHOULD | inapplicable | 359 ms |
| `auth/oidc/manifest#authn-oidc-valid-id-token` | MUST | passed | 330 ms |
| `auth/oidc/manifest#authn-oidc-expired-id-token` | MUST | passed | 148 ms |
| `auth/oidc/manifest#authn-oidc-alg-none` | MUST | passed | 97 ms |
| `auth/oidc/manifest#authn-oidc-bad-signature` | MUST | passed | 363 ms |
| `auth/oidc/manifest#authn-oidc-untrusted-issuer` | MUST | passed | 55 ms |
| `auth/oidc/manifest#authn-oidc-missing-azp` | MUST | passed | 84 ms |
| `auth/cid/manifest#authn-cid-valid-credential` | MUST | passed | 275 ms |
| `auth/cid/manifest#authn-cid-unknown-kid` | MUST | passed | 268 ms |
| `auth/cid/manifest#authn-cid-bad-signature` | MUST | passed | 104 ms |
| `auth/cid/manifest#authn-cid-expired` | MUST | passed | 86 ms |
| `auth/cid/manifest#authn-cid-alg-none` | MUST | passed | 183 ms |
| `auth/cid/manifest#authn-cid-claims-mismatch` | MUST | passed | 211 ms |
| `auth/cid/manifest#authn-cid-document-id-mismatch` | MUST | passed | 202 ms |
| `auth/cid/manifest#authn-cid-key-not-for-authentication` | MUST | passed | 190 ms |
| `auth/cid/manifest#authn-cid-key-revoked` | MUST | passed | 100 ms |
| `auth/cid/manifest#authn-cid-foreign-controller` | MUST | passed | 172 ms |
| `auth/cid/manifest#authn-cid-referenced-method` | MUST | passed | 107 ms |
| `auth/cid/manifest#authn-cid-didkey-valid-credential` | MUST | passed | 101 ms |
| `auth/cid/manifest#authn-cid-didkey-invalid-signature` | MUST | passed | 63 ms |
| `auth/cid/manifest#authn-cid-didkey-alg-none` | MUST | passed | 51 ms |
| `auth/cid/manifest#authn-cid-didkey-expired` | MUST | passed | 88 ms |
| `auth/cid/manifest#authn-cid-didkey-claims-mismatch` | MUST | passed | 100 ms |
| `auth/cid/manifest#authn-cid-didkey-audience-excludes-as` | MUST | passed | 100 ms |
| `auth/cid/manifest#authn-cid-didkey-missing-exp` | MUST | passed | 119 ms |
| `auth/cid/manifest#authn-cid-didkey-missing-iat` | MUST | passed | 113 ms |
| `auth/cid/manifest#authn-cid-didkey-missing-subject` | MUST | passed | 112 ms |
| `auth/cid/manifest#authn-cid-didkey-missing-issuer` | MUST | passed | 100 ms |
| `auth/cid/manifest#authn-cid-didkey-missing-client-id` | MUST | passed | 92 ms |
| `auth/saml/manifest#authn-saml-valid-assertion` | MUST | passed | 301 ms |
| `auth/saml/manifest#authn-saml-invalid-signature` | MUST | passed | 286 ms |
| `auth/saml/manifest#authn-saml-unsigned` | MUST | passed | 200 ms |
| `notifications/webhook/manifest#webhook-subscription-response` | MUST | passed | 119 ms |
| `notifications/webhook/manifest#webhook-subscription-expires-supported` | MUST | passed | 131 ms |
| `notifications/webhook/manifest#webhook-subscription-listed` | MUST | passed | 253 ms |
| `notifications/webhook/manifest#webhook-subscription-get-delete` | MUST | passed | 186 ms |
| `notifications/webhook/manifest#webhook-delivery-lws-json` | MUST | passed | 2162 ms |
| `notifications/webhook/manifest#webhook-delivery-signed` | SHOULD | passed | 2196 ms |
| `notifications/webhook/manifest#webhook-signature-components` | MUST | passed | 2198 ms |
| `notifications/webhook/manifest#webhook-signing-key-published` | MUST | passed | 2165 ms |
| `notifications/webhook/manifest#webhook-signature-verifies` | MUST | passed | 2180 ms |
| `notifications/webhook/manifest#webhook-delivery-retried` | MAY | passed | 3162 ms |
| `notifications/webhook/manifest#webhook-subscription-deactivated` | MAY | passed | 268 ms |
| `index/manifest#index-services-advertised` | MUST | passed | 103 ms |
| `index/manifest#type-index-lists-readable-types` | MUST | passed | 94 ms |
| `index/manifest#type-index-omits-unreadable-type` | MUST | passed | 92 ms |
| `index/manifest#type-index-not-shared` | MUST | passed | 35 ms |
| `index/manifest#type-search-by-type` | MUST | passed | 62 ms |
| `index/manifest#type-search-and-or` | MUST | passed | 71 ms |
| `index/manifest#type-search-native-classes` | MUST | passed | 51 ms |
| `index/manifest#type-search-no-match` | MUST | passed | 42 ms |
| `index/manifest#type-search-duplicate-groups` | MUST | passed | 43 ms |
| `index/manifest#type-search-at-members-ignored` | MUST | passed | 68 ms |
| `index/manifest#type-search-empty-key-absent` | MUST | passed | 51 ms |
| `index/manifest#type-search-empty-group-rejected` | MUST | passed | 30 ms |
| `index/manifest#type-search-type-not-array-rejected` | MUST | passed | 31 ms |
| `index/manifest#type-search-bad-element-rejected` | MUST | passed | 38 ms |
| `index/manifest#type-search-malformed-json-rejected` | MUST | passed | 31 ms |
| `index/manifest#type-search-relative-iri-rejected` | MUST | passed | 39 ms |
| `index/manifest#type-search-missing-content-type-rejected` | MUST | passed | 43 ms |
| `index/manifest#type-search-unsupported-format-rejected` | MUST | passed | 43 ms |
| `index/manifest#type-search-unsupported-format-accept-query` | SHOULD | passed | 47 ms |
| `index/manifest#type-search-accept-query-advertised` | SHOULD | passed | 44 ms |
| `index/manifest#type-search-not-acceptable` | MUST | passed | 55 ms |
| `index/manifest#type-search-unindexed-relation` | MUST | passed | 102 ms |
| `index/manifest#type-search-structural-relation-not-indexed` | MUST | passed | 118 ms |
| `index/manifest#type-search-authorization-filtered` | MUST | passed | 424 ms |
| `index/manifest#type-search-revoked-not-shown` | MUST | passed | 440 ms |
| `index/manifest#type-search-not-shared` | MUST | passed | 239 ms |
| `index/manifest#type-search-type-from-link-header` | SHOULD | passed | 259 ms |
| `index/manifest#type-search-type-from-content` | MAY | passed | 302 ms |
| `index/manifest#type-search-content-types-identical` | MUST | passed | 631 ms |
| `index/manifest#type-search-reflects-update` | SHOULD | passed | 526 ms |
| `index/manifest#type-search-reflects-delete` | SHOULD | passed | 453 ms |
| `index/manifest#type-search-vary-accept` | MUST | passed | 355 ms |
| `index/manifest#type-search-safe` | MAY | passed | 493 ms |
| `index/manifest#type-search-next-page` | MUST | inapplicable | 472 ms |
| `index/manifest#type-search-relation-filter` | MAY | passed | 402 ms |
| `index/manifest#type-search-relation-cnf` | MAY | passed | 503 ms |
| `index/manifest#type-search-relation-from-link-header` | SHOULD | passed | 399 ms |
| `index/manifest#type-search-too-complex` | MUST | passed | 189 ms |
| `index/manifest#type-search-unrecognized-page-link` | MUST | passed | 166 ms |
| `index/manifest#type-search-content-location-protected` | MUST | passed | 191 ms |

### Detail

**`core/linksets#linkset-put-405-when-unsupported`** — inapplicable

```
core/linksets#linkset-put-405-when-unsupported - inapplicable [MUST] (1002 ms)
  inapplicable: precondition 'the linkset does not advertise PUT (otherwise this test does not apply)' does not hold: header Allow matches expected matches /(?i)^(?!.*\bPUT\b)/, got GET, HEAD, OPTIONS, PATCH, PUT
  step 'the linkset does not advertise PUT (otherwise this test does not apply)':
    FAILED header Allow matches
      expected: matches /(?i)^(?!.*\bPUT\b)/
      actual:   GET, HEAD, OPTIONS, PATCH, PUT
    exchange: GET http://127.0.0.1:41945/touchstone-run-cdc3b6df/linkset-put-405-when-unsupported/res1792622369?linkset -> 200
    response body: {"linkset":[{"anchor":"http://127.0.0.1:41945/touchstone-run-cdc3b6df/linkset-put-405-when-unsupported/res1792622369","up":[{"href":"http://127.0.0.1:41945/touchstone-run-cdc3b6df/linkset-put-405-when-unsupported/"}],"type":[{"href":"https://www.w3.org/ns/lws#DataResource"}],"https://www.w3.org/ns/lws#storage":[{"href":"http://127.0.0.1:41945/.well-known/lws-storage"}]}]}
```

**`core/moving#move-keeps-identifier-content-and-links`** — inapplicable

```
core/moving#move-keeps-identifier-content-and-links - inapplicable [MUST] (1308 ms)
  inapplicable: precondition 'the storage's MoveResource says it preserves identifiers (otherwise this test does not apply)' does not hold: json /capability some expected some element satisfies [{"pointer":"/type","hasValue":"MoveResource"},{"pointer":"/preservesIdentifier","equals":true}], got [{"type":"MoveResource","appliesTo":["DataResource","Container"],"preservesIdentifier":false}]
  step 'the storage's MoveResource says it preserves identifiers (otherwise this test does not apply)':
    FAILED json /capability some
      expected: some element satisfies [{"pointer":"/type","hasValue":"MoveResource"},{"pointer":"/preservesIdentifier","equals":true}]
      actual:   [{"type":"MoveResource","appliesTo":["DataResource","Container"],"preservesIdentifier":false}]
    exchange: GET http://127.0.0.1:41945/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:41945/.well-known/lws-storage","type":"Storage","verificationMethod":[{"id":"http://127.0.0.1:41945/.well-known/lws-storage#notification-key-161ea634","type":"JsonWebKey","controller":"http://127.0.0.1:41945/.well-known/lws-storage","publicKeyJwk":{"kty":"OKP","crv":"Ed25519","x":"0Q7PgQN7PUOJspDsxBWgpeIVYftGjbmr8GuT_4HvrQs"}}],"authentication":["http://127.0.0.1:41945/.well-known/lws-storage#notification-key-161ea634"],"capability":[{"type":"MoveResource","appliesTo":["DataResource","Container"],"preservesIdentifier":false}],"service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:41945/"},{"type":"NotificationService","serviceEndpoint":"http://127.0.0.1:41945/.well-known/lws-subscriptions/","subscriptionType":["WebhookSubscription"]},{"type":"TypeIndexService","serviceEndpoint":"http://127.0.0.1:41945/.well-known/lws-type-index"},{"type":"TypeSearchService","serviceEndpoint":"http://127.0.0.1:41945/.well-known/lws-type-search","https://github.com/danbri/factoidal/issues/922#unstableResultsResource":"anticipatory and unstable: a QUERY answer carries Content-Location (RFC 10008 section 2.3) naming a results resource that lws10-index does not define; likely to change"},{"type":"AccessRequestService","serviceEndpoint":"http://127.0.0.1:41945/.well-known/lws-access-requests/","conformsTo":["https://www.w3.org/ns/lws#AccessProfile"]},{"type":"AccessGrantService","serviceEndpoint":"http://127.0.0.1:41945/.well-known/lws-access-grants/","conformsTo":["https://www.w3.org/ns/lws#AccessProfile"]}]}
```

**`core/moving#move-container-refused-without-container-support`** — inapplicable

```
core/moving#move-container-refused-without-container-support - inapplicable [MUST] (644 ms)
  inapplicable: precondition 'the storage moves data resources but not containers (otherwise this test does not apply)' does not hold: json /capability some expected some element satisfies [{"pointer":"/type","hasValue":"MoveResource"},{"pointer":"/appliesTo","optional":true,"none":[{"pointer":"","matches":"^(https://www\\.w3\\.org/ns/lws#)?Container$"}]}], got [{"type":"MoveResource","appliesTo":["DataResource","Container"],"preservesIdentifier":false}]
  step 'the storage moves data resources but not containers (otherwise this test does not apply)':
    FAILED json /capability some
      expected: some element satisfies [{"pointer":"/type","hasValue":"MoveResource"},{"pointer":"/appliesTo","optional":true,"none":[{"pointer":"","matches":"^(https://www\\.w3\\.org/ns/lws#)?Container$"}]}]
      actual:   [{"type":"MoveResource","appliesTo":["DataResource","Container"],"preservesIdentifier":false}]
    exchange: GET http://127.0.0.1:41945/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:41945/.well-known/lws-storage","type":"Storage","verificationMethod":[{"id":"http://127.0.0.1:41945/.well-known/lws-storage#notification-key-161ea634","type":"JsonWebKey","controller":"http://127.0.0.1:41945/.well-known/lws-storage","publicKeyJwk":{"kty":"OKP","crv":"Ed25519","x":"0Q7PgQN7PUOJspDsxBWgpeIVYftGjbmr8GuT_4HvrQs"}}],"authentication":["http://127.0.0.1:41945/.well-known/lws-storage#notification-key-161ea634"],"capability":[{"type":"MoveResource","appliesTo":["DataResource","Container"],"preservesIdentifier":false}],"service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:41945/"},{"type":"NotificationService","serviceEndpoint":"http://127.0.0.1:41945/.well-known/lws-subscriptions/","subscriptionType":["WebhookSubscription"]},{"type":"TypeIndexService","serviceEndpoint":"http://127.0.0.1:41945/.well-known/lws-type-index"},{"type":"TypeSearchService","serviceEndpoint":"http://127.0.0.1:41945/.well-known/lws-type-search","https://github.com/danbri/factoidal/issues/922#unstableResultsResource":"anticipatory and unstable: a QUERY answer carries Content-Location (RFC 10008 section 2.3) naming a results resource that lws10-index does not define; likely to change"},{"type":"AccessRequestService","serviceEndpoint":"http://127.0.0.1:41945/.well-known/lws-access-requests/","conformsTo":["https://www.w3.org/ns/lws#AccessProfile"]},{"type":"AccessGrantService","serviceEndpoint":"http://127.0.0.1:41945/.well-known/lws-access-grants/","conformsTo":["https://www.w3.org/ns/lws#AccessProfile"]}]}
```

**`core/moving#move-refused-without-capability`** — inapplicable

```
core/moving#move-refused-without-capability - inapplicable [MUST] (715 ms)
  inapplicable: precondition 'the storage describes no MoveResource capability (otherwise this test does not apply)' does not hold: json /capability none expected none element satisfies [{"pointer":"/type","hasValue":"MoveResource"}], got [{"type":"MoveResource","appliesTo":["DataResource","Container"],"preservesIdentifier":false}]
  step 'the storage describes no MoveResource capability (otherwise this test does not apply)':
    FAILED json /capability none
      expected: none element satisfies [{"pointer":"/type","hasValue":"MoveResource"}]
      actual:   [{"type":"MoveResource","appliesTo":["DataResource","Container"],"preservesIdentifier":false}]
    exchange: GET http://127.0.0.1:41945/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:41945/.well-known/lws-storage","type":"Storage","verificationMethod":[{"id":"http://127.0.0.1:41945/.well-known/lws-storage#notification-key-161ea634","type":"JsonWebKey","controller":"http://127.0.0.1:41945/.well-known/lws-storage","publicKeyJwk":{"kty":"OKP","crv":"Ed25519","x":"0Q7PgQN7PUOJspDsxBWgpeIVYftGjbmr8GuT_4HvrQs"}}],"authentication":["http://127.0.0.1:41945/.well-known/lws-storage#notification-key-161ea634"],"capability":[{"type":"MoveResource","appliesTo":["DataResource","Container"],"preservesIdentifier":false}],"service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:41945/"},{"type":"NotificationService","serviceEndpoint":"http://127.0.0.1:41945/.well-known/lws-subscriptions/","subscriptionType":["WebhookSubscription"]},{"type":"TypeIndexService","serviceEndpoint":"http://127.0.0.1:41945/.well-known/lws-type-index"},{"type":"TypeSearchService","serviceEndpoint":"http://127.0.0.1:41945/.well-known/lws-type-search","https://github.com/danbri/factoidal/issues/922#unstableResultsResource":"anticipatory and unstable: a QUERY answer carries Content-Location (RFC 10008 section 2.3) naming a results resource that lws10-index does not define; likely to change"},{"type":"AccessRequestService","serviceEndpoint":"http://127.0.0.1:41945/.well-known/lws-access-requests/","conformsTo":["https://www.w3.org/ns/lws#AccessProfile"]},{"type":"AccessGrantService","serviceEndpoint":"http://127.0.0.1:41945/.well-known/lws-access-grants/","conformsTo":["https://www.w3.org/ns/lws#AccessProfile"]}]}
```

**`core/pagination#pagination-first-page`** — inapplicable

```
core/pagination#pagination-first-page - inapplicable [MUST] (476 ms)
  inapplicable: precondition 'the server splits a five-member container into pages (otherwise this test does not apply)' does not hold: Link rel="next" expected a matching link, got <http://www.w3.org/ns/ldp#BasicContainer>; rel="type", <http://www.w3.org/ns/ldp#Container>; rel="type", <http://www.w3.org/ns/ldp#Resource>; rel="type", </touchstone-run-cdc3b6df/pagination-first-page/paged/.acl>; rel="acl", </touchstone-run-cdc3b6df/pagination-first-page/paged/.meta>; rel="describedby", <http://127.0.0.1:41945/.well-known/solid>; rel="http://www.w3.org/ns/solid/terms#storageDescription", </touchstone-run-cdc3b6df/pagination-first-page/paged/?linkset>; rel="linkset"; type="application/linkset+json", </touchstone-run-cdc3b6df/pagination-first-page/>; rel="up", <https://www.w3.org/ns/lws#Container>; rel="type", <http://127.0.0.1:41945/.well-known/lws-storage>; rel="https://www.w3.org/ns/lws#storage", </touchstone-run-cdc3b6df/pagination-first-page/paged/?page=1>; rel="first", </touchstone-run-cdc3b6df/pagination-first-page/paged/?page=1>; rel="last"
  step 'the server splits a five-member container into pages (otherwise this test does not apply)':
    FAILED Link rel="next"
      expected: a matching link
      actual:   <http://www.w3.org/ns/ldp#BasicContainer>; rel="type", <http://www.w3.org/ns/ldp#Container>; rel="type", <http://www.w3.org/ns/ldp#Resource>; rel="type", </touchstone-run-cdc3b6df/pagination-first-page/paged/.acl>; rel="acl", </touchstone-run-cdc3b6df/pagination-first-page/paged/.meta>; rel="describedby", <http://127.0.0.1:41945/.well-known/solid>; rel="http://www.w3.org/ns/solid/terms#storageDescription", </touchstone-run-cdc3b6df/pagination-first-page/paged/?linkset>; rel="linkset"; type="application/linkset+json", </touchstone-run-cdc3b6df/pagination-first-page/>; rel="up", <https://www.w3.org/ns/lws#Container>; rel="type", <http://127.0.0.1:41945/.well-known/lws-storage>; rel="https://www.w3.org/ns/lws#storage", </touchstone-run-cdc3b6df/pagination-first-page/paged/?page=1>; rel="first", </touchstone-run-cdc3b6df/pagination-first-page/paged/?page=1>; rel="last"
    exchange: GET http://127.0.0.1:41945/touchstone-run-cdc3b6df/pagination-first-page/paged/ -> 200
    response body: {"@context":"https://www.w3.org/ns/lws/v1","id":"http://127.0.0.1:41945/touchstone-run-cdc3b6df/pagination-first-page/paged/","type":"Container","totalItems":5,"items":[{"id":"http://127.0.0.1:41945/touchstone-run-cdc3b6df/pagination-first-page/paged/res1792622373","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T22:39:33Z"},{"id":"http://127.0.0.1:41945/touchstone-run-cdc3b6df/pagination-first-page/paged/res1792622373-1","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T22:39:33Z"},{"id":"http://127.0.0.1:41945/touchstone-run-cdc3b6df/pagination-first-page/paged/res1792622373-2","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T22:39:33Z"},{"id":"http://127.0.0.1:41945/touchstone-run-cdc3b6df/pagination-first-page/paged/res1792622373-3","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T22:39:33Z"},{"id":"http://127.0.0.1:41945/touchstone-run-cdc3b6df/pagination-first-page/paged/res1792622373-4","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T22:39:33Z"}]}
```

**`core/pagination#pagination-next-page`** — inapplicable

```
core/pagination#pagination-next-page - inapplicable [MUST] (446 ms)
  inapplicable: precondition 'the server splits a five-member container into pages (otherwise this test does not apply)' does not hold: Link rel="next" expected a matching link, got <http://www.w3.org/ns/ldp#BasicContainer>; rel="type", <http://www.w3.org/ns/ldp#Container>; rel="type", <http://www.w3.org/ns/ldp#Resource>; rel="type", </touchstone-run-cdc3b6df/pagination-next-page/paged/.acl>; rel="acl", </touchstone-run-cdc3b6df/pagination-next-page/paged/.meta>; rel="describedby", <http://127.0.0.1:41945/.well-known/solid>; rel="http://www.w3.org/ns/solid/terms#storageDescription", </touchstone-run-cdc3b6df/pagination-next-page/paged/?linkset>; rel="linkset"; type="application/linkset+json", </touchstone-run-cdc3b6df/pagination-next-page/>; rel="up", <https://www.w3.org/ns/lws#Container>; rel="type", <http://127.0.0.1:41945/.well-known/lws-storage>; rel="https://www.w3.org/ns/lws#storage", </touchstone-run-cdc3b6df/pagination-next-page/paged/?page=1>; rel="first", </touchstone-run-cdc3b6df/pagination-next-page/paged/?page=1>; rel="last"
  step 'the server splits a five-member container into pages (otherwise this test does not apply)':
    FAILED Link rel="next"
      expected: a matching link
      actual:   <http://www.w3.org/ns/ldp#BasicContainer>; rel="type", <http://www.w3.org/ns/ldp#Container>; rel="type", <http://www.w3.org/ns/ldp#Resource>; rel="type", </touchstone-run-cdc3b6df/pagination-next-page/paged/.acl>; rel="acl", </touchstone-run-cdc3b6df/pagination-next-page/paged/.meta>; rel="describedby", <http://127.0.0.1:41945/.well-known/solid>; rel="http://www.w3.org/ns/solid/terms#storageDescription", </touchstone-run-cdc3b6df/pagination-next-page/paged/?linkset>; rel="linkset"; type="application/linkset+json", </touchstone-run-cdc3b6df/pagination-next-page/>; rel="up", <https://www.w3.org/ns/lws#Container>; rel="type", <http://127.0.0.1:41945/.well-known/lws-storage>; rel="https://www.w3.org/ns/lws#storage", </touchstone-run-cdc3b6df/pagination-next-page/paged/?page=1>; rel="first", </touchstone-run-cdc3b6df/pagination-next-page/paged/?page=1>; rel="last"
    exchange: GET http://127.0.0.1:41945/touchstone-run-cdc3b6df/pagination-next-page/paged/ -> 200
    response body: {"@context":"https://www.w3.org/ns/lws/v1","id":"http://127.0.0.1:41945/touchstone-run-cdc3b6df/pagination-next-page/paged/","type":"Container","totalItems":5,"items":[{"id":"http://127.0.0.1:41945/touchstone-run-cdc3b6df/pagination-next-page/paged/res1792622373","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T22:39:33Z"},{"id":"http://127.0.0.1:41945/touchstone-run-cdc3b6df/pagination-next-page/paged/res1792622373-1","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T22:39:33Z"},{"id":"http://127.0.0.1:41945/touchstone-run-cdc3b6df/pagination-next-page/paged/res1792622373-2","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T22:39:33Z"},{"id":"http://127.0.0.1:41945/touchstone-run-cdc3b6df/pagination-next-page/paged/res1792622373-3","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T22:39:33Z"},{"id":"http://127.0.0.1:41945/touchstone-run-cdc3b6df/pagination-next-page/paged/res1792622373-4","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T22:39:33Z"}]}
```

**`core/pagination#pagination-last-page`** — inapplicable

```
core/pagination#pagination-last-page - inapplicable [MUST] (371 ms)
  inapplicable: precondition 'the server splits a five-member container into pages (otherwise this test does not apply)' does not hold: Link rel="next" expected a matching link, got <http://www.w3.org/ns/ldp#BasicContainer>; rel="type", <http://www.w3.org/ns/ldp#Container>; rel="type", <http://www.w3.org/ns/ldp#Resource>; rel="type", </touchstone-run-cdc3b6df/pagination-last-page/paged/.acl>; rel="acl", </touchstone-run-cdc3b6df/pagination-last-page/paged/.meta>; rel="describedby", <http://127.0.0.1:41945/.well-known/solid>; rel="http://www.w3.org/ns/solid/terms#storageDescription", </touchstone-run-cdc3b6df/pagination-last-page/paged/?linkset>; rel="linkset"; type="application/linkset+json", </touchstone-run-cdc3b6df/pagination-last-page/>; rel="up", <https://www.w3.org/ns/lws#Container>; rel="type", <http://127.0.0.1:41945/.well-known/lws-storage>; rel="https://www.w3.org/ns/lws#storage", </touchstone-run-cdc3b6df/pagination-last-page/paged/?page=1>; rel="first", </touchstone-run-cdc3b6df/pagination-last-page/paged/?page=1>; rel="last"
  step 'the server splits a five-member container into pages (otherwise this test does not apply)':
    FAILED Link rel="next"
      expected: a matching link
      actual:   <http://www.w3.org/ns/ldp#BasicContainer>; rel="type", <http://www.w3.org/ns/ldp#Container>; rel="type", <http://www.w3.org/ns/ldp#Resource>; rel="type", </touchstone-run-cdc3b6df/pagination-last-page/paged/.acl>; rel="acl", </touchstone-run-cdc3b6df/pagination-last-page/paged/.meta>; rel="describedby", <http://127.0.0.1:41945/.well-known/solid>; rel="http://www.w3.org/ns/solid/terms#storageDescription", </touchstone-run-cdc3b6df/pagination-last-page/paged/?linkset>; rel="linkset"; type="application/linkset+json", </touchstone-run-cdc3b6df/pagination-last-page/>; rel="up", <https://www.w3.org/ns/lws#Container>; rel="type", <http://127.0.0.1:41945/.well-known/lws-storage>; rel="https://www.w3.org/ns/lws#storage", </touchstone-run-cdc3b6df/pagination-last-page/paged/?page=1>; rel="first", </touchstone-run-cdc3b6df/pagination-last-page/paged/?page=1>; rel="last"
    exchange: GET http://127.0.0.1:41945/touchstone-run-cdc3b6df/pagination-last-page/paged/ -> 200
    response body: {"@context":"https://www.w3.org/ns/lws/v1","id":"http://127.0.0.1:41945/touchstone-run-cdc3b6df/pagination-last-page/paged/","type":"Container","totalItems":5,"items":[{"id":"http://127.0.0.1:41945/touchstone-run-cdc3b6df/pagination-last-page/paged/res1792622373","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T22:39:33Z"},{"id":"http://127.0.0.1:41945/touchstone-run-cdc3b6df/pagination-last-page/paged/res1792622373-1","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T22:39:33Z"},{"id":"http://127.0.0.1:41945/touchstone-run-cdc3b6df/pagination-last-page/paged/res1792622373-2","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T22:39:33Z"},{"id":"http://127.0.0.1:41945/touchstone-run-cdc3b6df/pagination-last-page/paged/res1792622373-3","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T22:39:33Z"},{"id":"http://127.0.0.1:41945/touchstone-run-cdc3b6df/pagination-last-page/paged/res1792622373-4","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T22:39:33Z"}]}
```

**`core/pagination#pagination-totalitems-all-pages`** — inapplicable

```
core/pagination#pagination-totalitems-all-pages - inapplicable [SHOULD] (359 ms)
  inapplicable: precondition 'the server splits a five-member container into pages (otherwise this test does not apply)' does not hold: Link rel="next" expected a matching link, got <http://www.w3.org/ns/ldp#BasicContainer>; rel="type", <http://www.w3.org/ns/ldp#Container>; rel="type", <http://www.w3.org/ns/ldp#Resource>; rel="type", </touchstone-run-cdc3b6df/pagination-totalitems-all-pages/paged/.acl>; rel="acl", </touchstone-run-cdc3b6df/pagination-totalitems-all-pages/paged/.meta>; rel="describedby", <http://127.0.0.1:41945/.well-known/solid>; rel="http://www.w3.org/ns/solid/terms#storageDescription", </touchstone-run-cdc3b6df/pagination-totalitems-all-pages/paged/?linkset>; rel="linkset"; type="application/linkset+json", </touchstone-run-cdc3b6df/pagination-totalitems-all-pages/>; rel="up", <https://www.w3.org/ns/lws#Container>; rel="type", <http://127.0.0.1:41945/.well-known/lws-storage>; rel="https://www.w3.org/ns/lws#storage", </touchstone-run-cdc3b6df/pagination-totalitems-all-pages/paged/?page=1>; rel="first", </touchstone-run-cdc3b6df/pagination-totalitems-all-pages/paged/?page=1>; rel="last"
  step 'the server splits a five-member container into pages (otherwise this test does not apply)':
    FAILED Link rel="next"
      expected: a matching link
      actual:   <http://www.w3.org/ns/ldp#BasicContainer>; rel="type", <http://www.w3.org/ns/ldp#Container>; rel="type", <http://www.w3.org/ns/ldp#Resource>; rel="type", </touchstone-run-cdc3b6df/pagination-totalitems-all-pages/paged/.acl>; rel="acl", </touchstone-run-cdc3b6df/pagination-totalitems-all-pages/paged/.meta>; rel="describedby", <http://127.0.0.1:41945/.well-known/solid>; rel="http://www.w3.org/ns/solid/terms#storageDescription", </touchstone-run-cdc3b6df/pagination-totalitems-all-pages/paged/?linkset>; rel="linkset"; type="application/linkset+json", </touchstone-run-cdc3b6df/pagination-totalitems-all-pages/>; rel="up", <https://www.w3.org/ns/lws#Container>; rel="type", <http://127.0.0.1:41945/.well-known/lws-storage>; rel="https://www.w3.org/ns/lws#storage", </touchstone-run-cdc3b6df/pagination-totalitems-all-pages/paged/?page=1>; rel="first", </touchstone-run-cdc3b6df/pagination-totalitems-all-pages/paged/?page=1>; rel="last"
    exchange: GET http://127.0.0.1:41945/touchstone-run-cdc3b6df/pagination-totalitems-all-pages/paged/ -> 200
    response body: {"@context":"https://www.w3.org/ns/lws/v1","id":"http://127.0.0.1:41945/touchstone-run-cdc3b6df/pagination-totalitems-all-pages/paged/","type":"Container","totalItems":5,"items":[{"id":"http://127.0.0.1:41945/touchstone-run-cdc3b6df/pagination-totalitems-all-pages/paged/res1792622373","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T22:39:33Z"},{"id":"http://127.0.0.1:41945/touchstone-run-cdc3b6df/pagination-totalitems-all-pages/paged/res1792622373-1","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T22:39:33Z"},{"id":"http://127.0.0.1:41945/touchstone-run-cdc3b6df/pagination-totalitems-all-pages/paged/res1792622373-2","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T22:39:33Z"},{"id":"http://127.0.0.1:41945/touchstone-run-cdc3b6df/pagination-totalitems-all-pages/paged/res1792622373-3","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T22:39:33Z"},{"id":"http://127.0.0.1:41945/touchstone-run-cdc3b6df/pagination-totalitems-all-pages/paged/res1792622373-4","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T22:39:33Z"}]}
```

**`index/manifest#type-search-next-page`** — inapplicable

```
index/manifest#type-search-next-page - inapplicable [MUST] (472 ms)
  inapplicable: precondition 'the search on Alpha spans pages (otherwise this test does not apply)' does not hold: Link rel="next" expected a matching link, got <http://127.0.0.1:41945/.well-known/lws-type-search?q=eyJ0eXBlIjpbWyJodHRwOi8vMTI3LjAuMC4xOjQxOTQ1L3RvdWNoc3RvbmUtcnVuLWNkYzNiNmRmL3R5cGUtc2VhcmNoLW5leHQtcGFnZS8jQWxwaGEiXV19&page=1>; rel="first", <http://127.0.0.1:41945/.well-known/lws-type-search?q=eyJ0eXBlIjpbWyJodHRwOi8vMTI3LjAuMC4xOjQxOTQ1L3RvdWNoc3RvbmUtcnVuLWNkYzNiNmRmL3R5cGUtc2VhcmNoLW5leHQtcGFnZS8jQWxwaGEiXV19&page=1>; rel="last", <http://127.0.0.1:41945/.well-known/lws-storage>; rel="https://www.w3.org/ns/lws#storage"
  step 'the search on Alpha spans pages (otherwise this test does not apply)':
    FAILED Link rel="next"
      expected: a matching link
      actual:   <http://127.0.0.1:41945/.well-known/lws-type-search?q=eyJ0eXBlIjpbWyJodHRwOi8vMTI3LjAuMC4xOjQxOTQ1L3RvdWNoc3RvbmUtcnVuLWNkYzNiNmRmL3R5cGUtc2VhcmNoLW5leHQtcGFnZS8jQWxwaGEiXV19&page=1>; rel="first", <http://127.0.0.1:41945/.well-known/lws-type-search?q=eyJ0eXBlIjpbWyJodHRwOi8vMTI3LjAuMC4xOjQxOTQ1L3RvdWNoc3RvbmUtcnVuLWNkYzNiNmRmL3R5cGUtc2VhcmNoLW5leHQtcGFnZS8jQWxwaGEiXV19&page=1>; rel="last", <http://127.0.0.1:41945/.well-known/lws-storage>; rel="https://www.w3.org/ns/lws#storage"
    exchange: QUERY http://127.0.0.1:41945/.well-known/lws-type-search -> 200
    response body: {"@context":"https://www.w3.org/ns/lws/v1","type":"ContainerPage","totalItems":5,"items":[{"id":"http://127.0.0.1:41945/touchstone-run-cdc3b6df/type-search-next-page/res1792622376","type":["DataResource","http://127.0.0.1:41945/touchstone-run-cdc3b6df/type-search-next-page/#Alpha"],"format":"text/turtle","size":84,"modified":"2026-10-21T22:39:36Z"},{"id":"http://127.0.0.1:41945/touchstone-run-cdc3b6df/type-search-next-page/res1792622376-1","type":["DataResource","http://127.0.0.1:41945/touchstone-run-cdc3b6df/type-search-next-page/#Alpha"],"format":"text/turtle","size":84,"modified":"2026-10-21T22:39:36Z"},{"id":"http://127.0.0.1:41945/touchstone-run-cdc3b6df/type-search-next-page/res1792622376-2","type":["DataResource","http://127.0.0.1:41945/touchstone-run-cdc3b6df/type-search-next-page/#Alpha"],"format":"text/turtle","size":84,"modified":"2026-10-21T22:39:36Z"},{"id":"http://127.0.0.1:41945/touchstone-run-cdc3b6df/type-search-next-page/res1792622376-3","type":["DataResource","http://127.0.0.1:41945/touchstone-run-cdc3b6df/type-search-next-page/#Alpha"],"format":"text/turtle","size":84,"modified":"2026-10-21T22:39:36Z"},{"id":"http://127.0.0.1:41945/touchstone-run-cdc3b6df/type-search-next-page/res1792622376-4","type":["DataResource","http://127.0.0.1:41945/touchstone-run-cdc3b6df/type-search-next-page/#Alpha","http://127.0.0.1:41945/touchstone-run-cdc3b6df/type-search-next-page/#Epsilon"],"format":"text/turtle","size":165,"modified":"2026-10-21T22:39:36Z"}]}
```

## Requirement matrix

| requirement | level | result | tests |
|---|---|---|---:|
| [`id-token-alg-not-none`](https://www.w3.org/TR/lws10-authn-openid/#serialization) | MUST | PASS | 1 |
| [`id-token-aud-claim`](https://www.w3.org/TR/lws10-authn-openid/#serialization) | MUST | PASS | 1 |
| [`id-token-azp-claim`](https://www.w3.org/TR/lws10-authn-openid/#serialization) | MUST | PASS | 2 |
| [`id-token-iss-claim`](https://www.w3.org/TR/lws10-authn-openid/#serialization) | MUST | PASS | 1 |
| [`id-token-sub-claim`](https://www.w3.org/TR/lws10-authn-openid/#serialization) | MUST | PASS | 1 |
| [`id-token-token-type-uri`](https://www.w3.org/TR/lws10-authn-openid/#token-type) | MUST | PASS | 1 |
| [`validation-dereference-subject-cid`](https://www.w3.org/TR/lws10-authn-openid/#validation) | MUST | PASS | 2 |
| [`validation-locate-issuer-service-and-verify`](https://www.w3.org/TR/lws10-authn-openid/#validation) | MUST | PASS | 4 |
| [`audience-restriction`](https://www.w3.org/TR/lws10-authn-saml/#serialization) | MUST | PASS | 1 |
| [`issuer-assertion`](https://www.w3.org/TR/lws10-authn-saml/#serialization) | MUST | PASS | 1 |
| [`nameid-subject`](https://www.w3.org/TR/lws10-authn-saml/#serialization) | MUST | PASS | 1 |
| [`recipient-client-id`](https://www.w3.org/TR/lws10-authn-saml/#serialization) | MUST | PASS | 1 |
| [`signed-and-required-assertions`](https://www.w3.org/TR/lws10-authn-saml/#serialization) | MUST | PASS | 2 |
| [`token-type-saml2`](https://www.w3.org/TR/lws10-authn-saml/#token-type) | MUST | PASS | 1 |
| [`validation-signature`](https://www.w3.org/TR/lws10-authn-saml/#validation) | MUST | PASS | 2 |
| [`alg-not-none`](https://www.w3.org/TR/lws10-authn-ssi-cid/#serialization) | MUST | PASS | 2 |
| [`aud-includes-as`](https://www.w3.org/TR/lws10-authn-ssi-cid/#serialization) | MUST | PASS | 3 |
| [`client-id-claim`](https://www.w3.org/TR/lws10-authn-ssi-cid/#serialization) | MUST | PASS | 2 |
| [`exp-claim`](https://www.w3.org/TR/lws10-authn-ssi-cid/#serialization) | MUST | PASS | 3 |
| [`iat-claim`](https://www.w3.org/TR/lws10-authn-ssi-cid/#serialization) | MUST | PASS | 3 |
| [`iss-claim`](https://www.w3.org/TR/lws10-authn-ssi-cid/#serialization) | MUST | PASS | 2 |
| [`sub-claim`](https://www.w3.org/TR/lws10-authn-ssi-cid/#serialization) | MUST | PASS | 2 |
| [`sub-iss-client-same-uri`](https://www.w3.org/TR/lws10-authn-ssi-cid/#serialization) | MUST | PASS | 7 |
| [`token-type-jwt`](https://www.w3.org/TR/lws10-authn-ssi-cid/#token-type) | MUST | PASS | 2 |
| [`validation-all-claims`](https://www.w3.org/TR/lws10-authn-ssi-cid/#validation) | MUST | PASS | 8 |
| [`validation-dereference-sub-cid`](https://www.w3.org/TR/lws10-authn-ssi-cid/#validation) | MUST | PASS | 4 |
| [`validation-exp-in-future`](https://www.w3.org/TR/lws10-authn-ssi-cid/#validation) | MUST | PASS | 4 |
| [`validation-kid-verification-method`](https://www.w3.org/TR/lws10-authn-ssi-cid/#validation) | MUST | PASS | 9 |
| [`validation-reject-alg-none`](https://www.w3.org/TR/lws10-authn-ssi-cid/#validation) | MUST | PASS | 1 |
| [`access-access-collection`](https://www.w3.org/TR/lws10-core/#access-property) | MUST | PASS | 2 |
| [`access-access-required`](https://www.w3.org/TR/lws10-core/#access-property) | MUST | PASS | 2 |
| [`access-endpoints-are-lws-containers`](https://www.w3.org/TR/lws10-core/#access-protocol) | MUST | PASS | 1 |
| [`access-endpoints-get-post-delete`](https://www.w3.org/TR/lws10-core/#access-protocol) | SHOULD | PASS | 1 |
| [`access-endpoints-jsonld-payloads`](https://www.w3.org/TR/lws10-core/#access-protocol) | MUST | PASS | 1 |
| [`access-extra-properties-allowed`](https://www.w3.org/TR/lws10-core/#access-data-model) | MAY | PASS | 1 |
| [`access-inbox-notifications`](https://www.w3.org/TR/lws10-core/#access-notifications) | SHOULD | PASS | 1 |
| [`access-inbox-optional`](https://www.w3.org/TR/lws10-core/#access-inbox-property) | MAY | PASS | 1 |
| [`access-inbox-uri`](https://www.w3.org/TR/lws10-core/#access-inbox-property) | MUST | PASS | 1 |
| [`access-jsonld-context-lws-v1`](https://www.w3.org/TR/lws10-core/#json-ld-serialization) | MUST | PASS | 1 |
| [`access-notification-data-model`](https://www.w3.org/TR/lws10-core/#access-notifications) | MUST | PASS | 1 |
| [`access-notification-delivery`](https://www.w3.org/TR/lws10-core/#access-notifications) | MUST | PASS | 1 |
| [`access-notification-events`](https://www.w3.org/TR/lws10-core/#access-notification-events) | SHOULD | PASS | 1 |
| [`access-notify-grant-created`](https://www.w3.org/TR/lws10-core/#access-notification-events) | SHOULD | UNCOVERED | 0 |
| [`access-notify-other-events`](https://www.w3.org/TR/lws10-core/#access-notification-events) | MAY | UNCOVERED | 0 |
| [`access-notify-request-created`](https://www.w3.org/TR/lws10-core/#access-notification-events) | SHOULD | UNCOVERED | 0 |
| [`access-post-location-header`](https://www.w3.org/TR/lws10-core/#access-protocol) | MUST | PASS | 2 |
| [`access-services-advertised`](https://www.w3.org/TR/lws10-core/#access-discovery) | MUST | PASS | 1 |
| [`access-storage-required`](https://www.w3.org/TR/lws10-core/#access-storage-property) | MUST | PASS | 2 |
| [`access-storage-uri`](https://www.w3.org/TR/lws10-core/#access-storage-property) | MUST | PASS | 1 |
| [`access-type-required`](https://www.w3.org/TR/lws10-core/#access-type-property) | MUST | PASS | 2 |
| [`access-type-values`](https://www.w3.org/TR/lws10-core/#access-type-property) | MUST | PASS | 2 |
| [`authn-audience-restriction-recommended`](https://www.w3.org/TR/lws10-core/#authentication-data-model) | SHOULD | PASS | 1 |
| [`authn-client-claim`](https://www.w3.org/TR/lws10-core/#authentication-data-model) | MUST | PASS | 2 |
| [`authn-credential-signed`](https://www.w3.org/TR/lws10-core/#authentication-validation) | MUST | PASS | 8 |
| [`authn-credential-tamper-evident-claims`](https://www.w3.org/TR/lws10-core/#authentication-data-model) | MUST | PASS | 3 |
| [`authn-issuer-claim-uri`](https://www.w3.org/TR/lws10-core/#authentication-data-model) | MUST | PASS | 1 |
| [`authn-issuer-trust-out-of-band`](https://www.w3.org/TR/lws10-core/#authentication-validation) | MAY | UNCOVERED | 0 |
| [`authn-subject-claim-uri`](https://www.w3.org/TR/lws10-core/#authentication-data-model) | MUST | PASS | 1 |
| [`authn-suite-token-type-uri`](https://www.w3.org/TR/lws10-core/#authentication-type-identifier) | MUST | PASS | 1 |
| [`authz-401-storage-link`](https://www.w3.org/TR/lws10-core/#authorization-server-discovery) | MUST | PASS | 2 |
| [`authz-401-www-authenticate-challenge`](https://www.w3.org/TR/lws10-core/#authorization-server-discovery) | MUST | PASS | 5 |
| [`authz-access-token-aud-claim`](https://www.w3.org/TR/lws10-core/#authorization-token-exchange-response) | MUST | PASS | 2 |
| [`authz-access-token-client-id-claim`](https://www.w3.org/TR/lws10-core/#authorization-token-exchange-response) | MUST | PASS | 1 |
| [`authz-access-token-exp-short-lived`](https://www.w3.org/TR/lws10-core/#authorization-token-exchange-response) | MUST | PASS | 1 |
| [`authz-access-token-iat-claim`](https://www.w3.org/TR/lws10-core/#authorization-token-exchange-response) | MUST | PASS | 1 |
| [`authz-access-token-iss-claim`](https://www.w3.org/TR/lws10-core/#authorization-token-exchange-response) | MUST | PASS | 2 |
| [`authz-access-token-jti-claim`](https://www.w3.org/TR/lws10-core/#authorization-token-exchange-response) | MUST | PASS | 1 |
| [`authz-access-token-sub-claim`](https://www.w3.org/TR/lws10-core/#authorization-token-exchange-response) | MUST | PASS | 1 |
| [`authz-bearer-presentation-rfc6750`](https://www.w3.org/TR/lws10-core/#authorization-token-validation-presentation) | MUST | PASS | 1 |
| [`authz-challenge-extra-params`](https://www.w3.org/TR/lws10-core/#authorization-server-discovery) | MAY | UNCOVERED | 0 |
| [`authz-client-prm-resource-matches`](https://www.w3.org/TR/lws10-core/#authorization-discovery-validation) | MUST | PASS | 2 |
| [`authz-client-resource-metadata-same-origin`](https://www.w3.org/TR/lws10-core/#authorization-discovery-validation) | MUST | PASS | 1 |
| [`authz-client-storage-root-same-origin`](https://www.w3.org/TR/lws10-core/#authorization-discovery-validation) | MUST | PASS | 1 |
| [`authz-invalid-token-401-error-param`](https://www.w3.org/TR/lws10-core/#authorization-token-validation-verification) | MUST | PASS | 2 |
| [`authz-jwt-signature-jwks-rotation`](https://www.w3.org/TR/lws10-core/#authorization-token-validation-verification) | MUST | PASS | 4 |
| [`authz-metadata-subject-identifier-types`](https://www.w3.org/TR/lws10-core/#authorization-server-metadata) | SHOULD | PASS | 1 |
| [`authz-metadata-subject-token-types`](https://www.w3.org/TR/lws10-core/#authorization-server-metadata) | SHOULD | PASS | 2 |
| [`authz-oauth2-baseline`](https://www.w3.org/TR/lws10-core/#authorization) | MAY | UNCOVERED | 0 |
| [`authz-policy-denial-rejected`](https://www.w3.org/TR/lws10-core/#authorization-token-validation-verification) | MUST | PASS | 4 |
| [`authz-prm-authorization-servers`](https://www.w3.org/TR/lws10-core/#protected-resource-metadata) | MUST | PASS | 1 |
| [`authz-prm-conforms-rfc9728`](https://www.w3.org/TR/lws10-core/#protected-resource-metadata) | MUST | PASS | 1 |
| [`authz-server-metadata-well-known`](https://www.w3.org/TR/lws10-core/#authorization-server-metadata) | MUST | PASS | 1 |
| [`authz-token-error-rfc6749`](https://www.w3.org/TR/lws10-core/#authorization-token-exchange-response) | MUST | PASS | 3 |
| [`authz-token-exchange-grant`](https://www.w3.org/TR/lws10-core/#authorization-token-exchange-request) | MUST | PASS | 2 |
| [`authz-token-exchange-resource-param`](https://www.w3.org/TR/lws10-core/#authorization-token-exchange-request) | MUST | PASS | 3 |
| [`authz-token-exchange-subject-token-param`](https://www.w3.org/TR/lws10-core/#authorization-token-exchange-request) | MUST | PASS | 2 |
| [`authz-token-response-rfc6749-rfc9068`](https://www.w3.org/TR/lws10-core/#authorization-token-exchange-response) | MUST | PASS | 1 |
| [`authz-token-validation-checklist`](https://www.w3.org/TR/lws10-core/#authorization-token-validation-verification) | MUST | PASS | 9 |
| [`authz-validate-before-issuing`](https://www.w3.org/TR/lws10-core/#authorization-token-exchange-request) | MUST | PASS | 1 |
| [`capability-move-applies-to`](https://www.w3.org/TR/lws10-core/#storage-description-capabilities) | MUST | PASS | 3 |
| [`capability-move-preserves-identifier`](https://www.w3.org/TR/lws10-core/#storage-description-capabilities) | MUST | PASS | 2 |
| [`capability-move-resource`](https://www.w3.org/TR/lws10-core/#storage-description-capabilities) | MUST | PASS | 2 |
| [`conditional-requests-supported`](https://www.w3.org/TR/lws10-core/#read-resource) | SHOULD | PASS | 4 |
| [`conformance-server-class`](https://www.w3.org/TR/lws10-core/#conformance) | MUST | UNCOVERED | 0 |
| [`conneg-lws-json-honored`](https://www.w3.org/TR/lws10-core/#content-negotiation) | MUST | PASS | 2 |
| [`conneg-lws-profile-isomorphic`](https://www.w3.org/TR/lws10-core/#content-negotiation) | MUST | PASS | 2 |
| [`conneg-vary-accept`](https://www.w3.org/TR/lws10-core/#content-negotiation) | SHOULD | PASS | 1 |
| [`contained-description-recommended-members`](https://www.w3.org/TR/lws10-core/#contained-resource-description) | SHOULD | PASS | 1 |
| [`contained-description-required-members`](https://www.w3.org/TR/lws10-core/#contained-resource-description) | MUST | PASS | 1 |
| [`contained-format-for-dataresources`](https://www.w3.org/TR/lws10-core/#contained-resource-description) | MUST | PASS | 2 |
| [`contained-resource-type-values`](https://www.w3.org/TR/lws10-core/#contained-resource-description) | MUST | PASS | 1 |
| [`container-empty-items-array`](https://www.w3.org/TR/lws10-core/#container-properties) | MUST | PASS | 2 |
| [`container-listing-authorization-visibility`](https://www.w3.org/TR/lws10-core/#container-membership-and-authorization) | MUST | PASS | 1 |
| [`container-model-members`](https://www.w3.org/TR/lws10-core/#container-model) | MAY | UNCOVERED | 0 |
| [`container-representation-required-properties`](https://www.w3.org/TR/lws10-core/#container-properties) | MUST | PASS | 1 |
| [`container-totalitems-accuracy`](https://www.w3.org/TR/lws10-core/#container-properties) | SHOULD | PASS | 1 |
| [`containment-create-atomic-items`](https://www.w3.org/TR/lws10-core/#containment-integrity) | MUST | PASS | 1 |
| [`containment-delete-atomic-items`](https://www.w3.org/TR/lws10-core/#containment-integrity) | MUST | PASS | 3 |
| [`containment-integrity`](https://www.w3.org/TR/lws10-core/#containment-integrity) | MUST | PASS | 1 |
| [`containment-integrity-move`](https://www.w3.org/TR/lws10-core/#containment-integrity) | MUST | PASS | 1 |
| [`containment-no-cycles`](https://www.w3.org/TR/lws10-core/#containment-integrity) | MUST | UNCOVERED | 0 |
| [`containment-no-orphans`](https://www.w3.org/TR/lws10-core/#containment-integrity) | MUST | PASS | 1 |
| [`containment-rel-up-get-head`](https://www.w3.org/TR/lws10-core/#containment) | MUST | PASS | 4 |
| [`create-401-storage-link`](https://www.w3.org/TR/lws10-core/#create-resource) | SHOULD | PASS | 1 |
| [`create-container-type-link`](https://www.w3.org/TR/lws10-core/#create-resource) | MUST | PASS | 1 |
| [`create-linkset-before-success`](https://www.w3.org/TR/lws10-core/#create-resource) | MUST | PASS | 1 |
| [`create-post-201-location-links`](https://www.w3.org/TR/lws10-core/#create-resource) | MUST | PASS | 5 |
| [`create-post-missing-container-404`](https://www.w3.org/TR/lws10-core/#create-resource) | MUST | PASS | 2 |
| [`create-post-not-idempotent`](https://www.w3.org/TR/lws10-core/#create-resource) | SHOULD | PASS | 1 |
| [`create-server-managed-metadata-protected`](https://www.w3.org/TR/lws10-core/#create-resource) | MUST | PASS | 1 |
| [`delete-401-403-404-semantics`](https://www.w3.org/TR/lws10-core/#delete-resource) | MUST | PASS | 2 |
| [`delete-if-match-optional`](https://www.w3.org/TR/lws10-core/#delete-resource) | MAY | PASS | 1 |
| [`delete-non-empty-container-409-depth`](https://www.w3.org/TR/lws10-core/#delete-resource) | MUST | PASS | 3 |
| [`delete-removes-from-parent-listing`](https://www.w3.org/TR/lws10-core/#delete-resource) | MUST | PASS | 2 |
| [`delete-success-204-conditional`](https://www.w3.org/TR/lws10-core/#delete-resource) | MUST | PASS | 3 |
| [`error-rfc9457-problem-details`](https://www.w3.org/TR/lws10-core/#summary-of-http-status-mappings) | SHOULD | PASS | 1 |
| [`get-data-resource-content-range-etag`](https://www.w3.org/TR/lws10-core/#read-resource) | MUST | PASS | 3 |
| [`head-parity-with-get`](https://www.w3.org/TR/lws10-core/#read-resource) | MUST | PASS | 2 |
| [`link-storage-on-responses`](https://www.w3.org/TR/lws10-core/#metadata-0) | MUST | PASS | 4 |
| [`link-up-on-non-root-resources`](https://www.w3.org/TR/lws10-core/#metadata-0) | MUST | PASS | 1 |
| [`linkset-accept-patch-json-patch`](https://www.w3.org/TR/lws10-core/#metadata-0) | MUST | PASS | 1 |
| [`linkset-allow-get-patch`](https://www.w3.org/TR/lws10-core/#metadata-0) | MUST | PASS | 1 |
| [`linkset-etag-get-head`](https://www.w3.org/TR/lws10-core/#metadata-0) | MUST | PASS | 1 |
| [`linkset-lifecycle-tied-to-resource`](https://www.w3.org/TR/lws10-core/#metadata-0) | MUST | PASS | 2 |
| [`linkset-media-type-json`](https://www.w3.org/TR/lws10-core/#metadata-0) | MUST | PASS | 1 |
| [`linkset-optional-methods-advertised`](https://www.w3.org/TR/lws10-core/#metadata-0) | MUST | INAPPLICABLE | 1 |
| [`linkset-patch-json-patch`](https://www.w3.org/TR/lws10-core/#metadata-0) | MUST | PASS | 1 |
| [`linkset-precondition-failed-412`](https://www.w3.org/TR/lws10-core/#update-resource) | MUST | PASS | 1 |
| [`linkset-put-405-if-unsupported`](https://www.w3.org/TR/lws10-core/#metadata-0) | MUST | INAPPLICABLE | 1 |
| [`linkset-restricted-links-preserved`](https://www.w3.org/TR/lws10-core/#metadata-0) | MUST | PASS | 1 |
| [`linkset-server-managed-atomic`](https://www.w3.org/TR/lws10-core/#metadata-0) | MUST | PASS | 2 |
| [`linkset-standalone-rfc9264`](https://www.w3.org/TR/lws10-core/#metadata-0) | MUST | PASS | 2 |
| [`lws-cid-media-type-storage-description`](https://www.w3.org/TR/lws10-core/#lws-media-type-0) | MUST | PASS | 1 |
| [`lws-json-media-type-container-representation`](https://www.w3.org/TR/lws10-core/#lws-media-type-0) | MUST | PASS | 1 |
| [`metadata-capability-advertising`](https://www.w3.org/TR/lws10-core/#metadata-0) | MUST | PASS | 1 |
| [`move-authorization-delete-and-create`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | PASS | 2 |
| [`move-container-subtree-authorization`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | UNCOVERED | 0 |
| [`move-containers-applies-to`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | PASS | 2 |
| [`move-containment-atomic`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | PASS | 3 |
| [`move-containment-integrity-cycles`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | PASS | 1 |
| [`move-cross-storage-may-reject`](https://www.w3.org/TR/lws10-core/#moving-resources) | MAY | UNCOVERED | 0 |
| [`move-destination-existing-container`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | PASS | 2 |
| [`move-identifier-preserved`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | INAPPLICABLE | 1 |
| [`move-new-identifier-response`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | UNCOVERED | 0 |
| [`move-notification-single-activity`](https://www.w3.org/TR/lws10-core/#moving-resources) | SHOULD | PASS | 1 |
| [`move-preserves-content-and-links`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | INAPPLICABLE | 1 |
| [`move-request-json-patch`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | PASS | 1 |
| [`move-server-support`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | PASS | 3 |
| [`notification-activity-as2-conformance`](https://www.w3.org/TR/lws10-core/#activity-properties) | MUST | PASS | 1 |
| [`notification-activity-id`](https://www.w3.org/TR/lws10-core/#activity-properties) | MUST | PASS | 1 |
| [`notification-activity-move`](https://www.w3.org/TR/lws10-core/#activity-types) | MUST | PASS | 1 |
| [`notification-activity-object`](https://www.w3.org/TR/lws10-core/#activity-properties) | MUST | PASS | 1 |
| [`notification-activity-object-id`](https://www.w3.org/TR/lws10-core/#activity-properties) | MUST | PASS | 5 |
| [`notification-activity-object-type`](https://www.w3.org/TR/lws10-core/#activity-properties) | MUST | PASS | 1 |
| [`notification-activity-optional-properties`](https://www.w3.org/TR/lws10-core/#activity-properties) | MAY | PASS | 1 |
| [`notification-activity-published`](https://www.w3.org/TR/lws10-core/#activity-properties) | MUST | PASS | 1 |
| [`notification-activity-type`](https://www.w3.org/TR/lws10-core/#activity-properties) | MUST | PASS | 3 |
| [`notification-activity-types-additional`](https://www.w3.org/TR/lws10-core/#activity-types) | MAY | UNCOVERED | 0 |
| [`notification-activity-types-supported`](https://www.w3.org/TR/lws10-core/#activity-types) | MUST | PASS | 5 |
| [`notification-batching`](https://www.w3.org/TR/lws10-core/#batching) | MAY | UNCOVERED | 0 |
| [`notification-envelope-activity`](https://www.w3.org/TR/lws10-core/#envelope-properties) | MUST | PASS | 1 |
| [`notification-envelope-storage`](https://www.w3.org/TR/lws10-core/#envelope-properties) | MUST | PASS | 1 |
| [`notification-envelope-type`](https://www.w3.org/TR/lws10-core/#envelope-properties) | MUST | PASS | 1 |
| [`notification-suite-subscription-type-identifier`](https://www.w3.org/TR/lws10-core/#notification-subscription-type-identifier) | MUST | PASS | 1 |
| [`notifications-advertise-notificationservice`](https://www.w3.org/TR/lws10-core/#notification-discovery) | MUST | PASS | 1 |
| [`notificationservice-additional-properties`](https://www.w3.org/TR/lws10-core/#notification-discovery) | MAY | UNCOVERED | 0 |
| [`notificationservice-endpoint-and-subscription-types`](https://www.w3.org/TR/lws10-core/#notification-discovery) | MUST | PASS | 1 |
| [`operations-core-four-atomic`](https://www.w3.org/TR/lws10-core/#operations) | MUST | UNCOVERED | 0 |
| [`pagination-200-totalitems-all-pages`](https://www.w3.org/TR/lws10-core/#requesting-pages) | MUST | INAPPLICABLE | 3 |
| [`pagination-first-page-flow`](https://www.w3.org/TR/lws10-core/#requesting-pages) | MAY | INAPPLICABLE | 1 |
| [`pagination-link-first`](https://www.w3.org/TR/lws10-core/#pagination-link-relations) | MUST | PASS | 5 |
| [`pagination-link-last`](https://www.w3.org/TR/lws10-core/#pagination-link-relations) | MAY | INAPPLICABLE | 1 |
| [`pagination-link-next`](https://www.w3.org/TR/lws10-core/#pagination-link-relations) | MUST | PASS | 2 |
| [`pagination-link-prev`](https://www.w3.org/TR/lws10-core/#pagination-link-relations) | MUST | PASS | 2 |
| [`pagination-over-threshold`](https://www.w3.org/TR/lws10-core/#pagination) | SHOULD | UNCOVERED | 0 |
| [`patch-json-patch-baseline`](https://www.w3.org/TR/lws10-core/#update-resource) | MUST | PASS | 2 |
| [`policy-action-required`](https://www.w3.org/TR/lws10-core/#odrl-action) | MUST | PASS | 2 |
| [`policy-action-values`](https://www.w3.org/TR/lws10-core/#odrl-action) | MUST | PASS | 1 |
| [`policy-assignee-required`](https://www.w3.org/TR/lws10-core/#odrl-assignee) | MUST | PASS | 2 |
| [`policy-assignee-uri-foaf-agent`](https://www.w3.org/TR/lws10-core/#odrl-assignee) | MUST | PASS | 2 |
| [`policy-constraint-left-operands`](https://www.w3.org/TR/lws10-core/#odrl-constraint) | MUST | PASS | 5 |
| [`policy-constraint-objects`](https://www.w3.org/TR/lws10-core/#odrl-constraint) | MUST | PASS | 2 |
| [`policy-constraint-optional`](https://www.w3.org/TR/lws10-core/#odrl-constraint) | MAY | PASS | 1 |
| [`policy-constraints-all-satisfied`](https://www.w3.org/TR/lws10-core/#odrl-constraint) | MUST | PASS | 1 |
| [`policy-constraints-conjunction-semantics`](https://www.w3.org/TR/lws10-core/#constraint-combining) | MUST | PASS | 1 |
| [`policy-target-extra-types`](https://www.w3.org/TR/lws10-core/#odrl-target) | MAY | UNCOVERED | 0 |
| [`policy-target-object`](https://www.w3.org/TR/lws10-core/#odrl-target) | MUST | PASS | 2 |
| [`policy-target-optional`](https://www.w3.org/TR/lws10-core/#odrl-target) | MAY | UNCOVERED | 0 |
| [`policy-type-access-policy`](https://www.w3.org/TR/lws10-core/#odrl-type) | MUST | PASS | 2 |
| [`policy-type-required`](https://www.w3.org/TR/lws10-core/#odrl-type) | MUST | PASS | 2 |
| [`privacy-move-redirect-access-control`](https://www.w3.org/TR/lws10-core/#privacy-moving-resources) | SHOULD | UNCOVERED | 0 |
| [`privacy-notification-actor-omitted`](https://www.w3.org/TR/lws10-core/#privacy-notifications) | SHOULD | PASS | 1 |
| [`privacy-notification-authorized-resources-only`](https://www.w3.org/TR/lws10-core/#privacy-notifications) | SHOULD | PASS | 1 |
| [`put-clients-use-conditional-requests`](https://www.w3.org/TR/lws10-core/#update-resource) | SHOULD | UNCOVERED | 0 |
| [`read-container-etag-type-links`](https://www.w3.org/TR/lws10-core/#read-resource) | MUST | PASS | 1 |
| [`read-container-listing-authz-filtered`](https://www.w3.org/TR/lws10-core/#read-resource) | MAY | PASS | 1 |
| [`read-container-listing-member-metadata`](https://www.w3.org/TR/lws10-core/#read-resource) | MUST | PASS | 1 |
| [`read-type-distinction-metadata-links`](https://www.w3.org/TR/lws10-core/#read-resource) | MUST | PASS | 2 |
| [`security-move-capability-restraint`](https://www.w3.org/TR/lws10-core/#security-moving-resources) | MUST | UNCOVERED | 0 |
| [`security-move-container-subtree`](https://www.w3.org/TR/lws10-core/#security-moving-resources) | MUST | UNCOVERED | 0 |
| [`security-move-privilege-combination`](https://www.w3.org/TR/lws10-core/#security-moving-resources) | MUST | PASS | 2 |
| [`security-notification-access-control`](https://www.w3.org/TR/lws10-core/#security-notifications) | MUST | PASS | 4 |
| [`status-204-410-deletions`](https://www.w3.org/TR/lws10-core/#summary-of-http-status-mappings) | MAY | PASS | 1 |
| [`storage-capability-id-optional`](https://www.w3.org/TR/lws10-core/#storage-description-data-model) | MUST | PASS | 1 |
| [`storage-capability-property`](https://www.w3.org/TR/lws10-core/#storage-description-data-model) | MUST | PASS | 1 |
| [`storage-capability-type-required`](https://www.w3.org/TR/lws10-core/#storage-description-data-model) | MUST | PASS | 1 |
| [`storage-description-id-required`](https://www.w3.org/TR/lws10-core/#storage-description-data-model) | MUST | PASS | 1 |
| [`storage-description-link-header`](https://www.w3.org/TR/lws10-core/#storage-description-binding) | MUST | PASS | 2 |
| [`storage-description-lws-cid`](https://www.w3.org/TR/lws10-core/#storage-description-representation) | MUST | PASS | 1 |
| [`storage-description-storageroot-service`](https://www.w3.org/TR/lws10-core/#storage-description-services) | MUST | PASS | 2 |
| [`storage-description-type-storage`](https://www.w3.org/TR/lws10-core/#storage-description-data-model) | MUST | PASS | 1 |
| [`storage-service-endpoint-required`](https://www.w3.org/TR/lws10-core/#storage-description-data-model) | MUST | PASS | 1 |
| [`storage-service-id-optional`](https://www.w3.org/TR/lws10-core/#storage-description-data-model) | MUST | PASS | 1 |
| [`storage-service-property`](https://www.w3.org/TR/lws10-core/#storage-description-data-model) | MUST | PASS | 1 |
| [`storage-service-type-required`](https://www.w3.org/TR/lws10-core/#storage-description-data-model) | MUST | PASS | 1 |
| [`storage-uri-returns-lws-cid-document`](https://www.w3.org/TR/lws10-core/#storage-description-binding) | MUST | PASS | 2 |
| [`subscription-authorization-on-create`](https://www.w3.org/TR/lws10-core/#subscription-authorization) | MUST | PASS | 2 |
| [`subscription-authorization-on-delivery`](https://www.w3.org/TR/lws10-core/#subscription-authorization) | MUST | PASS | 2 |
| [`subscription-authorization-revoked`](https://www.w3.org/TR/lws10-core/#subscription-authorization) | MUST | PASS | 1 |
| [`subscription-create-post-lws-json`](https://www.w3.org/TR/lws10-core/#subscriptions) | MUST | PASS | 1 |
| [`subscription-request-additional-fields`](https://www.w3.org/TR/lws10-core/#subscription-request) | MAY | PASS | 1 |
| [`subscription-request-required-fields`](https://www.w3.org/TR/lws10-core/#subscription-request) | MUST | PASS | 3 |
| [`subscription-request-topic`](https://www.w3.org/TR/lws10-core/#subscription-request) | MUST | PASS | 2 |
| [`subscription-request-type`](https://www.w3.org/TR/lws10-core/#subscription-request) | MUST | PASS | 3 |
| [`subscription-response-lws-json`](https://www.w3.org/TR/lws10-core/#subscription-response) | MUST | PASS | 1 |
| [`subscription-response-subscription-url`](https://www.w3.org/TR/lws10-core/#subscription-response) | MUST | PASS | 1 |
| [`subscription-response-type`](https://www.w3.org/TR/lws10-core/#subscription-response) | MUST | PASS | 1 |
| [`update-content-vs-metadata-prefer-set-linkset`](https://www.w3.org/TR/lws10-core/#update-resource) | MUST | PASS | 1 |
| [`uri-independent-of-hierarchy`](https://www.w3.org/TR/lws10-core/#resource-identification-0) | SHOULD | PASS | 1 |
| [`accept-query-advertised`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | SHOULD | PASS | 1 |
| [`accept-query-no-disclosure`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | PASS | 1 |
| [`at-members-ignored`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | PASS | 1 |
| [`authorization-enforced`](https://w3c.github.io/lws-protocol/lws10-index/#security-authorization) | MUST | PASS | 3 |
| [`baseline-format-supported`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | PASS | 1 |
| [`consistency-not-for-authorization`](https://w3c.github.io/lws-protocol/lws10-index/#type-derivation) | MUST | PASS | 1 |
| [`content-location-protected`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | PASS | 1 |
| [`content-types-identical`](https://w3c.github.io/lws-protocol/lws10-index/#type-derivation) | MUST | PASS | 1 |
| [`counts-filtered`](https://w3c.github.io/lws-protocol/lws10-index/#security-authorization) | MUST | PASS | 1 |
| [`current-authorization`](https://w3c.github.io/lws-protocol/lws10-index/#security-authorization) | MUST | PASS | 1 |
| [`derived-index-filtered`](https://w3c.github.io/lws-protocol/lws10-index/#security-authorization) | MUST | PASS | 2 |
| [`duplicate-groups-ignored`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | PASS | 1 |
| [`empty-group-rejected`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | PASS | 1 |
| [`eventually-consistent`](https://w3c.github.io/lws-protocol/lws10-index/#type-derivation) | MAY | UNCOVERED | 0 |
| [`expired-page-404-410`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-errors) | MUST | PASS | 1 |
| [`extensions-uphold-authorization`](https://w3c.github.io/lws-protocol/lws10-index/#security-authorization) | MUST | UNCOVERED | 0 |
| [`grammar-not-extended`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | PASS | 1 |
| [`invalid-iri-400`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-errors) | MUST | PASS | 1 |
| [`malformed-filter-400`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-errors) | MUST | PASS | 4 |
| [`missing-content-type-400`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-errors) | MUST | PASS | 1 |
| [`no-existence-disclosure`](https://w3c.github.io/lws-protocol/lws10-index/#security-authorization) | MUST | PASS | 2 |
| [`no-match-not-error`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | PASS | 2 |
| [`no-shared-cache`](https://w3c.github.io/lws-protocol/lws10-index/#security-authorization) | MUST | PASS | 2 |
| [`no-silent-narrowing`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-errors) | MUST | PASS | 1 |
| [`not-acceptable-406`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-errors) | MUST | PASS | 1 |
| [`other-formats`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MAY | UNCOVERED | 0 |
| [`other-response-formats`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MAY | PASS | 1 |
| [`query-content-type-required`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | PASS | 1 |
| [`query-safe-idempotent`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MAY | PASS | 1 |
| [`reflect-change-bounded`](https://w3c.github.io/lws-protocol/lws10-index/#type-derivation) | SHOULD | PASS | 4 |
| [`relation-sources-identical`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | PASS | 1 |
| [`relations-may-be-indexed`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MAY | PASS | 4 |
| [`relations-not-enumerated`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | UNCOVERED | 0 |
| [`responses-private`](https://w3c.github.io/lws-protocol/lws10-index/#security-authorization) | MUST | PASS | 2 |
| [`result-item-id-type`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | PASS | 2 |
| [`result-item-metadata`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MAY | UNCOVERED | 0 |
| [`revoked-not-shown`](https://w3c.github.io/lws-protocol/lws10-index/#security-authorization) | MUST | PASS | 1 |
| [`search-default-containerpage`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | PASS | 4 |
| [`service-advertised`](https://w3c.github.io/lws-protocol/lws10-index/#discovery) | MUST | PASS | 1 |
| [`service-endpoint`](https://w3c.github.io/lws-protocol/lws10-index/#discovery) | MUST | PASS | 1 |
| [`service-extra-properties`](https://w3c.github.io/lws-protocol/lws10-index/#discovery) | MAY | UNCOVERED | 0 |
| [`services-optional`](https://w3c.github.io/lws-protocol/lws10-index/#discovery) | MAY | PASS | 1 |
| [`structural-relations-not-indexed`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | PASS | 1 |
| [`too-complex-422`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-errors) | MUST | PASS | 1 |
| [`type-filter`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MAY | PASS | 5 |
| [`type-key-supported`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | PASS | 3 |
| [`types-from-content`](https://w3c.github.io/lws-protocol/lws10-index/#type-derivation) | MAY | PASS | 1 |
| [`types-from-link-headers`](https://w3c.github.io/lws-protocol/lws10-index/#type-derivation) | SHOULD | PASS | 4 |
| [`unauthorized-omitted`](https://w3c.github.io/lws-protocol/lws10-index/#security-authorization) | MUST | PASS | 2 |
| [`unindexed-relation-indistinguishable`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | PASS | 2 |
| [`unsupported-format-415`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-errors) | MUST | PASS | 1 |
| [`unsupported-format-accept-query`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-errors) | SHOULD | PASS | 1 |
| [`vary-accept`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-errors) | MUST | PASS | 1 |
| [`delivery-deactivation-optional`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#webhook-delivery) | MAY | PASS | 1 |
| [`delivery-lws-json`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#webhook-delivery) | MUST | PASS | 1 |
| [`delivery-retry-optional`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#webhook-delivery) | MAY | PASS | 1 |
| [`delivery-signed`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#webhook-authentication) | SHOULD | PASS | 1 |
| [`inbox-verifies-signature`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#webhook-authentication) | MUST | PASS | 1 |
| [`keyid-url-with-fragment`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#signature-verification) | MUST | PASS | 1 |
| [`receiver-verification-steps`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#signature-verification) | MUST | PASS | 1 |
| [`response-expires-optional`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#webhook-subscription) | MAY | PASS | 1 |
| [`response-type-webhook`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#webhook-subscription) | MUST | PASS | 1 |
| [`signature-covered-components`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#signature-requirements) | MUST | PASS | 2 |
| [`signature-input-created-keyid`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#signature-requirements) | MUST | PASS | 2 |
| [`signing-key-published`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#webhook-authentication) | MUST | PASS | 2 |
| [`storage-description-id-matches`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#signature-verification) | MUST | PASS | 1 |
| [`subscription-expires-optional`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#webhook-subscription) | MAY | PASS | 1 |
| [`subscription-get-delete`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#webhook-subscription-management) | MUST | PASS | 1 |
| [`subscription-inbox-required`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#webhook-subscription) | MUST | PASS | 1 |
| [`subscription-listing-container`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#webhook-subscription-management) | MUST | PASS | 2 |
| [`subscription-type-and-fields`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#webhook-subscription) | MUST | PASS | 2 |
| [`subscription-type-identifier`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#subscription-type) | MUST | PASS | 1 |

