# Touchstone conformance report

**CONFORMANT**: only MUST tests decide conformance (definitions/EXECUTION.md section 9), and 0 failed or ended cantTell. SHOULD and MAY failures are advisory: 0. Inapplicable MUST tests are coverage this run did not have: 125.

| | |
|---|---|
| target | factoidal-open-unstable |
| base URL | `http://127.0.0.1:33321/` |
| run | `9db984fc` |
| started | 2026-10-21T21:36:36.174670399Z |

## Results

| passed | failed | cantTell | inapplicable |
|---:|---:|---:|---:|
| 76 | 0 | 0 | 145 |

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
| `core/discovery#discovery-get-links-storageDescription` | MUST | passed | 510 ms |
| `core/discovery#discovery-link-storage-on-data-resource` | MUST | passed | 710 ms |
| `core/discovery#discovery-storage-description` | MUST | passed | 829 ms |
| `core/discovery#discovery-storage-description-default-media-type` | MUST | passed | 607 ms |
| `core/discovery#discovery-unauthorized-response-headers` | MUST | inapplicable | 0 ms |
| `core/discovery#discovery-storage-root-is-container` | MUST | passed | 1103 ms |
| `core/discovery#discovery-storage-description-ids-are-uris` | MUST | passed | 612 ms |
| `core/containers#getContainer` | MUST | passed | 416 ms |
| `core/containers#createContainer` | MUST | passed | 536 ms |
| `core/containers#createContainer-type-link` | SHOULD | passed | 453 ms |
| `core/containers#getContainer-containmentIntegrity` | MUST | passed | 613 ms |
| `core/containers#container-total-items-accurate` | SHOULD | passed | 1010 ms |
| `core/containers#contained-resource-type-values` | MUST | passed | 965 ms |
| `core/containers#contained-resource-format` | MUST | passed | 474 ms |
| `core/containers#contained-resource-size-modified` | SHOULD | passed | 638 ms |
| `core/containers#container-conneg` | MUST | passed | 390 ms |
| `core/containers#container-conneg-vary` | SHOULD | passed | 550 ms |
| `core/containers#container-conneg-weighted` | MUST | passed | 276 ms |
| `core/containers#container-head-parity` | MUST | passed | 613 ms |
| `core/containers#delete-empty-container` | MUST | passed | 858 ms |
| `core/containers#delete-non-empty-container-409` | MUST | passed | 1363 ms |
| `core/containers#delete-container-recursive` | MAY | passed | 1064 ms |
| `core/containers#delete-container-recursive-deep` | MAY | passed | 1329 ms |
| `core/containers#containment-hierarchy-consistent` | MUST | passed | 1167 ms |
| `core/containers#container-lws-profile-ld-json` | MUST | passed | 1017 ms |
| `core/containers#container-lws-profile-turtle` | MUST | passed | 1023 ms |
| `core/data_resources#createDataResource` | MUST | passed | 621 ms |
| `core/data_resources#createDataResource-type-link` | SHOULD | passed | 791 ms |
| `core/data_resources#create-post-twice-distinct` | SHOULD | passed | 867 ms |
| `core/data_resources#create-in-missing-container-rejected` | MUST | passed | 619 ms |
| `core/data_resources#create-in-missing-container-404` | SHOULD | passed | 442 ms |
| `core/data_resources#create-server-managed-links-protected` | MUST | passed | 540 ms |
| `core/data_resources#readDataResource` | MUST | passed | 548 ms |
| `core/data_resources#data-resource-head-parity` | MUST | passed | 665 ms |
| `core/data_resources#data-resource-range-request` | MUST | passed | 1155 ms |
| `core/data_resources#data-resource-range-unsatisfiable` | SHOULD | passed | 579 ms |
| `core/data_resources#data-resource-accept-ranges` | MAY | passed | 803 ms |
| `core/data_resources#updateDataResource` | MUST | passed | 704 ms |
| `core/data_resources#patch-json-patch-baseline` | MUST | passed | 723 ms |
| `core/data_resources#patch-json-patch-atomic` | MUST | passed | 555 ms |
| `core/data_resources#deleteDataResource` | MUST | passed | 739 ms |
| `core/data_resources#post-to-non-container-405` | SHOULD | passed | 556 ms |
| `core/data_resources#error-problem-details` | SHOULD | passed | 367 ms |
| `core/conditional_requests#conditional-get-304` | SHOULD | passed | 530 ms |
| `core/conditional_requests#conditional-get-container-304` | SHOULD | passed | 415 ms |
| `core/conditional_requests#conditional-get-stale-validator-200` | MUST | passed | 956 ms |
| `core/conditional_requests#conditional-put-stale-if-match-412` | MUST | passed | 683 ms |
| `core/conditional_requests#conditional-delete-stale-if-match-412` | SHOULD | passed | 635 ms |
| `core/conditional_requests#update-changes-strong-etag` | MUST | passed | 552 ms |
| `core/conditional_requests#delete-updates-parent-strong-etag` | MUST | passed | 772 ms |
| `core/conditional_requests#conditional-get-if-modified-since-304` | SHOULD | passed | 539 ms |
| `core/conditional_requests#conditional-get-if-unmodified-since-412` | SHOULD | passed | 915 ms |
| `core/linksets#getLinkset` | MUST | passed | 983 ms |
| `core/linksets#linkset-advertises-patch` | MUST | passed | 486 ms |
| `core/linksets#linkset-conditional-412` | MUST | passed | 564 ms |
| `core/linksets#linkset-put-405-when-unsupported` | MUST | inapplicable | 439 ms |
| `core/linksets#linkset-removed-with-resource` | MUST | passed | 691 ms |
| `core/linksets#linkset-ready-at-create` | MUST | passed | 567 ms |
| `core/linksets#linkset-up-not-redirected` | MUST | passed | 547 ms |
| `core/linksets#linkset-patch-stays-linkset` | MUST | passed | 655 ms |
| `core/linksets#linkset-patch-json-patch` | SHOULD | passed | 952 ms |
| `core/linksets#linkset-patch-preserves-server-links` | MUST | passed | 919 ms |
| `core/moving#discovery-move-capability` | MUST | passed | 524 ms |
| `core/moving#move-data-resource` | MUST | passed | 1499 ms |
| `core/moving#move-updates-container-etags` | MUST | passed | 1260 ms |
| `core/moving#move-keeps-identifier-content-and-links` | MUST | inapplicable | 665 ms |
| `core/moving#move-invalid-destination-refused` | MUST | passed | 1268 ms |
| `core/moving#move-container` | MUST | passed | 1226 ms |
| `core/moving#move-container-into-itself-refused` | MUST | passed | 1191 ms |
| `core/moving#move-container-refused-without-container-support` | MUST | inapplicable | 671 ms |
| `core/moving#move-refused-without-capability` | MUST | inapplicable | 581 ms |
| `core/moving#move-needs-create-in-destination` | MUST | inapplicable | 0 ms |
| `core/moving#move-needs-delete-of-resource` | MUST | inapplicable | 0 ms |
| `core/moving#move-notification` | MUST | inapplicable | 0 ms |
| `core/storage_authorization#getContainer-private-unauthorized` | MUST | inapplicable | 0 ms |
| `core/storage_authorization#protected-resource-metadata` | MUST | inapplicable | 0 ms |
| `core/storage_authorization#protected-resource-metadata-data-resource` | MUST | inapplicable | 0 ms |
| `core/storage_authorization#storage-root-same-origin` | MUST | inapplicable | 0 ms |
| `core/storage_authorization#getContainer-authenticated-owner` | MUST | inapplicable | 0 ms |
| `core/storage_authorization#createDataResource-unauthorized` | MUST | inapplicable | 0 ms |
| `core/storage_authorization#updateDataResource-unauthorized` | MUST | inapplicable | 0 ms |
| `core/storage_authorization#deleteDataResource-unauthorized` | MUST | inapplicable | 0 ms |
| `core/storage_authorization#authz-non-owner-read-rejected` | MUST | inapplicable | 0 ms |
| `core/storage_authorization#authz-non-owner-write-rejected` | MUST | inapplicable | 0 ms |
| `core/storage_authorization#authz-non-owner-delete-rejected` | MUST | inapplicable | 0 ms |
| `core/storage_authorization#authz-expired-token-rejected` | MUST | inapplicable | 1 ms |
| `core/storage_authorization#authz-token-bad-signature-rejected` | MUST | inapplicable | 0 ms |
| `core/storage_authorization#authz-token-alg-none-rejected` | MUST | inapplicable | 0 ms |
| `core/storage_authorization#authz-token-unknown-key-rejected` | MUST | inapplicable | 0 ms |
| `core/storage_authorization#authz-token-wrong-audience-rejected` | MUST | inapplicable | 0 ms |
| `core/storage_authorization#authz-token-wrong-issuer-rejected` | MUST | inapplicable | 1 ms |
| `core/storage_authorization#authz-token-not-yet-valid-rejected` | MUST | inapplicable | 0 ms |
| `core/storage_authorization#authz-token-issued-in-future-rejected` | MUST | inapplicable | 0 ms |
| `core/authorization_server#authz-server-metadata-well-known` | MUST | inapplicable | 0 ms |
| `core/authorization_server#authz-metadata-subject-token-types` | SHOULD | inapplicable | 0 ms |
| `core/authorization_server#authz-metadata-subject-token-types-are-uris` | MUST | inapplicable | 0 ms |
| `core/authorization_server#authz-metadata-subject-identifier-types` | SHOULD | inapplicable | 0 ms |
| `core/authorization_server#authz-token-exchange-valid` | MUST | inapplicable | 0 ms |
| `core/authorization_server#authz-token-exchange-invalid-resource` | MUST | inapplicable | 0 ms |
| `core/authorization_server#authz-token-exchange-missing-resource` | MUST | inapplicable | 0 ms |
| `core/authorization_server#authz-token-exchange-missing-subject-token` | MUST | inapplicable | 0 ms |
| `core/authorization_server#authz-issued-token-accepted-by-storage` | MUST | inapplicable | 0 ms |
| `core/access_grants#access-grant-endpoint-is-container` | MUST | passed | 414 ms |
| `core/access_grants#access-grant-create` | MUST | inapplicable | 0 ms |
| `core/access_grants#access-grant-revoke` | SHOULD | inapplicable | 0 ms |
| `core/access_grants#getContainer-public-read` | MUST | inapplicable | 0 ms |
| `core/access_grants#readDataResource-public-read` | MUST | inapplicable | 0 ms |
| `core/access_grants#access-grant-authenticated-agent` | MUST | inapplicable | 0 ms |
| `core/access_grants#access-grant-extra-properties-accepted` | MAY | inapplicable | 0 ms |
| `core/access_grants#access-grant-inbox-notified` | SHOULD | inapplicable | 0 ms |
| `core/access_grants#access-request-create` | MUST | inapplicable | 0 ms |
| `core/access_grants#access-grant-document-shape` | MUST | inapplicable | 0 ms |
| `core/access_grants#access-grant-incomplete-refused` | MUST | inapplicable | 0 ms |
| `core/access_grants#access-grant-constraints-all-satisfied` | MUST | inapplicable | 0 ms |
| `core/access_grants#access-grant-left-operands-accepted` | MUST | inapplicable | 0 ms |
| `core/access_grants#access-grant-constraint-format` | MUST | inapplicable | 0 ms |
| `core/access_grants#access-grant-constraint-type` | MUST | inapplicable | 0 ms |
| `core/access_grants#access-grant-constraint-client` | MUST | inapplicable | 0 ms |
| `core/access_grants#container-listing-filtered-metadata` | MAY | inapplicable | 0 ms |
| `core/notifications#notification-service-advertised` | MUST | passed | 494 ms |
| `core/notifications#subscription-create` | MUST | passed | 587 ms |
| `core/notifications#subscription-missing-type-refused` | MUST | passed | 612 ms |
| `core/notifications#subscription-unadvertised-type-refused` | MUST | passed | 451 ms |
| `core/notifications#subscription-missing-topic-refused` | MUST | passed | 384 ms |
| `core/notifications#subscription-unreadable-topic-refused` | MUST | inapplicable | 0 ms |
| `core/notifications#subscription-after-revocation-refused` | MUST | inapplicable | 0 ms |
| `core/notifications#notification-delivered-create` | MUST | inapplicable | 0 ms |
| `core/notifications#notification-delivered-update` | MUST | inapplicable | 0 ms |
| `core/notifications#notification-delivered-delete` | MUST | inapplicable | 0 ms |
| `core/notifications#notification-not-delivered-for-unreadable-resource` | MUST | inapplicable | 0 ms |
| `core/notifications#notification-stops-after-revocation` | MUST | inapplicable | 0 ms |
| `core/notifications#notification-actor-omitted` | SHOULD | inapplicable | 0 ms |
| `core/notifications#notification-delivered-in-subcontainer` | MUST | inapplicable | 0 ms |
| `core/notifications#notification-scope-data-resource-only` | MUST | inapplicable | 0 ms |
| `core/pagination#pagination-first-page` | MUST | passed | 779 ms |
| `core/pagination#pagination-next-page` | MUST | passed | 737 ms |
| `core/pagination#pagination-single-page` | MUST | inapplicable | 683 ms |
| `core/pagination#pagination-last-page` | MUST | passed | 695 ms |
| `core/pagination#pagination-totalitems-all-pages` | SHOULD | passed | 695 ms |
| `auth/oidc/manifest#authn-oidc-valid-id-token` | MUST | inapplicable | 0 ms |
| `auth/oidc/manifest#authn-oidc-expired-id-token` | MUST | inapplicable | 0 ms |
| `auth/oidc/manifest#authn-oidc-alg-none` | MUST | inapplicable | 0 ms |
| `auth/oidc/manifest#authn-oidc-bad-signature` | MUST | inapplicable | 0 ms |
| `auth/oidc/manifest#authn-oidc-untrusted-issuer` | MUST | inapplicable | 0 ms |
| `auth/oidc/manifest#authn-oidc-missing-azp` | MUST | inapplicable | 0 ms |
| `auth/cid/manifest#authn-cid-valid-credential` | MUST | inapplicable | 0 ms |
| `auth/cid/manifest#authn-cid-unknown-kid` | MUST | inapplicable | 0 ms |
| `auth/cid/manifest#authn-cid-bad-signature` | MUST | inapplicable | 0 ms |
| `auth/cid/manifest#authn-cid-expired` | MUST | inapplicable | 0 ms |
| `auth/cid/manifest#authn-cid-alg-none` | MUST | inapplicable | 0 ms |
| `auth/cid/manifest#authn-cid-claims-mismatch` | MUST | inapplicable | 0 ms |
| `auth/cid/manifest#authn-cid-document-id-mismatch` | MUST | inapplicable | 0 ms |
| `auth/cid/manifest#authn-cid-key-not-for-authentication` | MUST | inapplicable | 0 ms |
| `auth/cid/manifest#authn-cid-key-revoked` | MUST | inapplicable | 0 ms |
| `auth/cid/manifest#authn-cid-foreign-controller` | MUST | inapplicable | 0 ms |
| `auth/cid/manifest#authn-cid-referenced-method` | MUST | inapplicable | 0 ms |
| `auth/cid/manifest#authn-cid-didkey-valid-credential` | MUST | inapplicable | 0 ms |
| `auth/cid/manifest#authn-cid-didkey-invalid-signature` | MUST | inapplicable | 0 ms |
| `auth/cid/manifest#authn-cid-didkey-alg-none` | MUST | inapplicable | 0 ms |
| `auth/cid/manifest#authn-cid-didkey-expired` | MUST | inapplicable | 0 ms |
| `auth/cid/manifest#authn-cid-didkey-claims-mismatch` | MUST | inapplicable | 0 ms |
| `auth/cid/manifest#authn-cid-didkey-audience-excludes-as` | MUST | inapplicable | 0 ms |
| `auth/cid/manifest#authn-cid-didkey-missing-exp` | MUST | inapplicable | 0 ms |
| `auth/cid/manifest#authn-cid-didkey-missing-iat` | MUST | inapplicable | 0 ms |
| `auth/cid/manifest#authn-cid-didkey-missing-subject` | MUST | inapplicable | 0 ms |
| `auth/cid/manifest#authn-cid-didkey-missing-issuer` | MUST | inapplicable | 0 ms |
| `auth/cid/manifest#authn-cid-didkey-missing-client-id` | MUST | inapplicable | 0 ms |
| `auth/saml/manifest#authn-saml-valid-assertion` | MUST | inapplicable | 0 ms |
| `auth/saml/manifest#authn-saml-invalid-signature` | MUST | inapplicable | 0 ms |
| `auth/saml/manifest#authn-saml-unsigned` | MUST | inapplicable | 0 ms |
| `notifications/webhook/manifest#webhook-subscription-response` | MUST | inapplicable | 0 ms |
| `notifications/webhook/manifest#webhook-subscription-expires-supported` | MUST | inapplicable | 0 ms |
| `notifications/webhook/manifest#webhook-subscription-listed` | MUST | inapplicable | 0 ms |
| `notifications/webhook/manifest#webhook-subscription-get-delete` | MUST | inapplicable | 0 ms |
| `notifications/webhook/manifest#webhook-delivery-lws-json` | MUST | inapplicable | 0 ms |
| `notifications/webhook/manifest#webhook-delivery-signed` | SHOULD | inapplicable | 0 ms |
| `notifications/webhook/manifest#webhook-signature-components` | MUST | inapplicable | 0 ms |
| `notifications/webhook/manifest#webhook-signing-key-published` | MUST | inapplicable | 0 ms |
| `notifications/webhook/manifest#webhook-signature-verifies` | MUST | inapplicable | 0 ms |
| `notifications/webhook/manifest#webhook-delivery-retried` | MAY | inapplicable | 0 ms |
| `notifications/webhook/manifest#webhook-subscription-deactivated` | MAY | inapplicable | 0 ms |
| `index/manifest#index-services-advertised` | MUST | inapplicable | 0 ms |
| `index/manifest#type-index-lists-readable-types` | MUST | inapplicable | 0 ms |
| `index/manifest#type-index-omits-unreadable-type` | MUST | inapplicable | 0 ms |
| `index/manifest#type-index-not-shared` | MUST | inapplicable | 0 ms |
| `index/manifest#type-search-by-type` | MUST | inapplicable | 0 ms |
| `index/manifest#type-search-and-or` | MUST | inapplicable | 0 ms |
| `index/manifest#type-search-native-classes` | MUST | inapplicable | 0 ms |
| `index/manifest#type-search-no-match` | MUST | inapplicable | 0 ms |
| `index/manifest#type-search-duplicate-groups` | MUST | inapplicable | 0 ms |
| `index/manifest#type-search-at-members-ignored` | MUST | inapplicable | 0 ms |
| `index/manifest#type-search-empty-key-absent` | MUST | inapplicable | 0 ms |
| `index/manifest#type-search-empty-group-rejected` | MUST | inapplicable | 0 ms |
| `index/manifest#type-search-type-not-array-rejected` | MUST | inapplicable | 0 ms |
| `index/manifest#type-search-bad-element-rejected` | MUST | inapplicable | 0 ms |
| `index/manifest#type-search-malformed-json-rejected` | MUST | inapplicable | 0 ms |
| `index/manifest#type-search-relative-iri-rejected` | MUST | inapplicable | 0 ms |
| `index/manifest#type-search-missing-content-type-rejected` | MUST | inapplicable | 0 ms |
| `index/manifest#type-search-unsupported-format-rejected` | MUST | inapplicable | 0 ms |
| `index/manifest#type-search-unsupported-format-accept-query` | SHOULD | inapplicable | 0 ms |
| `index/manifest#type-search-accept-query-advertised` | SHOULD | inapplicable | 0 ms |
| `index/manifest#type-search-not-acceptable` | MUST | inapplicable | 0 ms |
| `index/manifest#type-search-unindexed-relation` | MUST | inapplicable | 0 ms |
| `index/manifest#type-search-structural-relation-not-indexed` | MUST | inapplicable | 0 ms |
| `index/manifest#type-search-authorization-filtered` | MUST | inapplicable | 0 ms |
| `index/manifest#type-search-revoked-not-shown` | MUST | inapplicable | 0 ms |
| `index/manifest#type-search-not-shared` | MUST | inapplicable | 0 ms |
| `index/manifest#type-search-type-from-link-header` | SHOULD | inapplicable | 0 ms |
| `index/manifest#type-search-type-from-content` | MAY | inapplicable | 0 ms |
| `index/manifest#type-search-content-types-identical` | MUST | inapplicable | 0 ms |
| `index/manifest#type-search-reflects-update` | SHOULD | inapplicable | 0 ms |
| `index/manifest#type-search-reflects-delete` | SHOULD | inapplicable | 0 ms |
| `index/manifest#type-search-vary-accept` | MUST | inapplicable | 0 ms |
| `index/manifest#type-search-safe` | MAY | inapplicable | 0 ms |
| `index/manifest#type-search-next-page` | MUST | inapplicable | 0 ms |
| `index/manifest#type-search-relation-filter` | MAY | inapplicable | 0 ms |
| `index/manifest#type-search-relation-cnf` | MAY | inapplicable | 0 ms |
| `index/manifest#type-search-relation-from-link-header` | SHOULD | inapplicable | 0 ms |
| `index/manifest#type-search-too-complex` | MUST | inapplicable | 0 ms |
| `index/manifest#type-search-unrecognized-page-link` | MUST | inapplicable | 0 ms |
| `index/manifest#type-search-content-location-protected` | MUST | inapplicable | 0 ms |

### Detail

**`core/discovery#discovery-unauthorized-response-headers`** — inapplicable

```
core/discovery#discovery-unauthorized-response-headers - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/linksets#linkset-put-405-when-unsupported`** — inapplicable

```
core/linksets#linkset-put-405-when-unsupported - inapplicable [MUST] (439 ms)
  inapplicable: precondition 'the linkset does not advertise PUT (otherwise this test does not apply)' does not hold: header Allow matches expected matches /(?i)^(?!.*\bPUT\b)/, got GET, HEAD, OPTIONS, PATCH, PUT
  step 'the linkset does not advertise PUT (otherwise this test does not apply)':
    FAILED header Allow matches
      expected: matches /(?i)^(?!.*\bPUT\b)/
      actual:   GET, HEAD, OPTIONS, PATCH, PUT
    exchange: GET http://127.0.0.1:33321/touchstone-run-9db984fc/linkset-put-405-when-unsupported/res1792618598?linkset -> 200
    response body: {"linkset":[{"anchor":"http://127.0.0.1:33321/touchstone-run-9db984fc/linkset-put-405-when-unsupported/res1792618598","up":[{"href":"http://127.0.0.1:33321/touchstone-run-9db984fc/linkset-put-405-when-unsupported/"}],"type":[{"href":"https://www.w3.org/ns/lws#DataResource"}],"https://www.w3.org/ns/lws#storage":[{"href":"http://127.0.0.1:33321/.well-known/lws-storage"}]}]}
```

**`core/moving#move-keeps-identifier-content-and-links`** — inapplicable

```
core/moving#move-keeps-identifier-content-and-links - inapplicable [MUST] (665 ms)
  inapplicable: precondition 'the storage's MoveResource says it preserves identifiers (otherwise this test does not apply)' does not hold: json /capability some expected some element satisfies [{"pointer":"/type","hasValue":"MoveResource"},{"pointer":"/preservesIdentifier","equals":true}], got [{"type":"MoveResource","appliesTo":["DataResource","Container"],"preservesIdentifier":false}]
  step 'the storage's MoveResource says it preserves identifiers (otherwise this test does not apply)':
    FAILED json /capability some
      expected: some element satisfies [{"pointer":"/type","hasValue":"MoveResource"},{"pointer":"/preservesIdentifier","equals":true}]
      actual:   [{"type":"MoveResource","appliesTo":["DataResource","Container"],"preservesIdentifier":false}]
    exchange: GET http://127.0.0.1:33321/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:33321/.well-known/lws-storage","type":"Storage","verificationMethod":[{"id":"http://127.0.0.1:33321/.well-known/lws-storage#notification-key-8f29fa97","type":"JsonWebKey","controller":"http://127.0.0.1:33321/.well-known/lws-storage","publicKeyJwk":{"kty":"OKP","crv":"Ed25519","x":"NNOqv0i1dqasL1NR5lst_dEjjvTWZilpYhI9LuCLnU4"}}],"authentication":["http://127.0.0.1:33321/.well-known/lws-storage#notification-key-8f29fa97"],"capability":[{"type":"MoveResource","appliesTo":["DataResource","Container"],"preservesIdentifier":false}],"service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:33321/"},{"type":"NotificationService","serviceEndpoint":"http://127.0.0.1:33321/.well-known/lws-subscriptions/","subscriptionType":["WebhookSubscription"]},{"type":"TypeIndexService","serviceEndpoint":"http://127.0.0.1:33321/.well-known/lws-type-index"},{"type":"TypeSearchService","serviceEndpoint":"http://127.0.0.1:33321/.well-known/lws-type-search","https://github.com/danbri/factoidal/issues/922#unstableResultsResource":"anticipatory and unstable: a QUERY answer carries Content-Location (RFC 10008 section 2.3) naming a results resource that lws10-index does not define; likely to change"},{"type":"AccessRequestService","serviceEndpoint":"http://127.0.0.1:33321/.well-known/lws-access-requests/","conformsTo":["https://www.w3.org/ns/lws#AccessProfile"]},{"type":"AccessGrantService","serviceEndpoint":"http://127.0.0.1:33321/.well-known/lws-access-grants/","conformsTo":["https://www.w3.org/ns/lws#AccessProfile"]}]}
```

**`core/moving#move-container-refused-without-container-support`** — inapplicable

```
core/moving#move-container-refused-without-container-support - inapplicable [MUST] (671 ms)
  inapplicable: precondition 'the storage moves data resources but not containers (otherwise this test does not apply)' does not hold: json /capability some expected some element satisfies [{"pointer":"/type","hasValue":"MoveResource"},{"pointer":"/appliesTo","optional":true,"none":[{"pointer":"","matches":"^(https://www\\.w3\\.org/ns/lws#)?Container$"}]}], got [{"type":"MoveResource","appliesTo":["DataResource","Container"],"preservesIdentifier":false}]
  step 'the storage moves data resources but not containers (otherwise this test does not apply)':
    FAILED json /capability some
      expected: some element satisfies [{"pointer":"/type","hasValue":"MoveResource"},{"pointer":"/appliesTo","optional":true,"none":[{"pointer":"","matches":"^(https://www\\.w3\\.org/ns/lws#)?Container$"}]}]
      actual:   [{"type":"MoveResource","appliesTo":["DataResource","Container"],"preservesIdentifier":false}]
    exchange: GET http://127.0.0.1:33321/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:33321/.well-known/lws-storage","type":"Storage","verificationMethod":[{"id":"http://127.0.0.1:33321/.well-known/lws-storage#notification-key-8f29fa97","type":"JsonWebKey","controller":"http://127.0.0.1:33321/.well-known/lws-storage","publicKeyJwk":{"kty":"OKP","crv":"Ed25519","x":"NNOqv0i1dqasL1NR5lst_dEjjvTWZilpYhI9LuCLnU4"}}],"authentication":["http://127.0.0.1:33321/.well-known/lws-storage#notification-key-8f29fa97"],"capability":[{"type":"MoveResource","appliesTo":["DataResource","Container"],"preservesIdentifier":false}],"service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:33321/"},{"type":"NotificationService","serviceEndpoint":"http://127.0.0.1:33321/.well-known/lws-subscriptions/","subscriptionType":["WebhookSubscription"]},{"type":"TypeIndexService","serviceEndpoint":"http://127.0.0.1:33321/.well-known/lws-type-index"},{"type":"TypeSearchService","serviceEndpoint":"http://127.0.0.1:33321/.well-known/lws-type-search","https://github.com/danbri/factoidal/issues/922#unstableResultsResource":"anticipatory and unstable: a QUERY answer carries Content-Location (RFC 10008 section 2.3) naming a results resource that lws10-index does not define; likely to change"},{"type":"AccessRequestService","serviceEndpoint":"http://127.0.0.1:33321/.well-known/lws-access-requests/","conformsTo":["https://www.w3.org/ns/lws#AccessProfile"]},{"type":"AccessGrantService","serviceEndpoint":"http://127.0.0.1:33321/.well-known/lws-access-grants/","conformsTo":["https://www.w3.org/ns/lws#AccessProfile"]}]}
```

**`core/moving#move-refused-without-capability`** — inapplicable

```
core/moving#move-refused-without-capability - inapplicable [MUST] (581 ms)
  inapplicable: precondition 'the storage describes no MoveResource capability (otherwise this test does not apply)' does not hold: json /capability none expected none element satisfies [{"pointer":"/type","hasValue":"MoveResource"}], got [{"type":"MoveResource","appliesTo":["DataResource","Container"],"preservesIdentifier":false}]
  step 'the storage describes no MoveResource capability (otherwise this test does not apply)':
    FAILED json /capability none
      expected: none element satisfies [{"pointer":"/type","hasValue":"MoveResource"}]
      actual:   [{"type":"MoveResource","appliesTo":["DataResource","Container"],"preservesIdentifier":false}]
    exchange: GET http://127.0.0.1:33321/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:33321/.well-known/lws-storage","type":"Storage","verificationMethod":[{"id":"http://127.0.0.1:33321/.well-known/lws-storage#notification-key-8f29fa97","type":"JsonWebKey","controller":"http://127.0.0.1:33321/.well-known/lws-storage","publicKeyJwk":{"kty":"OKP","crv":"Ed25519","x":"NNOqv0i1dqasL1NR5lst_dEjjvTWZilpYhI9LuCLnU4"}}],"authentication":["http://127.0.0.1:33321/.well-known/lws-storage#notification-key-8f29fa97"],"capability":[{"type":"MoveResource","appliesTo":["DataResource","Container"],"preservesIdentifier":false}],"service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:33321/"},{"type":"NotificationService","serviceEndpoint":"http://127.0.0.1:33321/.well-known/lws-subscriptions/","subscriptionType":["WebhookSubscription"]},{"type":"TypeIndexService","serviceEndpoint":"http://127.0.0.1:33321/.well-known/lws-type-index"},{"type":"TypeSearchService","serviceEndpoint":"http://127.0.0.1:33321/.well-known/lws-type-search","https://github.com/danbri/factoidal/issues/922#unstableResultsResource":"anticipatory and unstable: a QUERY answer carries Content-Location (RFC 10008 section 2.3) naming a results resource that lws10-index does not define; likely to change"},{"type":"AccessRequestService","serviceEndpoint":"http://127.0.0.1:33321/.well-known/lws-access-requests/","conformsTo":["https://www.w3.org/ns/lws#AccessProfile"]},{"type":"AccessGrantService","serviceEndpoint":"http://127.0.0.1:33321/.well-known/lws-access-grants/","conformsTo":["https://www.w3.org/ns/lws#AccessProfile"]}]}
```

**`core/moving#move-needs-create-in-destination`** — inapplicable

```
core/moving#move-needs-create-in-destination - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/moving#move-needs-delete-of-resource`** — inapplicable

```
core/moving#move-needs-delete-of-resource - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/moving#move-notification`** — inapplicable

```
core/moving#move-notification - inapplicable [MUST]
  inapplicable: the target does not declare ReachableFixtures
```

**`core/storage_authorization#getContainer-private-unauthorized`** — inapplicable

```
core/storage_authorization#getContainer-private-unauthorized - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/storage_authorization#protected-resource-metadata`** — inapplicable

```
core/storage_authorization#protected-resource-metadata - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/storage_authorization#protected-resource-metadata-data-resource`** — inapplicable

```
core/storage_authorization#protected-resource-metadata-data-resource - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/storage_authorization#storage-root-same-origin`** — inapplicable

```
core/storage_authorization#storage-root-same-origin - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/storage_authorization#getContainer-authenticated-owner`** — inapplicable

```
core/storage_authorization#getContainer-authenticated-owner - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/storage_authorization#createDataResource-unauthorized`** — inapplicable

```
core/storage_authorization#createDataResource-unauthorized - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/storage_authorization#updateDataResource-unauthorized`** — inapplicable

```
core/storage_authorization#updateDataResource-unauthorized - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/storage_authorization#deleteDataResource-unauthorized`** — inapplicable

```
core/storage_authorization#deleteDataResource-unauthorized - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/storage_authorization#authz-non-owner-read-rejected`** — inapplicable

```
core/storage_authorization#authz-non-owner-read-rejected - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/storage_authorization#authz-non-owner-write-rejected`** — inapplicable

```
core/storage_authorization#authz-non-owner-write-rejected - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/storage_authorization#authz-non-owner-delete-rejected`** — inapplicable

```
core/storage_authorization#authz-non-owner-delete-rejected - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/storage_authorization#authz-expired-token-rejected`** — inapplicable

```
core/storage_authorization#authz-expired-token-rejected - inapplicable [MUST] (1 ms)
  inapplicable: the target does not declare Authentication
```

**`core/storage_authorization#authz-token-bad-signature-rejected`** — inapplicable

```
core/storage_authorization#authz-token-bad-signature-rejected - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/storage_authorization#authz-token-alg-none-rejected`** — inapplicable

```
core/storage_authorization#authz-token-alg-none-rejected - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/storage_authorization#authz-token-unknown-key-rejected`** — inapplicable

```
core/storage_authorization#authz-token-unknown-key-rejected - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/storage_authorization#authz-token-wrong-audience-rejected`** — inapplicable

```
core/storage_authorization#authz-token-wrong-audience-rejected - inapplicable [MUST]
  inapplicable: the target does not declare Authentication, HarnessIssuedTokens
```

**`core/storage_authorization#authz-token-wrong-issuer-rejected`** — inapplicable

```
core/storage_authorization#authz-token-wrong-issuer-rejected - inapplicable [MUST] (1 ms)
  inapplicable: the target does not declare Authentication, HarnessIssuedTokens
```

**`core/storage_authorization#authz-token-not-yet-valid-rejected`** — inapplicable

```
core/storage_authorization#authz-token-not-yet-valid-rejected - inapplicable [MUST]
  inapplicable: the target does not declare Authentication, HarnessIssuedTokens
```

**`core/storage_authorization#authz-token-issued-in-future-rejected`** — inapplicable

```
core/storage_authorization#authz-token-issued-in-future-rejected - inapplicable [MUST]
  inapplicable: the target does not declare Authentication, HarnessIssuedTokens
```

**`core/authorization_server#authz-server-metadata-well-known`** — inapplicable

```
core/authorization_server#authz-server-metadata-well-known - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/authorization_server#authz-metadata-subject-token-types`** — inapplicable

```
core/authorization_server#authz-metadata-subject-token-types - inapplicable [SHOULD]
  inapplicable: the target does not declare Authentication
```

**`core/authorization_server#authz-metadata-subject-token-types-are-uris`** — inapplicable

```
core/authorization_server#authz-metadata-subject-token-types-are-uris - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/authorization_server#authz-metadata-subject-identifier-types`** — inapplicable

```
core/authorization_server#authz-metadata-subject-identifier-types - inapplicable [SHOULD]
  inapplicable: the target does not declare Authentication
```

**`core/authorization_server#authz-token-exchange-valid`** — inapplicable

```
core/authorization_server#authz-token-exchange-valid - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/authorization_server#authz-token-exchange-invalid-resource`** — inapplicable

```
core/authorization_server#authz-token-exchange-invalid-resource - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/authorization_server#authz-token-exchange-missing-resource`** — inapplicable

```
core/authorization_server#authz-token-exchange-missing-resource - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/authorization_server#authz-token-exchange-missing-subject-token`** — inapplicable

```
core/authorization_server#authz-token-exchange-missing-subject-token - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/authorization_server#authz-issued-token-accepted-by-storage`** — inapplicable

```
core/authorization_server#authz-issued-token-accepted-by-storage - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/access_grants#access-grant-create`** — inapplicable

```
core/access_grants#access-grant-create - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/access_grants#access-grant-revoke`** — inapplicable

```
core/access_grants#access-grant-revoke - inapplicable [SHOULD]
  inapplicable: the target does not declare Authentication
```

**`core/access_grants#getContainer-public-read`** — inapplicable

```
core/access_grants#getContainer-public-read - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/access_grants#readDataResource-public-read`** — inapplicable

```
core/access_grants#readDataResource-public-read - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/access_grants#access-grant-authenticated-agent`** — inapplicable

```
core/access_grants#access-grant-authenticated-agent - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/access_grants#access-grant-extra-properties-accepted`** — inapplicable

```
core/access_grants#access-grant-extra-properties-accepted - inapplicable [MAY]
  inapplicable: the target does not declare Authentication
```

**`core/access_grants#access-grant-inbox-notified`** — inapplicable

```
core/access_grants#access-grant-inbox-notified - inapplicable [SHOULD]
  inapplicable: the target does not declare Authentication, ReachableFixtures
```

**`core/access_grants#access-request-create`** — inapplicable

```
core/access_grants#access-request-create - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/access_grants#access-grant-document-shape`** — inapplicable

```
core/access_grants#access-grant-document-shape - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/access_grants#access-grant-incomplete-refused`** — inapplicable

```
core/access_grants#access-grant-incomplete-refused - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/access_grants#access-grant-constraints-all-satisfied`** — inapplicable

```
core/access_grants#access-grant-constraints-all-satisfied - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/access_grants#access-grant-left-operands-accepted`** — inapplicable

```
core/access_grants#access-grant-left-operands-accepted - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/access_grants#access-grant-constraint-format`** — inapplicable

```
core/access_grants#access-grant-constraint-format - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/access_grants#access-grant-constraint-type`** — inapplicable

```
core/access_grants#access-grant-constraint-type - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/access_grants#access-grant-constraint-client`** — inapplicable

```
core/access_grants#access-grant-constraint-client - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/access_grants#container-listing-filtered-metadata`** — inapplicable

```
core/access_grants#container-listing-filtered-metadata - inapplicable [MAY]
  inapplicable: the target does not declare Authentication
```

**`core/notifications#subscription-unreadable-topic-refused`** — inapplicable

```
core/notifications#subscription-unreadable-topic-refused - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/notifications#subscription-after-revocation-refused`** — inapplicable

```
core/notifications#subscription-after-revocation-refused - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`core/notifications#notification-delivered-create`** — inapplicable

```
core/notifications#notification-delivered-create - inapplicable [MUST]
  inapplicable: the target does not declare ReachableFixtures
```

**`core/notifications#notification-delivered-update`** — inapplicable

```
core/notifications#notification-delivered-update - inapplicable [MUST]
  inapplicable: the target does not declare ReachableFixtures
```

**`core/notifications#notification-delivered-delete`** — inapplicable

```
core/notifications#notification-delivered-delete - inapplicable [MUST]
  inapplicable: the target does not declare ReachableFixtures
```

**`core/notifications#notification-not-delivered-for-unreadable-resource`** — inapplicable

```
core/notifications#notification-not-delivered-for-unreadable-resource - inapplicable [MUST]
  inapplicable: the target does not declare Authentication, ReachableFixtures
```

**`core/notifications#notification-stops-after-revocation`** — inapplicable

```
core/notifications#notification-stops-after-revocation - inapplicable [MUST]
  inapplicable: the target does not declare Authentication, ReachableFixtures
```

**`core/notifications#notification-actor-omitted`** — inapplicable

```
core/notifications#notification-actor-omitted - inapplicable [SHOULD]
  inapplicable: the target does not declare ReachableFixtures
```

**`core/notifications#notification-delivered-in-subcontainer`** — inapplicable

```
core/notifications#notification-delivered-in-subcontainer - inapplicable [MUST]
  inapplicable: the target does not declare ReachableFixtures
```

**`core/notifications#notification-scope-data-resource-only`** — inapplicable

```
core/notifications#notification-scope-data-resource-only - inapplicable [MUST]
  inapplicable: the target does not declare ReachableFixtures
```

**`core/pagination#pagination-single-page`** — inapplicable

```
core/pagination#pagination-single-page - inapplicable [MUST] (683 ms)
  inapplicable: precondition 'the listing is paginated and holds all five members on its page (otherwise this test does not apply)' does not hold: json /items/4 selects a value expected a value at /items/4, got nothing
  step 'the listing is paginated and holds all five members on its page (otherwise this test does not apply)':
    FAILED json /items/4 selects a value
      expected: a value at /items/4
      actual:   nothing
    exchange: GET http://127.0.0.1:33321/touchstone-run-9db984fc/pagination-single-page/paged/ -> 200
    response body: {"@context":"https://www.w3.org/ns/lws/v1","id":"http://127.0.0.1:33321/touchstone-run-9db984fc/pagination-single-page/paged/","type":"Container","totalItems":5,"items":[{"id":"http://127.0.0.1:33321/touchstone-run-9db984fc/pagination-single-page/paged/res1792618599","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T21:36:39Z"},{"id":"http://127.0.0.1:33321/touchstone-run-9db984fc/pagination-single-page/paged/res1792618599-1","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T21:36:39Z"},{"id":"http://127.0.0.1:33321/touchstone-run-9db984fc/pagination-single-page/paged/res1792618600","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T21:36:40Z"},{"id":"http://127.0.0.1:33321/touchstone-run-9db984fc/pagination-single-page/paged/res1792618600-1","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T21:36:40Z"}]}
```

**`auth/oidc/manifest#authn-oidc-valid-id-token`** — inapplicable

```
auth/oidc/manifest#authn-oidc-valid-id-token - inapplicable [MUST]
  inapplicable: the target does not declare Authentication, ReachableFixtures
```

**`auth/oidc/manifest#authn-oidc-expired-id-token`** — inapplicable

```
auth/oidc/manifest#authn-oidc-expired-id-token - inapplicable [MUST]
  inapplicable: the target does not declare Authentication, ReachableFixtures
```

**`auth/oidc/manifest#authn-oidc-alg-none`** — inapplicable

```
auth/oidc/manifest#authn-oidc-alg-none - inapplicable [MUST]
  inapplicable: the target does not declare Authentication, ReachableFixtures
```

**`auth/oidc/manifest#authn-oidc-bad-signature`** — inapplicable

```
auth/oidc/manifest#authn-oidc-bad-signature - inapplicable [MUST]
  inapplicable: the target does not declare Authentication, ReachableFixtures
```

**`auth/oidc/manifest#authn-oidc-untrusted-issuer`** — inapplicable

```
auth/oidc/manifest#authn-oidc-untrusted-issuer - inapplicable [MUST]
  inapplicable: the target does not declare Authentication, ReachableFixtures
```

**`auth/oidc/manifest#authn-oidc-missing-azp`** — inapplicable

```
auth/oidc/manifest#authn-oidc-missing-azp - inapplicable [MUST]
  inapplicable: the target does not declare Authentication, ReachableFixtures
```

**`auth/cid/manifest#authn-cid-valid-credential`** — inapplicable

```
auth/cid/manifest#authn-cid-valid-credential - inapplicable [MUST]
  inapplicable: the target does not declare Authentication, ReachableFixtures
```

**`auth/cid/manifest#authn-cid-unknown-kid`** — inapplicable

```
auth/cid/manifest#authn-cid-unknown-kid - inapplicable [MUST]
  inapplicable: the target does not declare Authentication, ReachableFixtures
```

**`auth/cid/manifest#authn-cid-bad-signature`** — inapplicable

```
auth/cid/manifest#authn-cid-bad-signature - inapplicable [MUST]
  inapplicable: the target does not declare Authentication, ReachableFixtures
```

**`auth/cid/manifest#authn-cid-expired`** — inapplicable

```
auth/cid/manifest#authn-cid-expired - inapplicable [MUST]
  inapplicable: the target does not declare Authentication, ReachableFixtures
```

**`auth/cid/manifest#authn-cid-alg-none`** — inapplicable

```
auth/cid/manifest#authn-cid-alg-none - inapplicable [MUST]
  inapplicable: the target does not declare Authentication, ReachableFixtures
```

**`auth/cid/manifest#authn-cid-claims-mismatch`** — inapplicable

```
auth/cid/manifest#authn-cid-claims-mismatch - inapplicable [MUST]
  inapplicable: the target does not declare Authentication, ReachableFixtures
```

**`auth/cid/manifest#authn-cid-document-id-mismatch`** — inapplicable

```
auth/cid/manifest#authn-cid-document-id-mismatch - inapplicable [MUST]
  inapplicable: the target does not declare Authentication, ReachableFixtures
```

**`auth/cid/manifest#authn-cid-key-not-for-authentication`** — inapplicable

```
auth/cid/manifest#authn-cid-key-not-for-authentication - inapplicable [MUST]
  inapplicable: the target does not declare Authentication, ReachableFixtures
```

**`auth/cid/manifest#authn-cid-key-revoked`** — inapplicable

```
auth/cid/manifest#authn-cid-key-revoked - inapplicable [MUST]
  inapplicable: the target does not declare Authentication, ReachableFixtures
```

**`auth/cid/manifest#authn-cid-foreign-controller`** — inapplicable

```
auth/cid/manifest#authn-cid-foreign-controller - inapplicable [MUST]
  inapplicable: the target does not declare Authentication, ReachableFixtures
```

**`auth/cid/manifest#authn-cid-referenced-method`** — inapplicable

```
auth/cid/manifest#authn-cid-referenced-method - inapplicable [MUST]
  inapplicable: the target does not declare Authentication, ReachableFixtures
```

**`auth/cid/manifest#authn-cid-didkey-valid-credential`** — inapplicable

```
auth/cid/manifest#authn-cid-didkey-valid-credential - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`auth/cid/manifest#authn-cid-didkey-invalid-signature`** — inapplicable

```
auth/cid/manifest#authn-cid-didkey-invalid-signature - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`auth/cid/manifest#authn-cid-didkey-alg-none`** — inapplicable

```
auth/cid/manifest#authn-cid-didkey-alg-none - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`auth/cid/manifest#authn-cid-didkey-expired`** — inapplicable

```
auth/cid/manifest#authn-cid-didkey-expired - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`auth/cid/manifest#authn-cid-didkey-claims-mismatch`** — inapplicable

```
auth/cid/manifest#authn-cid-didkey-claims-mismatch - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`auth/cid/manifest#authn-cid-didkey-audience-excludes-as`** — inapplicable

```
auth/cid/manifest#authn-cid-didkey-audience-excludes-as - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`auth/cid/manifest#authn-cid-didkey-missing-exp`** — inapplicable

```
auth/cid/manifest#authn-cid-didkey-missing-exp - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`auth/cid/manifest#authn-cid-didkey-missing-iat`** — inapplicable

```
auth/cid/manifest#authn-cid-didkey-missing-iat - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`auth/cid/manifest#authn-cid-didkey-missing-subject`** — inapplicable

```
auth/cid/manifest#authn-cid-didkey-missing-subject - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`auth/cid/manifest#authn-cid-didkey-missing-issuer`** — inapplicable

```
auth/cid/manifest#authn-cid-didkey-missing-issuer - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`auth/cid/manifest#authn-cid-didkey-missing-client-id`** — inapplicable

```
auth/cid/manifest#authn-cid-didkey-missing-client-id - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`auth/saml/manifest#authn-saml-valid-assertion`** — inapplicable

```
auth/saml/manifest#authn-saml-valid-assertion - inapplicable [MUST]
  inapplicable: the target does not declare Authentication, SamlTrust
```

**`auth/saml/manifest#authn-saml-invalid-signature`** — inapplicable

```
auth/saml/manifest#authn-saml-invalid-signature - inapplicable [MUST]
  inapplicable: the target does not declare Authentication, SamlTrust
```

**`auth/saml/manifest#authn-saml-unsigned`** — inapplicable

```
auth/saml/manifest#authn-saml-unsigned - inapplicable [MUST]
  inapplicable: the target does not declare Authentication, SamlTrust
```

**`notifications/webhook/manifest#webhook-subscription-response`** — inapplicable

```
notifications/webhook/manifest#webhook-subscription-response - inapplicable [MUST]
  inapplicable: the target does not declare ReachableFixtures
```

**`notifications/webhook/manifest#webhook-subscription-expires-supported`** — inapplicable

```
notifications/webhook/manifest#webhook-subscription-expires-supported - inapplicable [MUST]
  inapplicable: the target does not declare ReachableFixtures
```

**`notifications/webhook/manifest#webhook-subscription-listed`** — inapplicable

```
notifications/webhook/manifest#webhook-subscription-listed - inapplicable [MUST]
  inapplicable: the target does not declare Authentication, ReachableFixtures
```

**`notifications/webhook/manifest#webhook-subscription-get-delete`** — inapplicable

```
notifications/webhook/manifest#webhook-subscription-get-delete - inapplicable [MUST]
  inapplicable: the target does not declare ReachableFixtures
```

**`notifications/webhook/manifest#webhook-delivery-lws-json`** — inapplicable

```
notifications/webhook/manifest#webhook-delivery-lws-json - inapplicable [MUST]
  inapplicable: the target does not declare ReachableFixtures
```

**`notifications/webhook/manifest#webhook-delivery-signed`** — inapplicable

```
notifications/webhook/manifest#webhook-delivery-signed - inapplicable [SHOULD]
  inapplicable: the target does not declare ReachableFixtures
```

**`notifications/webhook/manifest#webhook-signature-components`** — inapplicable

```
notifications/webhook/manifest#webhook-signature-components - inapplicable [MUST]
  inapplicable: the target does not declare ReachableFixtures
```

**`notifications/webhook/manifest#webhook-signing-key-published`** — inapplicable

```
notifications/webhook/manifest#webhook-signing-key-published - inapplicable [MUST]
  inapplicable: the target does not declare ReachableFixtures
```

**`notifications/webhook/manifest#webhook-signature-verifies`** — inapplicable

```
notifications/webhook/manifest#webhook-signature-verifies - inapplicable [MUST]
  inapplicable: the target does not declare ReachableFixtures
```

**`notifications/webhook/manifest#webhook-delivery-retried`** — inapplicable

```
notifications/webhook/manifest#webhook-delivery-retried - inapplicable [MAY]
  inapplicable: the target does not declare ReachableFixtures
```

**`notifications/webhook/manifest#webhook-subscription-deactivated`** — inapplicable

```
notifications/webhook/manifest#webhook-subscription-deactivated - inapplicable [MAY]
  inapplicable: the target does not declare ReachableFixtures
```

**`index/manifest#index-services-advertised`** — inapplicable

```
index/manifest#index-services-advertised - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-index-lists-readable-types`** — inapplicable

```
index/manifest#type-index-lists-readable-types - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-index-omits-unreadable-type`** — inapplicable

```
index/manifest#type-index-omits-unreadable-type - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-index-not-shared`** — inapplicable

```
index/manifest#type-index-not-shared - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-by-type`** — inapplicable

```
index/manifest#type-search-by-type - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-and-or`** — inapplicable

```
index/manifest#type-search-and-or - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-native-classes`** — inapplicable

```
index/manifest#type-search-native-classes - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-no-match`** — inapplicable

```
index/manifest#type-search-no-match - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-duplicate-groups`** — inapplicable

```
index/manifest#type-search-duplicate-groups - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-at-members-ignored`** — inapplicable

```
index/manifest#type-search-at-members-ignored - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-empty-key-absent`** — inapplicable

```
index/manifest#type-search-empty-key-absent - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-empty-group-rejected`** — inapplicable

```
index/manifest#type-search-empty-group-rejected - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-type-not-array-rejected`** — inapplicable

```
index/manifest#type-search-type-not-array-rejected - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-bad-element-rejected`** — inapplicable

```
index/manifest#type-search-bad-element-rejected - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-malformed-json-rejected`** — inapplicable

```
index/manifest#type-search-malformed-json-rejected - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-relative-iri-rejected`** — inapplicable

```
index/manifest#type-search-relative-iri-rejected - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-missing-content-type-rejected`** — inapplicable

```
index/manifest#type-search-missing-content-type-rejected - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-unsupported-format-rejected`** — inapplicable

```
index/manifest#type-search-unsupported-format-rejected - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-unsupported-format-accept-query`** — inapplicable

```
index/manifest#type-search-unsupported-format-accept-query - inapplicable [SHOULD]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-accept-query-advertised`** — inapplicable

```
index/manifest#type-search-accept-query-advertised - inapplicable [SHOULD]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-not-acceptable`** — inapplicable

```
index/manifest#type-search-not-acceptable - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-unindexed-relation`** — inapplicable

```
index/manifest#type-search-unindexed-relation - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-structural-relation-not-indexed`** — inapplicable

```
index/manifest#type-search-structural-relation-not-indexed - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-authorization-filtered`** — inapplicable

```
index/manifest#type-search-authorization-filtered - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-revoked-not-shown`** — inapplicable

```
index/manifest#type-search-revoked-not-shown - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-not-shared`** — inapplicable

```
index/manifest#type-search-not-shared - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-type-from-link-header`** — inapplicable

```
index/manifest#type-search-type-from-link-header - inapplicable [SHOULD]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-type-from-content`** — inapplicable

```
index/manifest#type-search-type-from-content - inapplicable [MAY]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-content-types-identical`** — inapplicable

```
index/manifest#type-search-content-types-identical - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-reflects-update`** — inapplicable

```
index/manifest#type-search-reflects-update - inapplicable [SHOULD]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-reflects-delete`** — inapplicable

```
index/manifest#type-search-reflects-delete - inapplicable [SHOULD]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-vary-accept`** — inapplicable

```
index/manifest#type-search-vary-accept - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-safe`** — inapplicable

```
index/manifest#type-search-safe - inapplicable [MAY]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-next-page`** — inapplicable

```
index/manifest#type-search-next-page - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-relation-filter`** — inapplicable

```
index/manifest#type-search-relation-filter - inapplicable [MAY]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-relation-cnf`** — inapplicable

```
index/manifest#type-search-relation-cnf - inapplicable [MAY]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-relation-from-link-header`** — inapplicable

```
index/manifest#type-search-relation-from-link-header - inapplicable [SHOULD]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-too-complex`** — inapplicable

```
index/manifest#type-search-too-complex - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-unrecognized-page-link`** — inapplicable

```
index/manifest#type-search-unrecognized-page-link - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

**`index/manifest#type-search-content-location-protected`** — inapplicable

```
index/manifest#type-search-content-location-protected - inapplicable [MUST]
  inapplicable: the target does not declare Authentication
```

## Requirement matrix

| requirement | level | result | tests |
|---|---|---|---:|
| [`id-token-alg-not-none`](https://www.w3.org/TR/lws10-authn-openid/#serialization) | MUST | INAPPLICABLE | 1 |
| [`id-token-aud-claim`](https://www.w3.org/TR/lws10-authn-openid/#serialization) | MUST | INAPPLICABLE | 1 |
| [`id-token-azp-claim`](https://www.w3.org/TR/lws10-authn-openid/#serialization) | MUST | INAPPLICABLE | 2 |
| [`id-token-iss-claim`](https://www.w3.org/TR/lws10-authn-openid/#serialization) | MUST | INAPPLICABLE | 1 |
| [`id-token-sub-claim`](https://www.w3.org/TR/lws10-authn-openid/#serialization) | MUST | INAPPLICABLE | 1 |
| [`id-token-token-type-uri`](https://www.w3.org/TR/lws10-authn-openid/#token-type) | MUST | INAPPLICABLE | 1 |
| [`validation-dereference-subject-cid`](https://www.w3.org/TR/lws10-authn-openid/#validation) | MUST | INAPPLICABLE | 2 |
| [`validation-locate-issuer-service-and-verify`](https://www.w3.org/TR/lws10-authn-openid/#validation) | MUST | INAPPLICABLE | 4 |
| [`audience-restriction`](https://www.w3.org/TR/lws10-authn-saml/#serialization) | MUST | INAPPLICABLE | 1 |
| [`issuer-assertion`](https://www.w3.org/TR/lws10-authn-saml/#serialization) | MUST | INAPPLICABLE | 1 |
| [`nameid-subject`](https://www.w3.org/TR/lws10-authn-saml/#serialization) | MUST | INAPPLICABLE | 1 |
| [`recipient-client-id`](https://www.w3.org/TR/lws10-authn-saml/#serialization) | MUST | INAPPLICABLE | 1 |
| [`signed-and-required-assertions`](https://www.w3.org/TR/lws10-authn-saml/#serialization) | MUST | INAPPLICABLE | 2 |
| [`token-type-saml2`](https://www.w3.org/TR/lws10-authn-saml/#token-type) | MUST | INAPPLICABLE | 1 |
| [`validation-signature`](https://www.w3.org/TR/lws10-authn-saml/#validation) | MUST | INAPPLICABLE | 2 |
| [`alg-not-none`](https://www.w3.org/TR/lws10-authn-ssi-cid/#serialization) | MUST | INAPPLICABLE | 2 |
| [`aud-includes-as`](https://www.w3.org/TR/lws10-authn-ssi-cid/#serialization) | MUST | INAPPLICABLE | 3 |
| [`client-id-claim`](https://www.w3.org/TR/lws10-authn-ssi-cid/#serialization) | MUST | INAPPLICABLE | 2 |
| [`exp-claim`](https://www.w3.org/TR/lws10-authn-ssi-cid/#serialization) | MUST | INAPPLICABLE | 3 |
| [`iat-claim`](https://www.w3.org/TR/lws10-authn-ssi-cid/#serialization) | MUST | INAPPLICABLE | 3 |
| [`iss-claim`](https://www.w3.org/TR/lws10-authn-ssi-cid/#serialization) | MUST | INAPPLICABLE | 2 |
| [`sub-claim`](https://www.w3.org/TR/lws10-authn-ssi-cid/#serialization) | MUST | INAPPLICABLE | 2 |
| [`sub-iss-client-same-uri`](https://www.w3.org/TR/lws10-authn-ssi-cid/#serialization) | MUST | INAPPLICABLE | 7 |
| [`token-type-jwt`](https://www.w3.org/TR/lws10-authn-ssi-cid/#token-type) | MUST | INAPPLICABLE | 2 |
| [`validation-all-claims`](https://www.w3.org/TR/lws10-authn-ssi-cid/#validation) | MUST | INAPPLICABLE | 8 |
| [`validation-dereference-sub-cid`](https://www.w3.org/TR/lws10-authn-ssi-cid/#validation) | MUST | INAPPLICABLE | 4 |
| [`validation-exp-in-future`](https://www.w3.org/TR/lws10-authn-ssi-cid/#validation) | MUST | INAPPLICABLE | 4 |
| [`validation-kid-verification-method`](https://www.w3.org/TR/lws10-authn-ssi-cid/#validation) | MUST | INAPPLICABLE | 9 |
| [`validation-reject-alg-none`](https://www.w3.org/TR/lws10-authn-ssi-cid/#validation) | MUST | INAPPLICABLE | 1 |
| [`access-access-collection`](https://www.w3.org/TR/lws10-core/#access-property) | MUST | INAPPLICABLE | 2 |
| [`access-access-required`](https://www.w3.org/TR/lws10-core/#access-property) | MUST | INAPPLICABLE | 2 |
| [`access-endpoints-are-lws-containers`](https://www.w3.org/TR/lws10-core/#access-protocol) | MUST | PASS | 1 |
| [`access-endpoints-get-post-delete`](https://www.w3.org/TR/lws10-core/#access-protocol) | SHOULD | INAPPLICABLE | 1 |
| [`access-endpoints-jsonld-payloads`](https://www.w3.org/TR/lws10-core/#access-protocol) | MUST | INAPPLICABLE | 1 |
| [`access-extra-properties-allowed`](https://www.w3.org/TR/lws10-core/#access-data-model) | MAY | INAPPLICABLE | 1 |
| [`access-inbox-notifications`](https://www.w3.org/TR/lws10-core/#access-notifications) | SHOULD | INAPPLICABLE | 1 |
| [`access-inbox-optional`](https://www.w3.org/TR/lws10-core/#access-inbox-property) | MAY | INAPPLICABLE | 1 |
| [`access-inbox-uri`](https://www.w3.org/TR/lws10-core/#access-inbox-property) | MUST | INAPPLICABLE | 1 |
| [`access-jsonld-context-lws-v1`](https://www.w3.org/TR/lws10-core/#json-ld-serialization) | MUST | INAPPLICABLE | 1 |
| [`access-notification-data-model`](https://www.w3.org/TR/lws10-core/#access-notifications) | MUST | INAPPLICABLE | 1 |
| [`access-notification-delivery`](https://www.w3.org/TR/lws10-core/#access-notifications) | MUST | INAPPLICABLE | 1 |
| [`access-notification-events`](https://www.w3.org/TR/lws10-core/#access-notification-events) | SHOULD | INAPPLICABLE | 1 |
| [`access-notify-grant-created`](https://www.w3.org/TR/lws10-core/#access-notification-events) | SHOULD | UNCOVERED | 0 |
| [`access-notify-other-events`](https://www.w3.org/TR/lws10-core/#access-notification-events) | MAY | UNCOVERED | 0 |
| [`access-notify-request-created`](https://www.w3.org/TR/lws10-core/#access-notification-events) | SHOULD | UNCOVERED | 0 |
| [`access-post-location-header`](https://www.w3.org/TR/lws10-core/#access-protocol) | MUST | INAPPLICABLE | 2 |
| [`access-services-advertised`](https://www.w3.org/TR/lws10-core/#access-discovery) | MUST | PASS | 1 |
| [`access-storage-required`](https://www.w3.org/TR/lws10-core/#access-storage-property) | MUST | INAPPLICABLE | 2 |
| [`access-storage-uri`](https://www.w3.org/TR/lws10-core/#access-storage-property) | MUST | INAPPLICABLE | 1 |
| [`access-type-required`](https://www.w3.org/TR/lws10-core/#access-type-property) | MUST | INAPPLICABLE | 2 |
| [`access-type-values`](https://www.w3.org/TR/lws10-core/#access-type-property) | MUST | INAPPLICABLE | 2 |
| [`authn-audience-restriction-recommended`](https://www.w3.org/TR/lws10-core/#authentication-data-model) | SHOULD | INAPPLICABLE | 1 |
| [`authn-client-claim`](https://www.w3.org/TR/lws10-core/#authentication-data-model) | MUST | INAPPLICABLE | 2 |
| [`authn-credential-signed`](https://www.w3.org/TR/lws10-core/#authentication-validation) | MUST | INAPPLICABLE | 8 |
| [`authn-credential-tamper-evident-claims`](https://www.w3.org/TR/lws10-core/#authentication-data-model) | MUST | INAPPLICABLE | 3 |
| [`authn-issuer-claim-uri`](https://www.w3.org/TR/lws10-core/#authentication-data-model) | MUST | INAPPLICABLE | 1 |
| [`authn-issuer-trust-out-of-band`](https://www.w3.org/TR/lws10-core/#authentication-validation) | MAY | UNCOVERED | 0 |
| [`authn-subject-claim-uri`](https://www.w3.org/TR/lws10-core/#authentication-data-model) | MUST | INAPPLICABLE | 1 |
| [`authn-suite-token-type-uri`](https://www.w3.org/TR/lws10-core/#authentication-type-identifier) | MUST | INAPPLICABLE | 1 |
| [`authz-401-storage-link`](https://www.w3.org/TR/lws10-core/#authorization-server-discovery) | MUST | INAPPLICABLE | 2 |
| [`authz-401-www-authenticate-challenge`](https://www.w3.org/TR/lws10-core/#authorization-server-discovery) | MUST | INAPPLICABLE | 5 |
| [`authz-access-token-aud-claim`](https://www.w3.org/TR/lws10-core/#authorization-token-exchange-response) | MUST | INAPPLICABLE | 2 |
| [`authz-access-token-client-id-claim`](https://www.w3.org/TR/lws10-core/#authorization-token-exchange-response) | MUST | INAPPLICABLE | 1 |
| [`authz-access-token-exp-short-lived`](https://www.w3.org/TR/lws10-core/#authorization-token-exchange-response) | MUST | INAPPLICABLE | 1 |
| [`authz-access-token-iat-claim`](https://www.w3.org/TR/lws10-core/#authorization-token-exchange-response) | MUST | INAPPLICABLE | 1 |
| [`authz-access-token-iss-claim`](https://www.w3.org/TR/lws10-core/#authorization-token-exchange-response) | MUST | INAPPLICABLE | 2 |
| [`authz-access-token-jti-claim`](https://www.w3.org/TR/lws10-core/#authorization-token-exchange-response) | MUST | INAPPLICABLE | 1 |
| [`authz-access-token-sub-claim`](https://www.w3.org/TR/lws10-core/#authorization-token-exchange-response) | MUST | INAPPLICABLE | 1 |
| [`authz-bearer-presentation-rfc6750`](https://www.w3.org/TR/lws10-core/#authorization-token-validation-presentation) | MUST | INAPPLICABLE | 1 |
| [`authz-challenge-extra-params`](https://www.w3.org/TR/lws10-core/#authorization-server-discovery) | MAY | UNCOVERED | 0 |
| [`authz-client-prm-resource-matches`](https://www.w3.org/TR/lws10-core/#authorization-discovery-validation) | MUST | INAPPLICABLE | 2 |
| [`authz-client-resource-metadata-same-origin`](https://www.w3.org/TR/lws10-core/#authorization-discovery-validation) | MUST | INAPPLICABLE | 1 |
| [`authz-client-storage-root-same-origin`](https://www.w3.org/TR/lws10-core/#authorization-discovery-validation) | MUST | INAPPLICABLE | 1 |
| [`authz-invalid-token-401-error-param`](https://www.w3.org/TR/lws10-core/#authorization-token-validation-verification) | MUST | INAPPLICABLE | 2 |
| [`authz-jwt-signature-jwks-rotation`](https://www.w3.org/TR/lws10-core/#authorization-token-validation-verification) | MUST | INAPPLICABLE | 4 |
| [`authz-metadata-subject-identifier-types`](https://www.w3.org/TR/lws10-core/#authorization-server-metadata) | SHOULD | INAPPLICABLE | 1 |
| [`authz-metadata-subject-token-types`](https://www.w3.org/TR/lws10-core/#authorization-server-metadata) | SHOULD | INAPPLICABLE | 2 |
| [`authz-oauth2-baseline`](https://www.w3.org/TR/lws10-core/#authorization) | MAY | UNCOVERED | 0 |
| [`authz-policy-denial-rejected`](https://www.w3.org/TR/lws10-core/#authorization-token-validation-verification) | MUST | INAPPLICABLE | 4 |
| [`authz-prm-authorization-servers`](https://www.w3.org/TR/lws10-core/#protected-resource-metadata) | MUST | INAPPLICABLE | 1 |
| [`authz-prm-conforms-rfc9728`](https://www.w3.org/TR/lws10-core/#protected-resource-metadata) | MUST | INAPPLICABLE | 1 |
| [`authz-server-metadata-well-known`](https://www.w3.org/TR/lws10-core/#authorization-server-metadata) | MUST | INAPPLICABLE | 1 |
| [`authz-token-error-rfc6749`](https://www.w3.org/TR/lws10-core/#authorization-token-exchange-response) | MUST | INAPPLICABLE | 3 |
| [`authz-token-exchange-grant`](https://www.w3.org/TR/lws10-core/#authorization-token-exchange-request) | MUST | INAPPLICABLE | 2 |
| [`authz-token-exchange-resource-param`](https://www.w3.org/TR/lws10-core/#authorization-token-exchange-request) | MUST | INAPPLICABLE | 3 |
| [`authz-token-exchange-subject-token-param`](https://www.w3.org/TR/lws10-core/#authorization-token-exchange-request) | MUST | INAPPLICABLE | 2 |
| [`authz-token-response-rfc6749-rfc9068`](https://www.w3.org/TR/lws10-core/#authorization-token-exchange-response) | MUST | INAPPLICABLE | 1 |
| [`authz-token-validation-checklist`](https://www.w3.org/TR/lws10-core/#authorization-token-validation-verification) | MUST | INAPPLICABLE | 9 |
| [`authz-validate-before-issuing`](https://www.w3.org/TR/lws10-core/#authorization-token-exchange-request) | MUST | INAPPLICABLE | 1 |
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
| [`create-401-storage-link`](https://www.w3.org/TR/lws10-core/#create-resource) | SHOULD | INAPPLICABLE | 1 |
| [`create-container-type-link`](https://www.w3.org/TR/lws10-core/#create-resource) | MUST | PASS | 1 |
| [`create-linkset-before-success`](https://www.w3.org/TR/lws10-core/#create-resource) | MUST | PASS | 1 |
| [`create-post-201-location-links`](https://www.w3.org/TR/lws10-core/#create-resource) | MUST | PASS | 5 |
| [`create-post-missing-container-404`](https://www.w3.org/TR/lws10-core/#create-resource) | MUST | PASS | 2 |
| [`create-post-not-idempotent`](https://www.w3.org/TR/lws10-core/#create-resource) | SHOULD | PASS | 1 |
| [`create-server-managed-metadata-protected`](https://www.w3.org/TR/lws10-core/#create-resource) | MUST | PASS | 1 |
| [`delete-401-403-404-semantics`](https://www.w3.org/TR/lws10-core/#delete-resource) | MUST | INAPPLICABLE | 2 |
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
| [`move-authorization-delete-and-create`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | INAPPLICABLE | 2 |
| [`move-container-subtree-authorization`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | UNCOVERED | 0 |
| [`move-containers-applies-to`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | PASS | 2 |
| [`move-containment-atomic`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | PASS | 3 |
| [`move-containment-integrity-cycles`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | PASS | 1 |
| [`move-cross-storage-may-reject`](https://www.w3.org/TR/lws10-core/#moving-resources) | MAY | UNCOVERED | 0 |
| [`move-destination-existing-container`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | PASS | 2 |
| [`move-identifier-preserved`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | INAPPLICABLE | 1 |
| [`move-new-identifier-response`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | UNCOVERED | 0 |
| [`move-notification-single-activity`](https://www.w3.org/TR/lws10-core/#moving-resources) | SHOULD | INAPPLICABLE | 1 |
| [`move-preserves-content-and-links`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | INAPPLICABLE | 1 |
| [`move-request-json-patch`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | PASS | 1 |
| [`move-server-support`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | PASS | 3 |
| [`notification-activity-as2-conformance`](https://www.w3.org/TR/lws10-core/#activity-properties) | MUST | INAPPLICABLE | 1 |
| [`notification-activity-id`](https://www.w3.org/TR/lws10-core/#activity-properties) | MUST | INAPPLICABLE | 1 |
| [`notification-activity-move`](https://www.w3.org/TR/lws10-core/#activity-types) | MUST | INAPPLICABLE | 1 |
| [`notification-activity-object`](https://www.w3.org/TR/lws10-core/#activity-properties) | MUST | INAPPLICABLE | 1 |
| [`notification-activity-object-id`](https://www.w3.org/TR/lws10-core/#activity-properties) | MUST | INAPPLICABLE | 5 |
| [`notification-activity-object-type`](https://www.w3.org/TR/lws10-core/#activity-properties) | MUST | INAPPLICABLE | 1 |
| [`notification-activity-optional-properties`](https://www.w3.org/TR/lws10-core/#activity-properties) | MAY | INAPPLICABLE | 1 |
| [`notification-activity-published`](https://www.w3.org/TR/lws10-core/#activity-properties) | MUST | INAPPLICABLE | 1 |
| [`notification-activity-type`](https://www.w3.org/TR/lws10-core/#activity-properties) | MUST | INAPPLICABLE | 3 |
| [`notification-activity-types-additional`](https://www.w3.org/TR/lws10-core/#activity-types) | MAY | UNCOVERED | 0 |
| [`notification-activity-types-supported`](https://www.w3.org/TR/lws10-core/#activity-types) | MUST | INAPPLICABLE | 5 |
| [`notification-batching`](https://www.w3.org/TR/lws10-core/#batching) | MAY | UNCOVERED | 0 |
| [`notification-envelope-activity`](https://www.w3.org/TR/lws10-core/#envelope-properties) | MUST | INAPPLICABLE | 1 |
| [`notification-envelope-storage`](https://www.w3.org/TR/lws10-core/#envelope-properties) | MUST | INAPPLICABLE | 1 |
| [`notification-envelope-type`](https://www.w3.org/TR/lws10-core/#envelope-properties) | MUST | INAPPLICABLE | 1 |
| [`notification-suite-subscription-type-identifier`](https://www.w3.org/TR/lws10-core/#notification-subscription-type-identifier) | MUST | PASS | 1 |
| [`notifications-advertise-notificationservice`](https://www.w3.org/TR/lws10-core/#notification-discovery) | MUST | PASS | 1 |
| [`notificationservice-additional-properties`](https://www.w3.org/TR/lws10-core/#notification-discovery) | MAY | UNCOVERED | 0 |
| [`notificationservice-endpoint-and-subscription-types`](https://www.w3.org/TR/lws10-core/#notification-discovery) | MUST | PASS | 1 |
| [`operations-core-four-atomic`](https://www.w3.org/TR/lws10-core/#operations) | MUST | UNCOVERED | 0 |
| [`pagination-200-totalitems-all-pages`](https://www.w3.org/TR/lws10-core/#requesting-pages) | MUST | PASS | 3 |
| [`pagination-first-page-flow`](https://www.w3.org/TR/lws10-core/#requesting-pages) | MAY | PASS | 1 |
| [`pagination-link-first`](https://www.w3.org/TR/lws10-core/#pagination-link-relations) | MUST | PASS | 5 |
| [`pagination-link-last`](https://www.w3.org/TR/lws10-core/#pagination-link-relations) | MAY | PASS | 1 |
| [`pagination-link-next`](https://www.w3.org/TR/lws10-core/#pagination-link-relations) | MUST | PASS | 2 |
| [`pagination-link-prev`](https://www.w3.org/TR/lws10-core/#pagination-link-relations) | MUST | PASS | 2 |
| [`pagination-over-threshold`](https://www.w3.org/TR/lws10-core/#pagination) | SHOULD | UNCOVERED | 0 |
| [`patch-json-patch-baseline`](https://www.w3.org/TR/lws10-core/#update-resource) | MUST | PASS | 2 |
| [`policy-action-required`](https://www.w3.org/TR/lws10-core/#odrl-action) | MUST | INAPPLICABLE | 2 |
| [`policy-action-values`](https://www.w3.org/TR/lws10-core/#odrl-action) | MUST | INAPPLICABLE | 1 |
| [`policy-assignee-required`](https://www.w3.org/TR/lws10-core/#odrl-assignee) | MUST | INAPPLICABLE | 2 |
| [`policy-assignee-uri-foaf-agent`](https://www.w3.org/TR/lws10-core/#odrl-assignee) | MUST | INAPPLICABLE | 2 |
| [`policy-constraint-left-operands`](https://www.w3.org/TR/lws10-core/#odrl-constraint) | MUST | INAPPLICABLE | 5 |
| [`policy-constraint-objects`](https://www.w3.org/TR/lws10-core/#odrl-constraint) | MUST | INAPPLICABLE | 2 |
| [`policy-constraint-optional`](https://www.w3.org/TR/lws10-core/#odrl-constraint) | MAY | INAPPLICABLE | 1 |
| [`policy-constraints-all-satisfied`](https://www.w3.org/TR/lws10-core/#odrl-constraint) | MUST | INAPPLICABLE | 1 |
| [`policy-constraints-conjunction-semantics`](https://www.w3.org/TR/lws10-core/#constraint-combining) | MUST | INAPPLICABLE | 1 |
| [`policy-target-extra-types`](https://www.w3.org/TR/lws10-core/#odrl-target) | MAY | UNCOVERED | 0 |
| [`policy-target-object`](https://www.w3.org/TR/lws10-core/#odrl-target) | MUST | INAPPLICABLE | 2 |
| [`policy-target-optional`](https://www.w3.org/TR/lws10-core/#odrl-target) | MAY | UNCOVERED | 0 |
| [`policy-type-access-policy`](https://www.w3.org/TR/lws10-core/#odrl-type) | MUST | INAPPLICABLE | 2 |
| [`policy-type-required`](https://www.w3.org/TR/lws10-core/#odrl-type) | MUST | INAPPLICABLE | 2 |
| [`privacy-move-redirect-access-control`](https://www.w3.org/TR/lws10-core/#privacy-moving-resources) | SHOULD | UNCOVERED | 0 |
| [`privacy-notification-actor-omitted`](https://www.w3.org/TR/lws10-core/#privacy-notifications) | SHOULD | INAPPLICABLE | 1 |
| [`privacy-notification-authorized-resources-only`](https://www.w3.org/TR/lws10-core/#privacy-notifications) | SHOULD | INAPPLICABLE | 1 |
| [`put-clients-use-conditional-requests`](https://www.w3.org/TR/lws10-core/#update-resource) | SHOULD | UNCOVERED | 0 |
| [`read-container-etag-type-links`](https://www.w3.org/TR/lws10-core/#read-resource) | MUST | PASS | 1 |
| [`read-container-listing-authz-filtered`](https://www.w3.org/TR/lws10-core/#read-resource) | MAY | INAPPLICABLE | 1 |
| [`read-container-listing-member-metadata`](https://www.w3.org/TR/lws10-core/#read-resource) | MUST | PASS | 1 |
| [`read-type-distinction-metadata-links`](https://www.w3.org/TR/lws10-core/#read-resource) | MUST | PASS | 2 |
| [`security-move-capability-restraint`](https://www.w3.org/TR/lws10-core/#security-moving-resources) | MUST | UNCOVERED | 0 |
| [`security-move-container-subtree`](https://www.w3.org/TR/lws10-core/#security-moving-resources) | MUST | UNCOVERED | 0 |
| [`security-move-privilege-combination`](https://www.w3.org/TR/lws10-core/#security-moving-resources) | MUST | INAPPLICABLE | 2 |
| [`security-notification-access-control`](https://www.w3.org/TR/lws10-core/#security-notifications) | MUST | INAPPLICABLE | 4 |
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
| [`subscription-authorization-on-create`](https://www.w3.org/TR/lws10-core/#subscription-authorization) | MUST | INAPPLICABLE | 2 |
| [`subscription-authorization-on-delivery`](https://www.w3.org/TR/lws10-core/#subscription-authorization) | MUST | INAPPLICABLE | 2 |
| [`subscription-authorization-revoked`](https://www.w3.org/TR/lws10-core/#subscription-authorization) | MUST | INAPPLICABLE | 1 |
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
| [`accept-query-advertised`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | SHOULD | INAPPLICABLE | 1 |
| [`accept-query-no-disclosure`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | INAPPLICABLE | 1 |
| [`at-members-ignored`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | INAPPLICABLE | 1 |
| [`authorization-enforced`](https://w3c.github.io/lws-protocol/lws10-index/#security-authorization) | MUST | INAPPLICABLE | 3 |
| [`baseline-format-supported`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | INAPPLICABLE | 1 |
| [`consistency-not-for-authorization`](https://w3c.github.io/lws-protocol/lws10-index/#type-derivation) | MUST | INAPPLICABLE | 1 |
| [`content-location-protected`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | INAPPLICABLE | 1 |
| [`content-types-identical`](https://w3c.github.io/lws-protocol/lws10-index/#type-derivation) | MUST | INAPPLICABLE | 1 |
| [`counts-filtered`](https://w3c.github.io/lws-protocol/lws10-index/#security-authorization) | MUST | INAPPLICABLE | 1 |
| [`current-authorization`](https://w3c.github.io/lws-protocol/lws10-index/#security-authorization) | MUST | INAPPLICABLE | 1 |
| [`derived-index-filtered`](https://w3c.github.io/lws-protocol/lws10-index/#security-authorization) | MUST | INAPPLICABLE | 2 |
| [`duplicate-groups-ignored`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | INAPPLICABLE | 1 |
| [`empty-group-rejected`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | INAPPLICABLE | 1 |
| [`eventually-consistent`](https://w3c.github.io/lws-protocol/lws10-index/#type-derivation) | MAY | UNCOVERED | 0 |
| [`expired-page-404-410`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-errors) | MUST | INAPPLICABLE | 1 |
| [`extensions-uphold-authorization`](https://w3c.github.io/lws-protocol/lws10-index/#security-authorization) | MUST | UNCOVERED | 0 |
| [`grammar-not-extended`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | INAPPLICABLE | 1 |
| [`invalid-iri-400`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-errors) | MUST | INAPPLICABLE | 1 |
| [`malformed-filter-400`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-errors) | MUST | INAPPLICABLE | 4 |
| [`missing-content-type-400`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-errors) | MUST | INAPPLICABLE | 1 |
| [`no-existence-disclosure`](https://w3c.github.io/lws-protocol/lws10-index/#security-authorization) | MUST | INAPPLICABLE | 2 |
| [`no-match-not-error`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | INAPPLICABLE | 2 |
| [`no-shared-cache`](https://w3c.github.io/lws-protocol/lws10-index/#security-authorization) | MUST | INAPPLICABLE | 2 |
| [`no-silent-narrowing`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-errors) | MUST | INAPPLICABLE | 1 |
| [`not-acceptable-406`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-errors) | MUST | INAPPLICABLE | 1 |
| [`other-formats`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MAY | UNCOVERED | 0 |
| [`other-response-formats`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MAY | INAPPLICABLE | 1 |
| [`query-content-type-required`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | INAPPLICABLE | 1 |
| [`query-safe-idempotent`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MAY | INAPPLICABLE | 1 |
| [`reflect-change-bounded`](https://w3c.github.io/lws-protocol/lws10-index/#type-derivation) | SHOULD | INAPPLICABLE | 4 |
| [`relation-sources-identical`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | INAPPLICABLE | 1 |
| [`relations-may-be-indexed`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MAY | INAPPLICABLE | 4 |
| [`relations-not-enumerated`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | UNCOVERED | 0 |
| [`responses-private`](https://w3c.github.io/lws-protocol/lws10-index/#security-authorization) | MUST | INAPPLICABLE | 2 |
| [`result-item-id-type`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | INAPPLICABLE | 2 |
| [`result-item-metadata`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MAY | UNCOVERED | 0 |
| [`revoked-not-shown`](https://w3c.github.io/lws-protocol/lws10-index/#security-authorization) | MUST | INAPPLICABLE | 1 |
| [`search-default-containerpage`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | INAPPLICABLE | 4 |
| [`service-advertised`](https://w3c.github.io/lws-protocol/lws10-index/#discovery) | MUST | INAPPLICABLE | 1 |
| [`service-endpoint`](https://w3c.github.io/lws-protocol/lws10-index/#discovery) | MUST | INAPPLICABLE | 1 |
| [`service-extra-properties`](https://w3c.github.io/lws-protocol/lws10-index/#discovery) | MAY | UNCOVERED | 0 |
| [`services-optional`](https://w3c.github.io/lws-protocol/lws10-index/#discovery) | MAY | INAPPLICABLE | 1 |
| [`structural-relations-not-indexed`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | INAPPLICABLE | 1 |
| [`too-complex-422`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-errors) | MUST | INAPPLICABLE | 1 |
| [`type-filter`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MAY | INAPPLICABLE | 5 |
| [`type-key-supported`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | INAPPLICABLE | 3 |
| [`types-from-content`](https://w3c.github.io/lws-protocol/lws10-index/#type-derivation) | MAY | INAPPLICABLE | 1 |
| [`types-from-link-headers`](https://w3c.github.io/lws-protocol/lws10-index/#type-derivation) | SHOULD | INAPPLICABLE | 4 |
| [`unauthorized-omitted`](https://w3c.github.io/lws-protocol/lws10-index/#security-authorization) | MUST | INAPPLICABLE | 2 |
| [`unindexed-relation-indistinguishable`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-query) | MUST | INAPPLICABLE | 2 |
| [`unsupported-format-415`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-errors) | MUST | INAPPLICABLE | 1 |
| [`unsupported-format-accept-query`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-errors) | SHOULD | INAPPLICABLE | 1 |
| [`vary-accept`](https://w3c.github.io/lws-protocol/lws10-index/#type-search-errors) | MUST | INAPPLICABLE | 1 |
| [`delivery-deactivation-optional`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#webhook-delivery) | MAY | INAPPLICABLE | 1 |
| [`delivery-lws-json`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#webhook-delivery) | MUST | INAPPLICABLE | 1 |
| [`delivery-retry-optional`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#webhook-delivery) | MAY | INAPPLICABLE | 1 |
| [`delivery-signed`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#webhook-authentication) | SHOULD | INAPPLICABLE | 1 |
| [`inbox-verifies-signature`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#webhook-authentication) | MUST | INAPPLICABLE | 1 |
| [`keyid-url-with-fragment`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#signature-verification) | MUST | INAPPLICABLE | 1 |
| [`receiver-verification-steps`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#signature-verification) | MUST | INAPPLICABLE | 1 |
| [`response-expires-optional`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#webhook-subscription) | MAY | INAPPLICABLE | 1 |
| [`response-type-webhook`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#webhook-subscription) | MUST | INAPPLICABLE | 1 |
| [`signature-covered-components`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#signature-requirements) | MUST | INAPPLICABLE | 2 |
| [`signature-input-created-keyid`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#signature-requirements) | MUST | INAPPLICABLE | 2 |
| [`signing-key-published`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#webhook-authentication) | MUST | INAPPLICABLE | 2 |
| [`storage-description-id-matches`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#signature-verification) | MUST | INAPPLICABLE | 1 |
| [`subscription-expires-optional`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#webhook-subscription) | MAY | INAPPLICABLE | 1 |
| [`subscription-get-delete`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#webhook-subscription-management) | MUST | INAPPLICABLE | 1 |
| [`subscription-inbox-required`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#webhook-subscription) | MUST | INAPPLICABLE | 1 |
| [`subscription-listing-container`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#webhook-subscription-management) | MUST | INAPPLICABLE | 2 |
| [`subscription-type-and-fields`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#webhook-subscription) | MUST | INAPPLICABLE | 2 |
| [`subscription-type-identifier`](https://w3c.github.io/lws-protocol/lws10-notifications-webhook/#subscription-type) | MUST | INAPPLICABLE | 1 |

