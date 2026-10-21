# Touchstone conformance report

**NOT CONFORMANT**: only MUST tests decide conformance (definitions/EXECUTION.md section 9), and 2 failed or ended cantTell. SHOULD and MAY failures are advisory: 1. Inapplicable MUST tests are coverage this run did not have: 82.

| | |
|---|---|
| target | factoidal-auth-shim |
| base URL | `http://127.0.0.1:4723/` |
| run | `5d0229bf` |
| started | 2026-10-21T15:14:53.458533076Z |

## Results

| passed | failed | cantTell | inapplicable |
|---:|---:|---:|---:|
| 117 | 3 | 0 | 101 |

## Requirement coverage by level

| level | in catalog | covered | failing |
|---|---:|---:|---:|
| MUST | 214 | 205 | 2 |
| SHOULD | 25 | 20 | 2 |
| MAY | 33 | 18 | 0 |

49 catalog requirements bind only clients, receivers, identity providers or other specifications, which a server run cannot break, so coverage leaves them out.

## Tests

| test | level | outcome | duration |
|---|---|---|---:|
| `core/discovery#discovery-get-links-storageDescription` | MUST | passed | 5977 ms |
| `core/discovery#discovery-link-storage-on-data-resource` | MUST | passed | 7496 ms |
| `core/discovery#discovery-storage-description` | MUST | passed | 4343 ms |
| `core/discovery#discovery-storage-description-default-media-type` | MUST | passed | 4608 ms |
| `core/discovery#discovery-unauthorized-response-headers` | MUST | failed | 4457 ms |
| `core/discovery#discovery-storage-root-is-container` | MUST | passed | 4755 ms |
| `core/discovery#discovery-storage-description-ids-are-uris` | MUST | passed | 7721 ms |
| `core/containers#getContainer` | MUST | passed | 5143 ms |
| `core/containers#createContainer` | MUST | passed | 6170 ms |
| `core/containers#createContainer-type-link` | SHOULD | passed | 6147 ms |
| `core/containers#getContainer-containmentIntegrity` | MUST | passed | 6164 ms |
| `core/containers#container-total-items-accurate` | SHOULD | passed | 8166 ms |
| `core/containers#contained-resource-type-values` | MUST | passed | 6456 ms |
| `core/containers#contained-resource-format` | MUST | passed | 6714 ms |
| `core/containers#contained-resource-size-modified` | SHOULD | passed | 4520 ms |
| `core/containers#container-conneg` | MUST | passed | 4204 ms |
| `core/containers#container-conneg-vary` | SHOULD | passed | 3146 ms |
| `core/containers#container-conneg-weighted` | MUST | passed | 2428 ms |
| `core/containers#container-head-parity` | MUST | passed | 3265 ms |
| `core/containers#delete-empty-container` | MUST | passed | 4634 ms |
| `core/containers#delete-non-empty-container-409` | MUST | passed | 6217 ms |
| `core/containers#delete-container-recursive` | MAY | passed | 5961 ms |
| `core/containers#delete-container-recursive-deep` | MAY | passed | 5856 ms |
| `core/containers#containment-hierarchy-consistent` | MUST | passed | 2863 ms |
| `core/containers#container-lws-profile-ld-json` | MUST | passed | 2547 ms |
| `core/containers#container-lws-profile-turtle` | MUST | failed | 2676 ms |
| `core/data_resources#createDataResource` | MUST | passed | 4740 ms |
| `core/data_resources#createDataResource-type-link` | SHOULD | passed | 1966 ms |
| `core/data_resources#create-post-twice-distinct` | SHOULD | passed | 2541 ms |
| `core/data_resources#create-in-missing-container-rejected` | MUST | passed | 7811 ms |
| `core/data_resources#create-in-missing-container-404` | SHOULD | passed | 1593 ms |
| `core/data_resources#create-server-managed-links-protected` | MUST | passed | 778 ms |
| `core/data_resources#readDataResource` | MUST | passed | 4871 ms |
| `core/data_resources#data-resource-head-parity` | MUST | passed | 3227 ms |
| `core/data_resources#data-resource-range-request` | MUST | passed | 2847 ms |
| `core/data_resources#data-resource-range-unsatisfiable` | SHOULD | passed | 921 ms |
| `core/data_resources#data-resource-accept-ranges` | MAY | passed | 6279 ms |
| `core/data_resources#updateDataResource` | MUST | passed | 4570 ms |
| `core/data_resources#patch-json-patch-baseline` | MUST | passed | 4187 ms |
| `core/data_resources#patch-json-patch-atomic` | MUST | passed | 4152 ms |
| `core/data_resources#deleteDataResource` | MUST | passed | 4797 ms |
| `core/data_resources#post-to-non-container-405` | SHOULD | passed | 4189 ms |
| `core/data_resources#error-problem-details` | SHOULD | passed | 1633 ms |
| `core/conditional_requests#conditional-get-304` | SHOULD | passed | 6610 ms |
| `core/conditional_requests#conditional-get-container-304` | SHOULD | passed | 5697 ms |
| `core/conditional_requests#conditional-get-stale-validator-200` | MUST | passed | 4331 ms |
| `core/conditional_requests#conditional-put-stale-if-match-412` | MUST | passed | 1750 ms |
| `core/conditional_requests#conditional-delete-stale-if-match-412` | SHOULD | passed | 7667 ms |
| `core/conditional_requests#update-changes-strong-etag` | MUST | passed | 6037 ms |
| `core/conditional_requests#delete-updates-parent-strong-etag` | MUST | passed | 6209 ms |
| `core/conditional_requests#conditional-get-if-modified-since-304` | SHOULD | passed | 4428 ms |
| `core/conditional_requests#conditional-get-if-unmodified-since-412` | SHOULD | failed | 2564 ms |
| `core/linksets#getLinkset` | MUST | passed | 5439 ms |
| `core/linksets#linkset-advertises-patch` | MUST | passed | 5131 ms |
| `core/linksets#linkset-conditional-412` | MUST | passed | 2086 ms |
| `core/linksets#linkset-put-405-when-unsupported` | MUST | inapplicable | 3429 ms |
| `core/linksets#linkset-removed-with-resource` | MUST | passed | 4553 ms |
| `core/linksets#linkset-ready-at-create` | MUST | passed | 1465 ms |
| `core/linksets#linkset-up-not-redirected` | MUST | passed | 4386 ms |
| `core/linksets#linkset-patch-stays-linkset` | MUST | passed | 6286 ms |
| `core/linksets#linkset-patch-json-patch` | SHOULD | passed | 3048 ms |
| `core/linksets#linkset-patch-preserves-server-links` | MUST | passed | 4500 ms |
| `core/moving#discovery-move-capability` | MUST | inapplicable | 2766 ms |
| `core/moving#move-data-resource` | MUST | inapplicable | 3089 ms |
| `core/moving#move-updates-container-etags` | MUST | inapplicable | 3261 ms |
| `core/moving#move-keeps-identifier-content-and-links` | MUST | inapplicable | 4436 ms |
| `core/moving#move-invalid-destination-refused` | MUST | inapplicable | 684 ms |
| `core/moving#move-container` | MUST | inapplicable | 5102 ms |
| `core/moving#move-container-into-itself-refused` | MUST | inapplicable | 2008 ms |
| `core/moving#move-container-refused-without-container-support` | MUST | inapplicable | 1918 ms |
| `core/moving#move-refused-without-capability` | MUST | passed | 5146 ms |
| `core/moving#move-needs-create-in-destination` | MUST | inapplicable | 103 ms |
| `core/moving#move-needs-delete-of-resource` | MUST | inapplicable | 165 ms |
| `core/moving#move-notification` | MUST | inapplicable | 2418 ms |
| `core/storage_authorization#getContainer-private-unauthorized` | MUST | passed | 2319 ms |
| `core/storage_authorization#protected-resource-metadata` | MUST | passed | 2280 ms |
| `core/storage_authorization#protected-resource-metadata-data-resource` | MUST | passed | 4487 ms |
| `core/storage_authorization#storage-root-same-origin` | MUST | inapplicable | 716 ms |
| `core/storage_authorization#getContainer-authenticated-owner` | MUST | passed | 783 ms |
| `core/storage_authorization#createDataResource-unauthorized` | MUST | passed | 2893 ms |
| `core/storage_authorization#updateDataResource-unauthorized` | MUST | passed | 3182 ms |
| `core/storage_authorization#deleteDataResource-unauthorized` | MUST | passed | 4742 ms |
| `core/storage_authorization#authz-non-owner-read-rejected` | MUST | passed | 3080 ms |
| `core/storage_authorization#authz-non-owner-write-rejected` | MUST | passed | 1622 ms |
| `core/storage_authorization#authz-non-owner-delete-rejected` | MUST | passed | 2872 ms |
| `core/storage_authorization#authz-expired-token-rejected` | MUST | passed | 892 ms |
| `core/storage_authorization#authz-token-bad-signature-rejected` | MUST | passed | 803 ms |
| `core/storage_authorization#authz-token-alg-none-rejected` | MUST | passed | 2532 ms |
| `core/storage_authorization#authz-token-unknown-key-rejected` | MUST | passed | 2545 ms |
| `core/storage_authorization#authz-token-wrong-audience-rejected` | MUST | passed | 2567 ms |
| `core/storage_authorization#authz-token-wrong-issuer-rejected` | MUST | passed | 805 ms |
| `core/storage_authorization#authz-token-not-yet-valid-rejected` | MUST | passed | 2512 ms |
| `core/storage_authorization#authz-token-issued-in-future-rejected` | MUST | passed | 2668 ms |
| `core/authorization_server#authz-server-metadata-well-known` | MUST | passed | 3685 ms |
| `core/authorization_server#authz-metadata-subject-token-types` | SHOULD | passed | 840 ms |
| `core/authorization_server#authz-metadata-subject-token-types-are-uris` | MUST | passed | 2176 ms |
| `core/authorization_server#authz-metadata-subject-identifier-types` | SHOULD | passed | 2203 ms |
| `core/authorization_server#authz-token-exchange-valid` | MUST | passed | 4906 ms |
| `core/authorization_server#authz-token-exchange-invalid-resource` | MUST | passed | 4617 ms |
| `core/authorization_server#authz-token-exchange-missing-resource` | MUST | passed | 763 ms |
| `core/authorization_server#authz-token-exchange-missing-subject-token` | MUST | passed | 2315 ms |
| `core/authorization_server#authz-issued-token-accepted-by-storage` | MUST | passed | 4362 ms |
| `core/access_grants#access-grant-endpoint-is-container` | MUST | inapplicable | 2086 ms |
| `core/access_grants#access-grant-create` | MUST | inapplicable | 3925 ms |
| `core/access_grants#access-grant-revoke` | SHOULD | inapplicable | 2082 ms |
| `core/access_grants#getContainer-public-read` | MUST | inapplicable | 111 ms |
| `core/access_grants#readDataResource-public-read` | MUST | inapplicable | 42 ms |
| `core/access_grants#access-grant-authenticated-agent` | MUST | inapplicable | 49 ms |
| `core/access_grants#access-grant-extra-properties-accepted` | MAY | inapplicable | 2325 ms |
| `core/access_grants#access-grant-inbox-notified` | SHOULD | inapplicable | 806 ms |
| `core/access_grants#access-request-create` | MUST | inapplicable | 2705 ms |
| `core/access_grants#access-grant-document-shape` | MUST | inapplicable | 2724 ms |
| `core/access_grants#access-grant-incomplete-refused` | MUST | inapplicable | 3109 ms |
| `core/access_grants#access-grant-constraints-all-satisfied` | MUST | inapplicable | 4770 ms |
| `core/access_grants#access-grant-left-operands-accepted` | MUST | inapplicable | 3199 ms |
| `core/access_grants#access-grant-constraint-format` | MUST | inapplicable | 2722 ms |
| `core/access_grants#access-grant-constraint-type` | MUST | inapplicable | 6212 ms |
| `core/access_grants#access-grant-constraint-client` | MUST | inapplicable | 2635 ms |
| `core/access_grants#container-listing-filtered-metadata` | MAY | inapplicable | 555 ms |
| `core/notifications#notification-service-advertised` | MUST | inapplicable | 2764 ms |
| `core/notifications#subscription-create` | MUST | inapplicable | 2920 ms |
| `core/notifications#subscription-missing-type-refused` | MUST | inapplicable | 3140 ms |
| `core/notifications#subscription-unadvertised-type-refused` | MUST | inapplicable | 5387 ms |
| `core/notifications#subscription-missing-topic-refused` | MUST | inapplicable | 3148 ms |
| `core/notifications#subscription-unreadable-topic-refused` | MUST | inapplicable | 209 ms |
| `core/notifications#subscription-after-revocation-refused` | MUST | inapplicable | 2771 ms |
| `core/notifications#notification-delivered-create` | MUST | inapplicable | 385 ms |
| `core/notifications#notification-delivered-update` | MUST | inapplicable | 4023 ms |
| `core/notifications#notification-delivered-delete` | MUST | inapplicable | 4126 ms |
| `core/notifications#notification-not-delivered-for-unreadable-resource` | MUST | inapplicable | 2609 ms |
| `core/notifications#notification-stops-after-revocation` | MUST | inapplicable | 898 ms |
| `core/notifications#notification-actor-omitted` | SHOULD | inapplicable | 4083 ms |
| `core/notifications#notification-delivered-in-subcontainer` | MUST | inapplicable | 4056 ms |
| `core/notifications#notification-scope-data-resource-only` | MUST | inapplicable | 4113 ms |
| `core/pagination#pagination-first-page` | MUST | inapplicable | 3565 ms |
| `core/pagination#pagination-next-page` | MUST | inapplicable | 2754 ms |
| `core/pagination#pagination-single-page` | MUST | inapplicable | 2754 ms |
| `core/pagination#pagination-last-page` | MUST | inapplicable | 2775 ms |
| `core/pagination#pagination-totalitems-all-pages` | SHOULD | inapplicable | 4338 ms |
| `auth/oidc/manifest#authn-oidc-valid-id-token` | MUST | passed | 2750 ms |
| `auth/oidc/manifest#authn-oidc-expired-id-token` | MUST | passed | 1487 ms |
| `auth/oidc/manifest#authn-oidc-alg-none` | MUST | passed | 2503 ms |
| `auth/oidc/manifest#authn-oidc-bad-signature` | MUST | passed | 4661 ms |
| `auth/oidc/manifest#authn-oidc-untrusted-issuer` | MUST | passed | 1757 ms |
| `auth/oidc/manifest#authn-oidc-missing-azp` | MUST | passed | 2454 ms |
| `auth/cid/manifest#authn-cid-valid-credential` | MUST | passed | 1910 ms |
| `auth/cid/manifest#authn-cid-unknown-kid` | MUST | passed | 4266 ms |
| `auth/cid/manifest#authn-cid-bad-signature` | MUST | passed | 533 ms |
| `auth/cid/manifest#authn-cid-expired` | MUST | passed | 4163 ms |
| `auth/cid/manifest#authn-cid-alg-none` | MUST | passed | 1195 ms |
| `auth/cid/manifest#authn-cid-claims-mismatch` | MUST | passed | 2569 ms |
| `auth/cid/manifest#authn-cid-document-id-mismatch` | MUST | passed | 2564 ms |
| `auth/cid/manifest#authn-cid-key-not-for-authentication` | MUST | passed | 2849 ms |
| `auth/cid/manifest#authn-cid-key-revoked` | MUST | passed | 3569 ms |
| `auth/cid/manifest#authn-cid-foreign-controller` | MUST | passed | 3362 ms |
| `auth/cid/manifest#authn-cid-referenced-method` | MUST | passed | 4246 ms |
| `auth/cid/manifest#authn-cid-didkey-valid-credential` | MUST | passed | 3362 ms |
| `auth/cid/manifest#authn-cid-didkey-invalid-signature` | MUST | passed | 3771 ms |
| `auth/cid/manifest#authn-cid-didkey-alg-none` | MUST | passed | 4167 ms |
| `auth/cid/manifest#authn-cid-didkey-expired` | MUST | passed | 4075 ms |
| `auth/cid/manifest#authn-cid-didkey-claims-mismatch` | MUST | passed | 3208 ms |
| `auth/cid/manifest#authn-cid-didkey-audience-excludes-as` | MUST | passed | 3271 ms |
| `auth/cid/manifest#authn-cid-didkey-missing-exp` | MUST | passed | 7429 ms |
| `auth/cid/manifest#authn-cid-didkey-missing-iat` | MUST | passed | 4396 ms |
| `auth/cid/manifest#authn-cid-didkey-missing-subject` | MUST | passed | 5735 ms |
| `auth/cid/manifest#authn-cid-didkey-missing-issuer` | MUST | passed | 647 ms |
| `auth/cid/manifest#authn-cid-didkey-missing-client-id` | MUST | passed | 2083 ms |
| `auth/saml/manifest#authn-saml-valid-assertion` | MUST | passed | 5452 ms |
| `auth/saml/manifest#authn-saml-invalid-signature` | MUST | passed | 5085 ms |
| `auth/saml/manifest#authn-saml-unsigned` | MUST | passed | 1154 ms |
| `notifications/webhook/manifest#webhook-subscription-response` | MUST | inapplicable | 616 ms |
| `notifications/webhook/manifest#webhook-subscription-expires-supported` | MUST | inapplicable | 1132 ms |
| `notifications/webhook/manifest#webhook-subscription-listed` | MUST | inapplicable | 564 ms |
| `notifications/webhook/manifest#webhook-subscription-get-delete` | MUST | inapplicable | 314 ms |
| `notifications/webhook/manifest#webhook-delivery-lws-json` | MUST | inapplicable | 4510 ms |
| `notifications/webhook/manifest#webhook-delivery-signed` | SHOULD | inapplicable | 4958 ms |
| `notifications/webhook/manifest#webhook-signature-components` | MUST | inapplicable | 263 ms |
| `notifications/webhook/manifest#webhook-signing-key-published` | MUST | inapplicable | 4276 ms |
| `notifications/webhook/manifest#webhook-signature-verifies` | MUST | inapplicable | 7661 ms |
| `notifications/webhook/manifest#webhook-delivery-retried` | MAY | inapplicable | 2772 ms |
| `notifications/webhook/manifest#webhook-subscription-deactivated` | MAY | inapplicable | 3990 ms |
| `index/manifest#index-services-advertised` | MUST | inapplicable | 1394 ms |
| `index/manifest#type-index-lists-readable-types` | MUST | inapplicable | 223 ms |
| `index/manifest#type-index-omits-unreadable-type` | MUST | inapplicable | 3914 ms |
| `index/manifest#type-index-not-shared` | MUST | inapplicable | 3778 ms |
| `index/manifest#type-search-by-type` | MUST | inapplicable | 4050 ms |
| `index/manifest#type-search-and-or` | MUST | inapplicable | 4124 ms |
| `index/manifest#type-search-native-classes` | MUST | inapplicable | 3512 ms |
| `index/manifest#type-search-no-match` | MUST | inapplicable | 1760 ms |
| `index/manifest#type-search-duplicate-groups` | MUST | inapplicable | 2252 ms |
| `index/manifest#type-search-at-members-ignored` | MUST | inapplicable | 5603 ms |
| `index/manifest#type-search-empty-key-absent` | MUST | inapplicable | 7180 ms |
| `index/manifest#type-search-empty-group-rejected` | MUST | inapplicable | 5758 ms |
| `index/manifest#type-search-type-not-array-rejected` | MUST | inapplicable | 558 ms |
| `index/manifest#type-search-bad-element-rejected` | MUST | inapplicable | 2600 ms |
| `index/manifest#type-search-malformed-json-rejected` | MUST | inapplicable | 3002 ms |
| `index/manifest#type-search-relative-iri-rejected` | MUST | inapplicable | 3297 ms |
| `index/manifest#type-search-missing-content-type-rejected` | MUST | inapplicable | 3072 ms |
| `index/manifest#type-search-unsupported-format-rejected` | MUST | inapplicable | 4181 ms |
| `index/manifest#type-search-unsupported-format-accept-query` | SHOULD | inapplicable | 4401 ms |
| `index/manifest#type-search-accept-query-advertised` | SHOULD | inapplicable | 3433 ms |
| `index/manifest#type-search-not-acceptable` | MUST | inapplicable | 7452 ms |
| `index/manifest#type-search-unindexed-relation` | MUST | inapplicable | 4614 ms |
| `index/manifest#type-search-structural-relation-not-indexed` | MUST | inapplicable | 6549 ms |
| `index/manifest#type-search-authorization-filtered` | MUST | inapplicable | 408 ms |
| `index/manifest#type-search-revoked-not-shown` | MUST | inapplicable | 5453 ms |
| `index/manifest#type-search-not-shared` | MUST | inapplicable | 4833 ms |
| `index/manifest#type-search-type-from-link-header` | SHOULD | inapplicable | 4809 ms |
| `index/manifest#type-search-type-from-content` | MAY | inapplicable | 4892 ms |
| `index/manifest#type-search-content-types-identical` | MUST | inapplicable | 1723 ms |
| `index/manifest#type-search-reflects-update` | SHOULD | inapplicable | 4801 ms |
| `index/manifest#type-search-reflects-delete` | SHOULD | inapplicable | 3467 ms |
| `index/manifest#type-search-vary-accept` | MUST | inapplicable | 4409 ms |
| `index/manifest#type-search-safe` | MAY | inapplicable | 3825 ms |
| `index/manifest#type-search-next-page` | MUST | inapplicable | 2676 ms |
| `index/manifest#type-search-relation-filter` | MAY | inapplicable | 2949 ms |
| `index/manifest#type-search-relation-cnf` | MAY | inapplicable | 2107 ms |
| `index/manifest#type-search-relation-from-link-header` | SHOULD | inapplicable | 2728 ms |
| `index/manifest#type-search-too-complex` | MUST | inapplicable | 2334 ms |
| `index/manifest#type-search-unrecognized-page-link` | MUST | inapplicable | 1051 ms |
| `index/manifest#type-search-content-location-protected` | MUST | inapplicable | 1230 ms |

### Detail

**`core/discovery#discovery-unauthorized-response-headers`** — failed

```
core/discovery#discovery-unauthorized-response-headers - failed [MUST] (4457 ms)
  step 'A 401 from a protected resource links to the storage':
    FAILED Link rel="https://www.w3.org/ns/lws#storage" to http://127.0.0.1:4723/.well-known/lws-storage
      expected: a matching link
      actual:   <http://127.0.0.1:4723/>; rel="https://www.w3.org/ns/lws#storage"
    exchange: GET http://127.0.0.1:4723/touchstone-run-5d0229bf/discovery-unauthorized-response-headers/ -> 401
    response body: {"type":"about:blank","title":"Unauthorized","status":401,"detail":"an access token is required","instance":"/touchstone-run-5d0229bf/discovery-unauthorized-response-headers/"}
```

**`core/containers#container-lws-profile-turtle`** — failed

```
core/containers#container-lws-profile-turtle - failed [MUST] (2676 ms)
  step 'its Content-Type names the profile, and its RDF is that of application/lws+json':
    FAILED RDF isomorphism with application/lws+json
      expected: the same RDF as the application/lws+json representation
      actual:   not isomorphic: 10 quads against 9; only in this response: [urn:x-arq:DefaultGraph http://127.0.0.1:4723/touchstone-run-5d0229bf/container-lws-profile-turtle/res1792595700 https://schema.org/size "14"^^xsd:long]; only in the other: [urn:x-arq:DefaultGraph http://127.0.0.1:4723/touchstone-run-5d0229bf/container-lws-profile-turtle/res1792595700 http://schema.org/size "14"^^xsd:long]
    exchange: GET http://127.0.0.1:4723/touchstone-run-5d0229bf/container-lws-profile-turtle/ -> 200
    response body: @prefix lws: <https://www.w3.org/ns/lws#> .
@prefix dcterms: <http://purl.org/dc/terms/> .
@prefix schema: <https://schema.org/> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .

<http://127.0.0.1:4723/touchstone-run-5d0229bf/container-lws-profile-turtle/> a lws:Container ;
  lws:totalItems 2 ;
  lws:items <http://127.0.0.1:4723/touchstone-run-5d0229bf/container-lws-profile-turtle/inner/>, <http://127.0.0.1:4723/touchstone-run-5d0229bf/container-lws-profile-turtle/res1792595700> .
<http://127.0.0.1:4723/touchstone-run-5d0229bf/container-lws-profile-turtle/inner/> a lws:Container ;
  dcterms:modified "2026-10-21T15:15:00Z"^^xsd:dateTime .
<http://127.0.0.1:4723/touchstone-run-5d0229bf/container-lws-profile-turtle/res1792595700> a lws:DataResource ;
  dcterms:format "text/plain" ;
  schema:size "14"^^xsd:long ;
  dcterms:modified "2026-10-21T15:15:00Z"^^xsd:dateTime .

```

**`core/conditional_requests#conditional-get-if-unmodified-since-412`** — failed

```
core/conditional_requests#conditional-get-if-unmodified-since-412 - failed [SHOULD] (2564 ms)
  step 'modified since the epoch, so 412':
    FAILED status code
      expected: 412
      actual:   200
    exchange: GET http://127.0.0.1:4723/touchstone-run-5d0229bf/conditional-get-if-unmodified-since-412/res1792595707 -> 200
    response body: date validator check
```

**`core/linksets#linkset-put-405-when-unsupported`** — inapplicable

```
core/linksets#linkset-put-405-when-unsupported - inapplicable [MUST] (3429 ms)
  inapplicable: precondition 'the linkset does not advertise PUT (otherwise this test does not apply)' does not hold: header Allow matches expected matches /(?i)^(?!.*\bPUT\b)/, got GET, HEAD, OPTIONS, PATCH, PUT
  step 'the linkset does not advertise PUT (otherwise this test does not apply)':
    FAILED header Allow matches
      expected: matches /(?i)^(?!.*\bPUT\b)/
      actual:   GET, HEAD, OPTIONS, PATCH, PUT
    exchange: GET http://127.0.0.1:4723/touchstone-run-5d0229bf/linkset-put-405-when-unsupported/res1792595708?linkset -> 200
    response body: {"linkset":[{"anchor":"http://127.0.0.1:4723/touchstone-run-5d0229bf/linkset-put-405-when-unsupported/res1792595708","up":[{"href":"http://127.0.0.1:4723/touchstone-run-5d0229bf/linkset-put-405-when-unsupported/"}],"type":[{"href":"https://www.w3.org/ns/lws#DataResource"}],"https://www.w3.org/ns/lws#storage":[{"href":"http://127.0.0.1:4723/.well-known/lws-storage"}]}]}
```

**`core/moving#discovery-move-capability`** — inapplicable

```
core/moving#discovery-move-capability - inapplicable [MUST] (2766 ms)
  inapplicable: precondition 'the storage describes a MoveResource capability (otherwise this test does not apply)' does not hold: json /capability selects a value expected a value at /capability, got nothing
  step 'the storage describes a MoveResource capability (otherwise this test does not apply)':
    FAILED json /capability selects a value
      expected: a value at /capability
      actual:   nothing
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`core/moving#move-data-resource`** — inapplicable

```
core/moving#move-data-resource - inapplicable [MUST] (3089 ms)
  inapplicable: precondition 'the storage describes a MoveResource capability (otherwise this test does not apply)' does not hold: json /capability selects a value expected a value at /capability, got nothing
  step 'the storage describes a MoveResource capability (otherwise this test does not apply)':
    FAILED json /capability selects a value
      expected: a value at /capability
      actual:   nothing
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`core/moving#move-updates-container-etags`** — inapplicable

```
core/moving#move-updates-container-etags - inapplicable [MUST] (3261 ms)
  inapplicable: precondition 'the storage describes a MoveResource capability (otherwise this test does not apply)' does not hold: json /capability selects a value expected a value at /capability, got nothing
  step 'the storage describes a MoveResource capability (otherwise this test does not apply)':
    FAILED json /capability selects a value
      expected: a value at /capability
      actual:   nothing
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`core/moving#move-keeps-identifier-content-and-links`** — inapplicable

```
core/moving#move-keeps-identifier-content-and-links - inapplicable [MUST] (4436 ms)
  inapplicable: precondition 'the storage's MoveResource says it preserves identifiers (otherwise this test does not apply)' does not hold: json /capability selects a value expected a value at /capability, got nothing
  step 'the storage's MoveResource says it preserves identifiers (otherwise this test does not apply)':
    FAILED json /capability selects a value
      expected: a value at /capability
      actual:   nothing
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`core/moving#move-invalid-destination-refused`** — inapplicable

```
core/moving#move-invalid-destination-refused - inapplicable [MUST] (684 ms)
  inapplicable: precondition 'the storage describes a MoveResource capability (otherwise this test does not apply)' does not hold: json /capability selects a value expected a value at /capability, got nothing
  step 'the storage describes a MoveResource capability (otherwise this test does not apply)':
    FAILED json /capability selects a value
      expected: a value at /capability
      actual:   nothing
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`core/moving#move-container`** — inapplicable

```
core/moving#move-container - inapplicable [MUST] (5102 ms)
  inapplicable: precondition 'the storage moves containers (otherwise this test does not apply)' does not hold: json /capability selects a value expected a value at /capability, got nothing
  step 'the storage moves containers (otherwise this test does not apply)':
    FAILED json /capability selects a value
      expected: a value at /capability
      actual:   nothing
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`core/moving#move-container-into-itself-refused`** — inapplicable

```
core/moving#move-container-into-itself-refused - inapplicable [MUST] (2008 ms)
  inapplicable: precondition 'the storage moves containers (otherwise this test does not apply)' does not hold: json /capability selects a value expected a value at /capability, got nothing
  step 'the storage moves containers (otherwise this test does not apply)':
    FAILED json /capability selects a value
      expected: a value at /capability
      actual:   nothing
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`core/moving#move-container-refused-without-container-support`** — inapplicable

```
core/moving#move-container-refused-without-container-support - inapplicable [MUST] (1918 ms)
  inapplicable: precondition 'the storage moves data resources but not containers (otherwise this test does not apply)' does not hold: json /capability selects a value expected a value at /capability, got nothing
  step 'the storage moves data resources but not containers (otherwise this test does not apply)':
    FAILED json /capability selects a value
      expected: a value at /capability
      actual:   nothing
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`core/moving#move-needs-create-in-destination`** — inapplicable

```
core/moving#move-needs-create-in-destination - inapplicable [MUST] (103 ms)
  inapplicable: prerequisite: grant [read] on destination to bob: the storage advertises no AccessGrantService and the provisioning adapter 'env' cannot grant access
```

**`core/moving#move-needs-delete-of-resource`** — inapplicable

```
core/moving#move-needs-delete-of-resource - inapplicable [MUST] (165 ms)
  inapplicable: prerequisite: grant [read, create] on destination to bob: the storage advertises no AccessGrantService and the provisioning adapter 'env' cannot grant access
```

**`core/moving#move-notification`** — inapplicable

```
core/moving#move-notification - inapplicable [MUST] (2418 ms)
  inapplicable: precondition 'the storage moves resources and offers webhook subscriptions (otherwise this test does not apply)' does not hold: json /capability selects a value expected a value at /capability, got nothing
  step 'the storage moves resources and offers webhook subscriptions (otherwise this test does not apply)':
    FAILED json /capability selects a value
      expected: a value at /capability
      actual:   nothing
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`core/storage_authorization#storage-root-same-origin`** — inapplicable

```
core/storage_authorization#storage-root-same-origin - inapplicable [MUST] (716 ms)
  inapplicable: precondition 'anyone may read the storage description (otherwise this test does not apply)' does not hold: status code expected 200, got 401
  step 'anyone may read the storage description (otherwise this test does not apply)':
    FAILED status code
      expected: 200
      actual:   401
    exchange: GET http://127.0.0.1:4723/ -> 401
    response body: {"type":"about:blank","title":"Unauthorized","status":401,"detail":"an access token is required","instance":"/"}
```

**`core/access_grants#access-grant-endpoint-is-container`** — inapplicable

```
core/access_grants#access-grant-endpoint-is-container - inapplicable [MUST] (2086 ms)
  inapplicable: step 'The access grant endpoint is an LWS container': the storage description at http://127.0.0.1:4723/.well-known/lws-storage advertises no AccessGrantService
  step 'The access grant endpoint is an LWS container':
    error: cannot build the request: the storage description at http://127.0.0.1:4723/.well-known/lws-storage advertises no AccessGrantService
```

**`core/access_grants#access-grant-create`** — inapplicable

```
core/access_grants#access-grant-create - inapplicable [MUST] (3925 ms)
  inapplicable: step 'grant bob read access to the test container': the storage description at http://127.0.0.1:4723/.well-known/lws-storage advertises no AccessGrantService
  step 'grant bob read access to the test container':
    error: cannot build the request: the storage description at http://127.0.0.1:4723/.well-known/lws-storage advertises no AccessGrantService
```

**`core/access_grants#access-grant-revoke`** — inapplicable

```
core/access_grants#access-grant-revoke - inapplicable [SHOULD] (2082 ms)
  inapplicable: step 'make the test container public (otherwise this test does not apply)': the storage description at http://127.0.0.1:4723/.well-known/lws-storage advertises no AccessGrantService
  step 'make the test container public (otherwise this test does not apply)':
    error: cannot build the request: the storage description at http://127.0.0.1:4723/.well-known/lws-storage advertises no AccessGrantService
```

**`core/access_grants#getContainer-public-read`** — inapplicable

```
core/access_grants#getContainer-public-read - inapplicable [MUST] (111 ms)
  inapplicable: prerequisite: grant [read] on notes to anonymous: the storage advertises no AccessGrantService and the provisioning adapter 'env' cannot grant access
```

**`core/access_grants#readDataResource-public-read`** — inapplicable

```
core/access_grants#readDataResource-public-read - inapplicable [MUST] (42 ms)
  inapplicable: prerequisite: grant [read] on created to anonymous: the storage advertises no AccessGrantService and the provisioning adapter 'env' cannot grant access
```

**`core/access_grants#access-grant-authenticated-agent`** — inapplicable

```
core/access_grants#access-grant-authenticated-agent - inapplicable [MUST] (49 ms)
  inapplicable: prerequisite: grant [read] on created to bob: the storage advertises no AccessGrantService and the provisioning adapter 'env' cannot grant access
```

**`core/access_grants#access-grant-extra-properties-accepted`** — inapplicable

```
core/access_grants#access-grant-extra-properties-accepted - inapplicable [MAY] (2325 ms)
  inapplicable: step 'grant bob read access, with a property this specification does not define': the storage description at http://127.0.0.1:4723/.well-known/lws-storage advertises no AccessGrantService
  step 'grant bob read access, with a property this specification does not define':
    error: cannot build the request: the storage description at http://127.0.0.1:4723/.well-known/lws-storage advertises no AccessGrantService
```

**`core/access_grants#access-grant-inbox-notified`** — inapplicable

```
core/access_grants#access-grant-inbox-notified - inapplicable [SHOULD] (806 ms)
  inapplicable: step 'grant bob read, naming this test's inbox': the storage description at http://127.0.0.1:4723/.well-known/lws-storage advertises no AccessGrantService
  step 'grant bob read, naming this test's inbox':
    error: cannot build the request: the storage description at http://127.0.0.1:4723/.well-known/lws-storage advertises no AccessGrantService
```

**`core/access_grants#access-request-create`** — inapplicable

```
core/access_grants#access-request-create - inapplicable [MUST] (2705 ms)
  inapplicable: step 'bob asks for read access to the test container': the storage description at http://127.0.0.1:4723/.well-known/lws-storage advertises no AccessRequestService
  step 'bob asks for read access to the test container':
    error: cannot build the request: the storage description at http://127.0.0.1:4723/.well-known/lws-storage advertises no AccessRequestService
```

**`core/access_grants#access-grant-document-shape`** — inapplicable

```
core/access_grants#access-grant-document-shape - inapplicable [MUST] (2724 ms)
  inapplicable: step 'grant bob read access to it': the storage description at http://127.0.0.1:4723/.well-known/lws-storage advertises no AccessGrantService
  step 'grant bob read access to it':
    error: cannot build the request: the storage description at http://127.0.0.1:4723/.well-known/lws-storage advertises no AccessGrantService
```

**`core/access_grants#access-grant-incomplete-refused`** — inapplicable

```
core/access_grants#access-grant-incomplete-refused - inapplicable [MUST] (3109 ms)
  inapplicable: step 'a grant without its type is refused': the storage description at http://127.0.0.1:4723/.well-known/lws-storage advertises no AccessGrantService
  step 'a grant without its type is refused':
    error: cannot build the request: the storage description at http://127.0.0.1:4723/.well-known/lws-storage advertises no AccessGrantService
```

**`core/access_grants#access-grant-constraints-all-satisfied`** — inapplicable

```
core/access_grants#access-grant-constraints-all-satisfied - inapplicable [MUST] (4770 ms)
  inapplicable: precondition 'the grant service advertises the Access Profile (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"AccessGrantService"},{"pointer":"/conformsTo","hasValue":"https://www.w3.org/ns/lws#AccessProfile"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the grant service advertises the Access Profile (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"AccessGrantService"},{"pointer":"/conformsTo","hasValue":"https://www.w3.org/ns/lws#AccessProfile"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`core/access_grants#access-grant-left-operands-accepted`** — inapplicable

```
core/access_grants#access-grant-left-operands-accepted - inapplicable [MUST] (3199 ms)
  inapplicable: precondition 'the grant service advertises the Access Profile (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"AccessGrantService"},{"pointer":"/conformsTo","hasValue":"https://www.w3.org/ns/lws#AccessProfile"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the grant service advertises the Access Profile (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"AccessGrantService"},{"pointer":"/conformsTo","hasValue":"https://www.w3.org/ns/lws#AccessProfile"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`core/access_grants#access-grant-constraint-format`** — inapplicable

```
core/access_grants#access-grant-constraint-format - inapplicable [MUST] (2722 ms)
  inapplicable: precondition 'the grant service advertises the Access Profile (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"AccessGrantService"},{"pointer":"/conformsTo","hasValue":"https://www.w3.org/ns/lws#AccessProfile"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the grant service advertises the Access Profile (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"AccessGrantService"},{"pointer":"/conformsTo","hasValue":"https://www.w3.org/ns/lws#AccessProfile"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`core/access_grants#access-grant-constraint-type`** — inapplicable

```
core/access_grants#access-grant-constraint-type - inapplicable [MUST] (6212 ms)
  inapplicable: precondition 'the grant service advertises the Access Profile (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"AccessGrantService"},{"pointer":"/conformsTo","hasValue":"https://www.w3.org/ns/lws#AccessProfile"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the grant service advertises the Access Profile (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"AccessGrantService"},{"pointer":"/conformsTo","hasValue":"https://www.w3.org/ns/lws#AccessProfile"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`core/access_grants#access-grant-constraint-client`** — inapplicable

```
core/access_grants#access-grant-constraint-client - inapplicable [MUST] (2635 ms)
  inapplicable: precondition 'the grant service advertises the Access Profile (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"AccessGrantService"},{"pointer":"/conformsTo","hasValue":"https://www.w3.org/ns/lws#AccessProfile"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the grant service advertises the Access Profile (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"AccessGrantService"},{"pointer":"/conformsTo","hasValue":"https://www.w3.org/ns/lws#AccessProfile"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`core/access_grants#container-listing-filtered-metadata`** — inapplicable

```
core/access_grants#container-listing-filtered-metadata - inapplicable [MAY] (555 ms)
  inapplicable: prerequisite: grant [read] on box to bob: the storage advertises no AccessGrantService and the provisioning adapter 'env' cannot grant access
```

**`core/notifications#notification-service-advertised`** — inapplicable

```
core/notifications#notification-service-advertised - inapplicable [MUST] (2764 ms)
  inapplicable: precondition 'the storage advertises notifications (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"NotificationService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage advertises notifications (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"NotificationService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`core/notifications#subscription-create`** — inapplicable

```
core/notifications#subscription-create - inapplicable [MUST] (2920 ms)
  inapplicable: precondition 'the storage offers webhook subscriptions (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers webhook subscriptions (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`core/notifications#subscription-missing-type-refused`** — inapplicable

```
core/notifications#subscription-missing-type-refused - inapplicable [MUST] (3140 ms)
  inapplicable: precondition 'the storage offers webhook subscriptions (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers webhook subscriptions (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`core/notifications#subscription-unadvertised-type-refused`** — inapplicable

```
core/notifications#subscription-unadvertised-type-refused - inapplicable [MUST] (5387 ms)
  inapplicable: precondition 'the storage offers webhook subscriptions (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers webhook subscriptions (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`core/notifications#subscription-missing-topic-refused`** — inapplicable

```
core/notifications#subscription-missing-topic-refused - inapplicable [MUST] (3148 ms)
  inapplicable: precondition 'the storage offers webhook subscriptions (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers webhook subscriptions (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`core/notifications#subscription-unreadable-topic-refused`** — inapplicable

```
core/notifications#subscription-unreadable-topic-refused - inapplicable [MUST] (209 ms)
  inapplicable: prerequisite: grant [read] on shared to bob: the storage advertises no AccessGrantService and the provisioning adapter 'env' cannot grant access
```

**`core/notifications#subscription-after-revocation-refused`** — inapplicable

```
core/notifications#subscription-after-revocation-refused - inapplicable [MUST] (2771 ms)
  inapplicable: precondition 'the storage offers webhook subscriptions (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers webhook subscriptions (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`core/notifications#notification-delivered-create`** — inapplicable

```
core/notifications#notification-delivered-create - inapplicable [MUST] (385 ms)
  inapplicable: precondition 'the storage offers webhook subscriptions (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers webhook subscriptions (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`core/notifications#notification-delivered-update`** — inapplicable

```
core/notifications#notification-delivered-update - inapplicable [MUST] (4023 ms)
  inapplicable: precondition 'the storage offers webhook subscriptions (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers webhook subscriptions (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`core/notifications#notification-delivered-delete`** — inapplicable

```
core/notifications#notification-delivered-delete - inapplicable [MUST] (4126 ms)
  inapplicable: precondition 'the storage offers webhook subscriptions (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers webhook subscriptions (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`core/notifications#notification-not-delivered-for-unreadable-resource`** — inapplicable

```
core/notifications#notification-not-delivered-for-unreadable-resource - inapplicable [MUST] (2609 ms)
  inapplicable: prerequisite: grant [read] on box to bob: the storage advertises no AccessGrantService and the provisioning adapter 'env' cannot grant access
```

**`core/notifications#notification-stops-after-revocation`** — inapplicable

```
core/notifications#notification-stops-after-revocation - inapplicable [MUST] (898 ms)
  inapplicable: prerequisite: grant [read] on kept to bob: the storage advertises no AccessGrantService and the provisioning adapter 'env' cannot grant access
```

**`core/notifications#notification-actor-omitted`** — inapplicable

```
core/notifications#notification-actor-omitted - inapplicable [SHOULD] (4083 ms)
  inapplicable: precondition 'the storage offers webhook subscriptions (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers webhook subscriptions (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`core/notifications#notification-delivered-in-subcontainer`** — inapplicable

```
core/notifications#notification-delivered-in-subcontainer - inapplicable [MUST] (4056 ms)
  inapplicable: precondition 'the storage offers webhook subscriptions (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers webhook subscriptions (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`core/notifications#notification-scope-data-resource-only`** — inapplicable

```
core/notifications#notification-scope-data-resource-only - inapplicable [MUST] (4113 ms)
  inapplicable: precondition 'the storage offers webhook subscriptions (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers webhook subscriptions (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`core/pagination#pagination-first-page`** — inapplicable

```
core/pagination#pagination-first-page - inapplicable [MUST] (3565 ms)
  inapplicable: precondition 'the server splits a five-member container into pages (otherwise this test does not apply)' does not hold: Link rel="first" expected a matching link, got <http://www.w3.org/ns/ldp#BasicContainer>; rel="type", <http://www.w3.org/ns/ldp#Container>; rel="type", <http://www.w3.org/ns/ldp#Resource>; rel="type", </touchstone-run-5d0229bf/pagination-first-page/paged/.acl>; rel="acl", </touchstone-run-5d0229bf/pagination-first-page/paged/.meta>; rel="describedby", <http://127.0.0.1:4723/.well-known/solid>; rel="http://www.w3.org/ns/solid/terms#storageDescription", </touchstone-run-5d0229bf/pagination-first-page/paged/?linkset>; rel="linkset"; type="application/linkset+json", </touchstone-run-5d0229bf/pagination-first-page/>; rel="up", <https://www.w3.org/ns/lws#Container>; rel="type", <http://127.0.0.1:4723/.well-known/lws-storage>; rel="https://www.w3.org/ns/lws#storage"
  step 'the server splits a five-member container into pages (otherwise this test does not apply)':
    FAILED Link rel="first"
      expected: a matching link
      actual:   <http://www.w3.org/ns/ldp#BasicContainer>; rel="type", <http://www.w3.org/ns/ldp#Container>; rel="type", <http://www.w3.org/ns/ldp#Resource>; rel="type", </touchstone-run-5d0229bf/pagination-first-page/paged/.acl>; rel="acl", </touchstone-run-5d0229bf/pagination-first-page/paged/.meta>; rel="describedby", <http://127.0.0.1:4723/.well-known/solid>; rel="http://www.w3.org/ns/solid/terms#storageDescription", </touchstone-run-5d0229bf/pagination-first-page/paged/?linkset>; rel="linkset"; type="application/linkset+json", </touchstone-run-5d0229bf/pagination-first-page/>; rel="up", <https://www.w3.org/ns/lws#Container>; rel="type", <http://127.0.0.1:4723/.well-known/lws-storage>; rel="https://www.w3.org/ns/lws#storage"
    exchange: GET http://127.0.0.1:4723/touchstone-run-5d0229bf/pagination-first-page/paged/ -> 200
    response body: {"@context":"https://www.w3.org/ns/lws/v1","id":"http://127.0.0.1:4723/touchstone-run-5d0229bf/pagination-first-page/paged/","type":"Container","totalItems":4,"items":[{"id":"http://127.0.0.1:4723/touchstone-run-5d0229bf/pagination-first-page/paged/res1792595722","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T15:15:22Z"},{"id":"http://127.0.0.1:4723/touchstone-run-5d0229bf/pagination-first-page/paged/res1792595722-1792595722","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T15:15:22Z"},{"id":"http://127.0.0.1:4723/touchstone-run-5d0229bf/pagination-first-page/paged/res1792595723","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T15:15:23Z"},{"id":"http://127.0.0.1:4723/touchstone-run-5d0229bf/pagination-first-page/paged/res1792595723-1792595723","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T15:15:23Z"}]}
```

**`core/pagination#pagination-next-page`** — inapplicable

```
core/pagination#pagination-next-page - inapplicable [MUST] (2754 ms)
  inapplicable: precondition 'the server splits a five-member container into pages (otherwise this test does not apply)' does not hold: Link rel="first" expected a matching link, got <http://www.w3.org/ns/ldp#BasicContainer>; rel="type", <http://www.w3.org/ns/ldp#Container>; rel="type", <http://www.w3.org/ns/ldp#Resource>; rel="type", </touchstone-run-5d0229bf/pagination-next-page/paged/.acl>; rel="acl", </touchstone-run-5d0229bf/pagination-next-page/paged/.meta>; rel="describedby", <http://127.0.0.1:4723/.well-known/solid>; rel="http://www.w3.org/ns/solid/terms#storageDescription", </touchstone-run-5d0229bf/pagination-next-page/paged/?linkset>; rel="linkset"; type="application/linkset+json", </touchstone-run-5d0229bf/pagination-next-page/>; rel="up", <https://www.w3.org/ns/lws#Container>; rel="type", <http://127.0.0.1:4723/.well-known/lws-storage>; rel="https://www.w3.org/ns/lws#storage"
  step 'the server splits a five-member container into pages (otherwise this test does not apply)':
    FAILED Link rel="first"
      expected: a matching link
      actual:   <http://www.w3.org/ns/ldp#BasicContainer>; rel="type", <http://www.w3.org/ns/ldp#Container>; rel="type", <http://www.w3.org/ns/ldp#Resource>; rel="type", </touchstone-run-5d0229bf/pagination-next-page/paged/.acl>; rel="acl", </touchstone-run-5d0229bf/pagination-next-page/paged/.meta>; rel="describedby", <http://127.0.0.1:4723/.well-known/solid>; rel="http://www.w3.org/ns/solid/terms#storageDescription", </touchstone-run-5d0229bf/pagination-next-page/paged/?linkset>; rel="linkset"; type="application/linkset+json", </touchstone-run-5d0229bf/pagination-next-page/>; rel="up", <https://www.w3.org/ns/lws#Container>; rel="type", <http://127.0.0.1:4723/.well-known/lws-storage>; rel="https://www.w3.org/ns/lws#storage"
    exchange: GET http://127.0.0.1:4723/touchstone-run-5d0229bf/pagination-next-page/paged/ -> 200
    response body: {"@context":"https://www.w3.org/ns/lws/v1","id":"http://127.0.0.1:4723/touchstone-run-5d0229bf/pagination-next-page/paged/","type":"Container","totalItems":3,"items":[{"id":"http://127.0.0.1:4723/touchstone-run-5d0229bf/pagination-next-page/paged/res1792595723","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T15:15:23Z"},{"id":"http://127.0.0.1:4723/touchstone-run-5d0229bf/pagination-next-page/paged/res1792595723-1792595723","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T15:15:23Z"},{"id":"http://127.0.0.1:4723/touchstone-run-5d0229bf/pagination-next-page/paged/res1792595724","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T15:15:24Z"}]}
```

**`core/pagination#pagination-single-page`** — inapplicable

```
core/pagination#pagination-single-page - inapplicable [MUST] (2754 ms)
  inapplicable: precondition 'the listing is paginated and holds all five members on its page (otherwise this test does not apply)' does not hold: Link rel="first" expected a matching link, got <http://www.w3.org/ns/ldp#BasicContainer>; rel="type", <http://www.w3.org/ns/ldp#Container>; rel="type", <http://www.w3.org/ns/ldp#Resource>; rel="type", </touchstone-run-5d0229bf/pagination-single-page/paged/.acl>; rel="acl", </touchstone-run-5d0229bf/pagination-single-page/paged/.meta>; rel="describedby", <http://127.0.0.1:4723/.well-known/solid>; rel="http://www.w3.org/ns/solid/terms#storageDescription", </touchstone-run-5d0229bf/pagination-single-page/paged/?linkset>; rel="linkset"; type="application/linkset+json", </touchstone-run-5d0229bf/pagination-single-page/>; rel="up", <https://www.w3.org/ns/lws#Container>; rel="type", <http://127.0.0.1:4723/.well-known/lws-storage>; rel="https://www.w3.org/ns/lws#storage"
  step 'the listing is paginated and holds all five members on its page (otherwise this test does not apply)':
    FAILED Link rel="first"
      expected: a matching link
      actual:   <http://www.w3.org/ns/ldp#BasicContainer>; rel="type", <http://www.w3.org/ns/ldp#Container>; rel="type", <http://www.w3.org/ns/ldp#Resource>; rel="type", </touchstone-run-5d0229bf/pagination-single-page/paged/.acl>; rel="acl", </touchstone-run-5d0229bf/pagination-single-page/paged/.meta>; rel="describedby", <http://127.0.0.1:4723/.well-known/solid>; rel="http://www.w3.org/ns/solid/terms#storageDescription", </touchstone-run-5d0229bf/pagination-single-page/paged/?linkset>; rel="linkset"; type="application/linkset+json", </touchstone-run-5d0229bf/pagination-single-page/>; rel="up", <https://www.w3.org/ns/lws#Container>; rel="type", <http://127.0.0.1:4723/.well-known/lws-storage>; rel="https://www.w3.org/ns/lws#storage"
    exchange: GET http://127.0.0.1:4723/touchstone-run-5d0229bf/pagination-single-page/paged/ -> 200
    response body: {"@context":"https://www.w3.org/ns/lws/v1","id":"http://127.0.0.1:4723/touchstone-run-5d0229bf/pagination-single-page/paged/","type":"Container","totalItems":3,"items":[{"id":"http://127.0.0.1:4723/touchstone-run-5d0229bf/pagination-single-page/paged/res1792595723","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T15:15:23Z"},{"id":"http://127.0.0.1:4723/touchstone-run-5d0229bf/pagination-single-page/paged/res1792595723-1792595723","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T15:15:23Z"},{"id":"http://127.0.0.1:4723/touchstone-run-5d0229bf/pagination-single-page/paged/res1792595724","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T15:15:24Z"}]}
```

**`core/pagination#pagination-last-page`** — inapplicable

```
core/pagination#pagination-last-page - inapplicable [MUST] (2775 ms)
  inapplicable: precondition 'the server splits a five-member container into pages (otherwise this test does not apply)' does not hold: Link rel="first" expected a matching link, got <http://www.w3.org/ns/ldp#BasicContainer>; rel="type", <http://www.w3.org/ns/ldp#Container>; rel="type", <http://www.w3.org/ns/ldp#Resource>; rel="type", </touchstone-run-5d0229bf/pagination-last-page/paged/.acl>; rel="acl", </touchstone-run-5d0229bf/pagination-last-page/paged/.meta>; rel="describedby", <http://127.0.0.1:4723/.well-known/solid>; rel="http://www.w3.org/ns/solid/terms#storageDescription", </touchstone-run-5d0229bf/pagination-last-page/paged/?linkset>; rel="linkset"; type="application/linkset+json", </touchstone-run-5d0229bf/pagination-last-page/>; rel="up", <https://www.w3.org/ns/lws#Container>; rel="type", <http://127.0.0.1:4723/.well-known/lws-storage>; rel="https://www.w3.org/ns/lws#storage"
  step 'the server splits a five-member container into pages (otherwise this test does not apply)':
    FAILED Link rel="first"
      expected: a matching link
      actual:   <http://www.w3.org/ns/ldp#BasicContainer>; rel="type", <http://www.w3.org/ns/ldp#Container>; rel="type", <http://www.w3.org/ns/ldp#Resource>; rel="type", </touchstone-run-5d0229bf/pagination-last-page/paged/.acl>; rel="acl", </touchstone-run-5d0229bf/pagination-last-page/paged/.meta>; rel="describedby", <http://127.0.0.1:4723/.well-known/solid>; rel="http://www.w3.org/ns/solid/terms#storageDescription", </touchstone-run-5d0229bf/pagination-last-page/paged/?linkset>; rel="linkset"; type="application/linkset+json", </touchstone-run-5d0229bf/pagination-last-page/>; rel="up", <https://www.w3.org/ns/lws#Container>; rel="type", <http://127.0.0.1:4723/.well-known/lws-storage>; rel="https://www.w3.org/ns/lws#storage"
    exchange: GET http://127.0.0.1:4723/touchstone-run-5d0229bf/pagination-last-page/paged/ -> 200
    response body: {"@context":"https://www.w3.org/ns/lws/v1","id":"http://127.0.0.1:4723/touchstone-run-5d0229bf/pagination-last-page/paged/","type":"Container","totalItems":4,"items":[{"id":"http://127.0.0.1:4723/touchstone-run-5d0229bf/pagination-last-page/paged/res1792595723","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T15:15:23Z"},{"id":"http://127.0.0.1:4723/touchstone-run-5d0229bf/pagination-last-page/paged/res1792595723-1792595723","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T15:15:23Z"},{"id":"http://127.0.0.1:4723/touchstone-run-5d0229bf/pagination-last-page/paged/res1792595724","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T15:15:24Z"},{"id":"http://127.0.0.1:4723/touchstone-run-5d0229bf/pagination-last-page/paged/res1792595724-1792595724","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T15:15:24Z"}]}
```

**`core/pagination#pagination-totalitems-all-pages`** — inapplicable

```
core/pagination#pagination-totalitems-all-pages - inapplicable [SHOULD] (4338 ms)
  inapplicable: precondition 'the server splits a five-member container into pages (otherwise this test does not apply)' does not hold: Link rel="first" expected a matching link, got <http://www.w3.org/ns/ldp#BasicContainer>; rel="type", <http://www.w3.org/ns/ldp#Container>; rel="type", <http://www.w3.org/ns/ldp#Resource>; rel="type", </touchstone-run-5d0229bf/pagination-totalitems-all-pages/paged/.acl>; rel="acl", </touchstone-run-5d0229bf/pagination-totalitems-all-pages/paged/.meta>; rel="describedby", <http://127.0.0.1:4723/.well-known/solid>; rel="http://www.w3.org/ns/solid/terms#storageDescription", </touchstone-run-5d0229bf/pagination-totalitems-all-pages/paged/?linkset>; rel="linkset"; type="application/linkset+json", </touchstone-run-5d0229bf/pagination-totalitems-all-pages/>; rel="up", <https://www.w3.org/ns/lws#Container>; rel="type", <http://127.0.0.1:4723/.well-known/lws-storage>; rel="https://www.w3.org/ns/lws#storage"
  step 'the server splits a five-member container into pages (otherwise this test does not apply)':
    FAILED Link rel="first"
      expected: a matching link
      actual:   <http://www.w3.org/ns/ldp#BasicContainer>; rel="type", <http://www.w3.org/ns/ldp#Container>; rel="type", <http://www.w3.org/ns/ldp#Resource>; rel="type", </touchstone-run-5d0229bf/pagination-totalitems-all-pages/paged/.acl>; rel="acl", </touchstone-run-5d0229bf/pagination-totalitems-all-pages/paged/.meta>; rel="describedby", <http://127.0.0.1:4723/.well-known/solid>; rel="http://www.w3.org/ns/solid/terms#storageDescription", </touchstone-run-5d0229bf/pagination-totalitems-all-pages/paged/?linkset>; rel="linkset"; type="application/linkset+json", </touchstone-run-5d0229bf/pagination-totalitems-all-pages/>; rel="up", <https://www.w3.org/ns/lws#Container>; rel="type", <http://127.0.0.1:4723/.well-known/lws-storage>; rel="https://www.w3.org/ns/lws#storage"
    exchange: GET http://127.0.0.1:4723/touchstone-run-5d0229bf/pagination-totalitems-all-pages/paged/ -> 200
    response body: {"@context":"https://www.w3.org/ns/lws/v1","id":"http://127.0.0.1:4723/touchstone-run-5d0229bf/pagination-totalitems-all-pages/paged/","type":"Container","totalItems":4,"items":[{"id":"http://127.0.0.1:4723/touchstone-run-5d0229bf/pagination-totalitems-all-pages/paged/res1792595723","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T15:15:23Z"},{"id":"http://127.0.0.1:4723/touchstone-run-5d0229bf/pagination-totalitems-all-pages/paged/res1792595723-1792595723","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T15:15:23Z"},{"id":"http://127.0.0.1:4723/touchstone-run-5d0229bf/pagination-totalitems-all-pages/paged/res1792595724","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T15:15:24Z"},{"id":"http://127.0.0.1:4723/touchstone-run-5d0229bf/pagination-totalitems-all-pages/paged/res1792595724-1792595724","type":"DataResource","format":"text/plain","size":8,"modified":"2026-10-21T15:15:24Z"}]}
```

**`notifications/webhook/manifest#webhook-subscription-response`** — inapplicable

```
notifications/webhook/manifest#webhook-subscription-response - inapplicable [MUST] (616 ms)
  inapplicable: precondition 'the storage offers webhook subscriptions (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers webhook subscriptions (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`notifications/webhook/manifest#webhook-subscription-expires-supported`** — inapplicable

```
notifications/webhook/manifest#webhook-subscription-expires-supported - inapplicable [MUST] (1132 ms)
  inapplicable: precondition 'the storage offers webhook subscriptions (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers webhook subscriptions (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`notifications/webhook/manifest#webhook-subscription-listed`** — inapplicable

```
notifications/webhook/manifest#webhook-subscription-listed - inapplicable [MUST] (564 ms)
  inapplicable: prerequisite: grant [read] on watched to bob: the storage advertises no AccessGrantService and the provisioning adapter 'env' cannot grant access
```

**`notifications/webhook/manifest#webhook-subscription-get-delete`** — inapplicable

```
notifications/webhook/manifest#webhook-subscription-get-delete - inapplicable [MUST] (314 ms)
  inapplicable: precondition 'the storage offers webhook subscriptions (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers webhook subscriptions (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`notifications/webhook/manifest#webhook-delivery-lws-json`** — inapplicable

```
notifications/webhook/manifest#webhook-delivery-lws-json - inapplicable [MUST] (4510 ms)
  inapplicable: precondition 'the storage offers webhook subscriptions (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers webhook subscriptions (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`notifications/webhook/manifest#webhook-delivery-signed`** — inapplicable

```
notifications/webhook/manifest#webhook-delivery-signed - inapplicable [SHOULD] (4958 ms)
  inapplicable: precondition 'the storage offers webhook subscriptions (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers webhook subscriptions (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`notifications/webhook/manifest#webhook-signature-components`** — inapplicable

```
notifications/webhook/manifest#webhook-signature-components - inapplicable [MUST] (263 ms)
  inapplicable: precondition 'the storage offers webhook subscriptions (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers webhook subscriptions (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`notifications/webhook/manifest#webhook-signing-key-published`** — inapplicable

```
notifications/webhook/manifest#webhook-signing-key-published - inapplicable [MUST] (4276 ms)
  inapplicable: precondition 'the storage offers webhook subscriptions (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers webhook subscriptions (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`notifications/webhook/manifest#webhook-signature-verifies`** — inapplicable

```
notifications/webhook/manifest#webhook-signature-verifies - inapplicable [MUST] (7661 ms)
  inapplicable: precondition 'the storage offers webhook subscriptions (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers webhook subscriptions (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`notifications/webhook/manifest#webhook-delivery-retried`** — inapplicable

```
notifications/webhook/manifest#webhook-delivery-retried - inapplicable [MAY] (2772 ms)
  inapplicable: precondition 'the storage offers webhook subscriptions (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers webhook subscriptions (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`notifications/webhook/manifest#webhook-subscription-deactivated`** — inapplicable

```
notifications/webhook/manifest#webhook-subscription-deactivated - inapplicable [MAY] (3990 ms)
  inapplicable: precondition 'the storage offers webhook subscriptions (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers webhook subscriptions (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"NotificationService"},{"pointer":"/subscriptionType","hasValue":"WebhookSubscription"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#index-services-advertised`** — inapplicable

```
index/manifest#index-services-advertised - inapplicable [MUST] (1394 ms)
  inapplicable: precondition 'the storage offers a Type Index or Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","matches":"^Type(Index|Search)Service$"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Index or Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","matches":"^Type(Index|Search)Service$"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-index-lists-readable-types`** — inapplicable

```
index/manifest#type-index-lists-readable-types - inapplicable [MUST] (223 ms)
  inapplicable: prerequisite: grant [read] on visible to bob: the storage advertises no AccessGrantService and the provisioning adapter 'env' cannot grant access
```

**`index/manifest#type-index-omits-unreadable-type`** — inapplicable

```
index/manifest#type-index-omits-unreadable-type - inapplicable [MUST] (3914 ms)
  inapplicable: prerequisite: grant [read] on visible to bob: the storage advertises no AccessGrantService and the provisioning adapter 'env' cannot grant access
```

**`index/manifest#type-index-not-shared`** — inapplicable

```
index/manifest#type-index-not-shared - inapplicable [MUST] (3778 ms)
  inapplicable: precondition 'the storage offers a Type Index Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeIndexService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Index Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeIndexService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-by-type`** — inapplicable

```
index/manifest#type-search-by-type - inapplicable [MUST] (4050 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-and-or`** — inapplicable

```
index/manifest#type-search-and-or - inapplicable [MUST] (4124 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-native-classes`** — inapplicable

```
index/manifest#type-search-native-classes - inapplicable [MUST] (3512 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-no-match`** — inapplicable

```
index/manifest#type-search-no-match - inapplicable [MUST] (1760 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-duplicate-groups`** — inapplicable

```
index/manifest#type-search-duplicate-groups - inapplicable [MUST] (2252 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-at-members-ignored`** — inapplicable

```
index/manifest#type-search-at-members-ignored - inapplicable [MUST] (5603 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-empty-key-absent`** — inapplicable

```
index/manifest#type-search-empty-key-absent - inapplicable [MUST] (7180 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-empty-group-rejected`** — inapplicable

```
index/manifest#type-search-empty-group-rejected - inapplicable [MUST] (5758 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-type-not-array-rejected`** — inapplicable

```
index/manifest#type-search-type-not-array-rejected - inapplicable [MUST] (558 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-bad-element-rejected`** — inapplicable

```
index/manifest#type-search-bad-element-rejected - inapplicable [MUST] (2600 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-malformed-json-rejected`** — inapplicable

```
index/manifest#type-search-malformed-json-rejected - inapplicable [MUST] (3002 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-relative-iri-rejected`** — inapplicable

```
index/manifest#type-search-relative-iri-rejected - inapplicable [MUST] (3297 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-missing-content-type-rejected`** — inapplicable

```
index/manifest#type-search-missing-content-type-rejected - inapplicable [MUST] (3072 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-unsupported-format-rejected`** — inapplicable

```
index/manifest#type-search-unsupported-format-rejected - inapplicable [MUST] (4181 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-unsupported-format-accept-query`** — inapplicable

```
index/manifest#type-search-unsupported-format-accept-query - inapplicable [SHOULD] (4401 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-accept-query-advertised`** — inapplicable

```
index/manifest#type-search-accept-query-advertised - inapplicable [SHOULD] (3433 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-not-acceptable`** — inapplicable

```
index/manifest#type-search-not-acceptable - inapplicable [MUST] (7452 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-unindexed-relation`** — inapplicable

```
index/manifest#type-search-unindexed-relation - inapplicable [MUST] (4614 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-structural-relation-not-indexed`** — inapplicable

```
index/manifest#type-search-structural-relation-not-indexed - inapplicable [MUST] (6549 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-authorization-filtered`** — inapplicable

```
index/manifest#type-search-authorization-filtered - inapplicable [MUST] (408 ms)
  inapplicable: prerequisite: grant [read] on visible to bob: the storage advertises no AccessGrantService and the provisioning adapter 'env' cannot grant access
```

**`index/manifest#type-search-revoked-not-shown`** — inapplicable

```
index/manifest#type-search-revoked-not-shown - inapplicable [MUST] (5453 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-not-shared`** — inapplicable

```
index/manifest#type-search-not-shared - inapplicable [MUST] (4833 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-type-from-link-header`** — inapplicable

```
index/manifest#type-search-type-from-link-header - inapplicable [SHOULD] (4809 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-type-from-content`** — inapplicable

```
index/manifest#type-search-type-from-content - inapplicable [MAY] (4892 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-content-types-identical`** — inapplicable

```
index/manifest#type-search-content-types-identical - inapplicable [MUST] (1723 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-reflects-update`** — inapplicable

```
index/manifest#type-search-reflects-update - inapplicable [SHOULD] (4801 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-reflects-delete`** — inapplicable

```
index/manifest#type-search-reflects-delete - inapplicable [SHOULD] (3467 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-vary-accept`** — inapplicable

```
index/manifest#type-search-vary-accept - inapplicable [MUST] (4409 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-safe`** — inapplicable

```
index/manifest#type-search-safe - inapplicable [MAY] (3825 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-next-page`** — inapplicable

```
index/manifest#type-search-next-page - inapplicable [MUST] (2676 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-relation-filter`** — inapplicable

```
index/manifest#type-search-relation-filter - inapplicable [MAY] (2949 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-relation-cnf`** — inapplicable

```
index/manifest#type-search-relation-cnf - inapplicable [MAY] (2107 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-relation-from-link-header`** — inapplicable

```
index/manifest#type-search-relation-from-link-header - inapplicable [SHOULD] (2728 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-too-complex`** — inapplicable

```
index/manifest#type-search-too-complex - inapplicable [MUST] (2334 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-unrecognized-page-link`** — inapplicable

```
index/manifest#type-search-unrecognized-page-link - inapplicable [MUST] (1051 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
```

**`index/manifest#type-search-content-location-protected`** — inapplicable

```
index/manifest#type-search-content-location-protected - inapplicable [MUST] (1230 ms)
  inapplicable: precondition 'the storage offers a Type Search Service (otherwise this test does not apply)' does not hold: json /service some expected some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}], got [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
  step 'the storage offers a Type Search Service (otherwise this test does not apply)':
    FAILED json /service some
      expected: some element satisfies [{"pointer":"/type","hasValue":"TypeSearchService"}]
      actual:   [{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]
    exchange: GET http://127.0.0.1:4723/.well-known/lws-storage -> 200
    response body: {"@context":["https://www.w3.org/ns/cid/v1","https://www.w3.org/ns/lws/v1"],"id":"http://127.0.0.1:4723/.well-known/lws-storage","type":"Storage","service":[{"type":"StorageRoot","serviceEndpoint":"http://127.0.0.1:4723/"}]}
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
| [`access-access-collection`](https://www.w3.org/TR/lws10-core/#access-property) | MUST | INAPPLICABLE | 2 |
| [`access-access-required`](https://www.w3.org/TR/lws10-core/#access-property) | MUST | INAPPLICABLE | 2 |
| [`access-endpoints-are-lws-containers`](https://www.w3.org/TR/lws10-core/#access-protocol) | MUST | INAPPLICABLE | 1 |
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
| [`access-services-advertised`](https://www.w3.org/TR/lws10-core/#access-discovery) | MUST | INAPPLICABLE | 1 |
| [`access-storage-required`](https://www.w3.org/TR/lws10-core/#access-storage-property) | MUST | INAPPLICABLE | 2 |
| [`access-storage-uri`](https://www.w3.org/TR/lws10-core/#access-storage-property) | MUST | INAPPLICABLE | 1 |
| [`access-type-required`](https://www.w3.org/TR/lws10-core/#access-type-property) | MUST | INAPPLICABLE | 2 |
| [`access-type-values`](https://www.w3.org/TR/lws10-core/#access-type-property) | MUST | INAPPLICABLE | 2 |
| [`authn-audience-restriction-recommended`](https://www.w3.org/TR/lws10-core/#authentication-data-model) | SHOULD | PASS | 1 |
| [`authn-client-claim`](https://www.w3.org/TR/lws10-core/#authentication-data-model) | MUST | PASS | 2 |
| [`authn-credential-signed`](https://www.w3.org/TR/lws10-core/#authentication-validation) | MUST | PASS | 8 |
| [`authn-credential-tamper-evident-claims`](https://www.w3.org/TR/lws10-core/#authentication-data-model) | MUST | PASS | 3 |
| [`authn-issuer-claim-uri`](https://www.w3.org/TR/lws10-core/#authentication-data-model) | MUST | PASS | 1 |
| [`authn-issuer-trust-out-of-band`](https://www.w3.org/TR/lws10-core/#authentication-validation) | MAY | UNCOVERED | 0 |
| [`authn-subject-claim-uri`](https://www.w3.org/TR/lws10-core/#authentication-data-model) | MUST | PASS | 1 |
| [`authn-suite-token-type-uri`](https://www.w3.org/TR/lws10-core/#authentication-type-identifier) | MUST | PASS | 1 |
| [`authz-401-storage-link`](https://www.w3.org/TR/lws10-core/#authorization-server-discovery) | MUST | FAIL | 2 |
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
| [`authz-client-storage-root-same-origin`](https://www.w3.org/TR/lws10-core/#authorization-discovery-validation) | MUST | INAPPLICABLE | 1 |
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
| [`capability-move-applies-to`](https://www.w3.org/TR/lws10-core/#storage-description-capabilities) | MUST | INAPPLICABLE | 3 |
| [`capability-move-preserves-identifier`](https://www.w3.org/TR/lws10-core/#storage-description-capabilities) | MUST | INAPPLICABLE | 2 |
| [`capability-move-resource`](https://www.w3.org/TR/lws10-core/#storage-description-capabilities) | MUST | PASS | 2 |
| [`conditional-requests-supported`](https://www.w3.org/TR/lws10-core/#read-resource) | SHOULD | FAIL | 4 |
| [`conformance-server-class`](https://www.w3.org/TR/lws10-core/#conformance) | MUST | UNCOVERED | 0 |
| [`conneg-lws-json-honored`](https://www.w3.org/TR/lws10-core/#content-negotiation) | MUST | PASS | 2 |
| [`conneg-lws-profile-isomorphic`](https://www.w3.org/TR/lws10-core/#content-negotiation) | MUST | FAIL | 2 |
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
| [`containment-integrity-move`](https://www.w3.org/TR/lws10-core/#containment-integrity) | MUST | INAPPLICABLE | 1 |
| [`containment-no-cycles`](https://www.w3.org/TR/lws10-core/#containment-integrity) | MUST | UNCOVERED | 0 |
| [`containment-no-orphans`](https://www.w3.org/TR/lws10-core/#containment-integrity) | MUST | PASS | 1 |
| [`containment-rel-up-get-head`](https://www.w3.org/TR/lws10-core/#containment) | MUST | PASS | 4 |
| [`create-401-storage-link`](https://www.w3.org/TR/lws10-core/#create-resource) | SHOULD | FAIL | 1 |
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
| [`move-authorization-delete-and-create`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | INAPPLICABLE | 2 |
| [`move-container-subtree-authorization`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | UNCOVERED | 0 |
| [`move-containers-applies-to`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | INAPPLICABLE | 2 |
| [`move-containment-atomic`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | INAPPLICABLE | 3 |
| [`move-containment-integrity-cycles`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | INAPPLICABLE | 1 |
| [`move-cross-storage-may-reject`](https://www.w3.org/TR/lws10-core/#moving-resources) | MAY | UNCOVERED | 0 |
| [`move-destination-existing-container`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | PASS | 2 |
| [`move-identifier-preserved`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | INAPPLICABLE | 1 |
| [`move-new-identifier-response`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | UNCOVERED | 0 |
| [`move-notification-single-activity`](https://www.w3.org/TR/lws10-core/#moving-resources) | SHOULD | INAPPLICABLE | 1 |
| [`move-preserves-content-and-links`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | INAPPLICABLE | 1 |
| [`move-request-json-patch`](https://www.w3.org/TR/lws10-core/#moving-resources) | MUST | INAPPLICABLE | 1 |
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
| [`notification-suite-subscription-type-identifier`](https://www.w3.org/TR/lws10-core/#notification-subscription-type-identifier) | MUST | INAPPLICABLE | 1 |
| [`notifications-advertise-notificationservice`](https://www.w3.org/TR/lws10-core/#notification-discovery) | MUST | INAPPLICABLE | 1 |
| [`notificationservice-additional-properties`](https://www.w3.org/TR/lws10-core/#notification-discovery) | MAY | UNCOVERED | 0 |
| [`notificationservice-endpoint-and-subscription-types`](https://www.w3.org/TR/lws10-core/#notification-discovery) | MUST | INAPPLICABLE | 1 |
| [`operations-core-four-atomic`](https://www.w3.org/TR/lws10-core/#operations) | MUST | UNCOVERED | 0 |
| [`pagination-200-totalitems-all-pages`](https://www.w3.org/TR/lws10-core/#requesting-pages) | MUST | INAPPLICABLE | 3 |
| [`pagination-first-page-flow`](https://www.w3.org/TR/lws10-core/#requesting-pages) | MAY | INAPPLICABLE | 1 |
| [`pagination-link-first`](https://www.w3.org/TR/lws10-core/#pagination-link-relations) | MUST | INAPPLICABLE | 5 |
| [`pagination-link-last`](https://www.w3.org/TR/lws10-core/#pagination-link-relations) | MAY | INAPPLICABLE | 1 |
| [`pagination-link-next`](https://www.w3.org/TR/lws10-core/#pagination-link-relations) | MUST | INAPPLICABLE | 2 |
| [`pagination-link-prev`](https://www.w3.org/TR/lws10-core/#pagination-link-relations) | MUST | INAPPLICABLE | 2 |
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
| [`subscription-create-post-lws-json`](https://www.w3.org/TR/lws10-core/#subscriptions) | MUST | INAPPLICABLE | 1 |
| [`subscription-request-additional-fields`](https://www.w3.org/TR/lws10-core/#subscription-request) | MAY | INAPPLICABLE | 1 |
| [`subscription-request-required-fields`](https://www.w3.org/TR/lws10-core/#subscription-request) | MUST | INAPPLICABLE | 3 |
| [`subscription-request-topic`](https://www.w3.org/TR/lws10-core/#subscription-request) | MUST | INAPPLICABLE | 2 |
| [`subscription-request-type`](https://www.w3.org/TR/lws10-core/#subscription-request) | MUST | INAPPLICABLE | 3 |
| [`subscription-response-lws-json`](https://www.w3.org/TR/lws10-core/#subscription-response) | MUST | INAPPLICABLE | 1 |
| [`subscription-response-subscription-url`](https://www.w3.org/TR/lws10-core/#subscription-response) | MUST | INAPPLICABLE | 1 |
| [`subscription-response-type`](https://www.w3.org/TR/lws10-core/#subscription-response) | MUST | INAPPLICABLE | 1 |
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

