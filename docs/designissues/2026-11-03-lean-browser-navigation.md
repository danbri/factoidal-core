# URL navigation for the Lean renderer

The browser shell uses three separate interfaces. The native resource broker
accepts an HTTP(S) URL and returns bounded unchanged bytes plus the final
response URL. Lean accepts document bytes and emits parsed DOM, resource
requests, computed layout, paint and link targets. The host presents controls
and transports the scene to WebGPU.

This permits a local native network capability without moving HTML parsing,
CSS cascade, resource discovery, layout or link picking into the host. It
also makes the web platform limit explicit: a static web host needs CORS
access or a separate broker. The local broker does not provide a cookie jar
or implicit authentication.

History commits after the scene is ready. Navigation and GPU rendering each
carry a request number. A newer navigation aborts resource fetches and makes
older render results ineligible for display. A slow or failed request cannot
replace a newer document or append a stale history entry. Back and Forward
reload original URLs; they do not restore a saved DOM or script VM.

The original page string remains unchanged. Lean identifies stylesheet and
script node IDs and resolves their URLs from the document URL and HTML base.
Host resource records contain `{nodeId,source,url}`. Lean applies stylesheet
rules in document order and validates script DOM commands. Font requests
must use the same prepared DOM, resources and commands as the final render.

Current implementation and verification status are in the
[navigation worknote](../20261103-lean-browser-navigation.md). This is a local
MVP subset, with explicit unsupported results, not a standards score.
