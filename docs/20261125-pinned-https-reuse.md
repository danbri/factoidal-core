# 2026-11-25 Reuse pinned HTTPS connections during synchronous script startup

BBC News drove 62 sequential HTTPS GETs to one asset host. The desktop
request executor created a new tunnel and HTTP client for every request.
Reuse a client for the same approved hostname, address and port within
one synchronous answer sequence, and close the clients when it ends.
Every request still goes through the same Lean request and redirect
decisions. The host still checks the site's certificate against its name.

A local two-address TLS test received all 64 expected bodies in order
with two connections. It also checked host names and manual redirects.
The Linux browser comparison used the same native engine, host inputs,
and four fresh processes per page. The live BBC pinned-request times
were 14.08 and 13.81 seconds before the change and 3.48 and 3.32 seconds
with reuse. First paint took 40.12 and 38.33 seconds before and 28.38
and 27.99 seconds with reuse. The four runs delivered all 124 identical
wire answers and the same document pixels. The archived page also matched
exactly and exercised only one HTTPS GET.

[Local TLS fixture](https://github.com/danbri/factoidal-builds/actions/runs/45538034864)
[Browser comparison](https://github.com/danbri/factoidal-builds/actions/runs/45538979963)
