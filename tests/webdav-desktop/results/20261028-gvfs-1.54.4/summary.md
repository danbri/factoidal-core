# WebDAV client request log summary

68 requests, 1.3 s total server time through the proxy.

## Clients (User-Agent)

| User-Agent | count |
| --- | --- |
| gvfs/1.54.4 | 68 |

## Methods

| method | count |
| --- | --- |
| PROPFIND | 44 |
| GET | 16 |
| PUT | 2 |
| MOVE | 2 |
| DELETE | 2 |
| OPTIONS | 1 |
| MKCOL | 1 |

## Method and status

| method status | count |
| --- | --- |
| PROPFIND 207 | 41 |
| GET 200 | 16 |
| PROPFIND 404 | 3 |
| MOVE 201 | 2 |
| DELETE 204 | 2 |
| OPTIONS 200 | 1 |
| PUT 201 | 1 |
| PUT 204 | 1 |
| MKCOL 201 | 1 |

## PROPFIND Depth header

| Depth | count |
| --- | --- |
| 0 | 35 |
| 1 | 9 |

## Properties asked for in PROPFIND bodies

| property (local name) | count |
| --- | --- |
| resourcetype | 44 |
| getcontentlength | 44 |
| creationdate | 22 |
| displayname | 22 |
| getcontenttype | 22 |
| getetag | 22 |
| getlastmodified | 22 |

## Files the client wrote for its own use

None matched the patterns in `summarise.mjs`.

## Requests that failed (status 400 or more, or no status)

A 404 to PROPFIND or HEAD is often a client that tests whether a name is free before it writes.

- 51 `PROPFIND /config/probe-linux.txt` -> 404
- 52 `PROPFIND /config/probe-linux.txt` -> 404
- 60 `PROPFIND /config/probe-linux-dir/probe-linux-renamed.txt` -> 404

## Writes in the config tree, in order (how editors save)

- 53 `PUT /config/probe-linux.txt` 201
- 54 `PUT /config/config/example-sparql/remote_sparql.txt` 204
- 57 `MOVE /config/probe-linux.txt -> /config/probe-linux-renamed.txt` 201
- 58 `MKCOL /config/probe-linux-dir/` 201
- 62 `MOVE /config/probe-linux-renamed.txt -> /config/probe-linux-dir/probe-linux-renamed.txt` 201
- 64 `DELETE /config/probe-linux-dir/probe-linux-renamed.txt` 204
- 66 `DELETE /config/probe-linux-dir` 204
