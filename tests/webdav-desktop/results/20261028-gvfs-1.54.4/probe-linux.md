# probe-linux: 2026-10-28T06:21:25Z

- origin: http://127.0.0.1:8097/
- system: Linux 6.18.44-fc-v180 x86_64; Ubuntu 24.04.5 LTS
- gio: 2.80.0

- ok    gio mount dav://127.0.0.1:8097/
- ok    root lists 8 folders: config deep hidden links many names sizes types 
- info  names/ lists 21 entries (seeded: 18 names + NAMES.txt + 2 folders = 21)
  ```
  CON.txt
  Icon
  NAMES.txt
  angle<brackets>.txt
  caf?-nfc.txt
  cafe?-nfd.txt
  case-pair
  colon:name.txt
  emoji-?.txt
  hash#.txt
  long-xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx.txt
  normalisation-pair
  nul.txt
  percent%25.txt
  pipe|.txt
  question?.txt
  quote".txt
  star*.txt
  trailing-dot.
  trailing-space 
  with space.txt
  ```
- ok    read names/with space.txt
- ok    read names/café-nfc.txt
- ok    read names/emoji-🦉.txt
- ok    read names/hash#.txt
- ok    read names/percent%25.txt
- ok    read names/question?.txt
- ok    read names/colon:name.txt
- ok    read names/CON.txt
- info  copied sizes/zero.bin in .031075235 s
- info  copied sizes/1KiB.bin in .032349358 s
- info  copied sizes/1MiB.bin in .055891448 s
- info  copied sizes/10MiB.bin in .112884799 s
- info  copied sizes/49MB.bin in .329565748 s
- info  copied sizes/51MB.bin in .386001723 s
- ok    sizes/: every file matches SHA256SUMS
- info  types/: content types
  ```
  chart.svg	515	(regular)	standard::content-type=image/svg+xml
  data.csv	92	(regular)	standard::content-type=text/csv
  data.json	61	(regular)	standard::content-type=application/json
  data.jsonld	135	(regular)	standard::content-type=application/ld+json
  data.ttl	150	(regular)	standard::content-type=text/turtle
  document.pdf	609	(regular)	standard::content-type=application/pdf
  empty.txt	0	(regular)	standard::content-type=text/plain
  hello.txt	36	(regular)	standard::content-type=text/plain
  image.png	747	(regular)	standard::content-type=image/png
  no-extension	51	(regular)	standard::content-type=application/octet-stream
  notes.md	138	(regular)	standard::content-type=text/markdown
  page.html	501	(regular)	standard::content-type=text/html
  query.rq	99	(regular)	standard::content-type=application/sparql-query
  results.srj	113	(regular)	standard::content-type=application/sparql-results+json
  ```
- info  hidden/: standard::is-hidden
  ```
  .directory	33	(regular)
  .dotfile	77	(regular)
  .dotfolder	0	(directory)
  .hidden	25	(regular)
  _underscore.txt	57	(regular)
  desktop.ini	100	(regular)
  listed-in-dot-hidden.txt	54	(regular)
  ```
- info  hidden/: .hidden list NOT honoured over dav (or attribute absent)
- ok    create config/probe-linux.txt
- ok    gio save over config/config/example-sparql/remote_sparql.txt (watch summary.md for the request pattern)
- ok    saved content reads back
- ok    rename
- ok    mkdir
- ok    move into a folder
- ok    delete a file
- ok    delete a folder
- info  links/: content types
  ```
  README.txt	237	(regular)	standard::content-type=text/plain
  dashboard.html	1606	(regular)	standard::content-type=text/html
  open-dashboard.desktop	130	(regular)	standard::content-type=application/x-desktop
  open-dashboard.url	68	(regular)	standard::content-type=application/x-mswinurl
  open-dashboard.webloc	265	(regular)	standard::content-type=application/x-webloc
  ```
- ok    many/ lists 1000 files in .377724882 s
- ok    unmount

probe-linux: 21 ok, 0 FAIL, 11 info (out of 32 lines)
