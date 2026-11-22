# Select the document root for viewport layout

Foafnaut keeps the top document and script-visible iframe documents in one DOM
arena. A layout read must select the document's root and viewport while keeping
the existing node numbers, since the script side already wraps those numbers.

The shared styled renderer now accepts a document node. It starts the
percentage-edge pass, canvas-background lookup and block layout at that node.
Render output continues to identify elements by their arena node numbers.
The default selects the top-level document at node zero.

The regression guard uses two documents in one arena and checks that distinct
viewport widths produce only the corresponding document's element box and
resolve its percentage margin against the selected viewport. The existing
link-region theorem is generalised to the selected document. The guard
also checks rejection of an element as the layout root. The browser still
needs the document-aware hit-query path tracked in issue #803.
