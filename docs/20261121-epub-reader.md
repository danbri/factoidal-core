# EPUB 3 reader

The first desktop reader handles local, reflowable, unencrypted EPUB 3 files with UTF-8 XHTML spine items. Lean reads the container, package manifest and spine, then generates passive HTML in reading order. The same pure code is available as `L4Factoidal.Epub.openBook` and `Book.readerHtml`. Foafnaut opens the `.epub` file through its ordinary local file entry point.

No member is extracted to disk. Script, author styles, remote and local filesystem resources, forms, embedded frames, and foreign active markup are omitted. Known archive-internal chapter links and bounded PNG, JPEG and GIF images are supported. This profile does not yet support author CSS, scripted books, fixed layout, media overlays or EPUB encryption. ZIP members and inflated bytes, package XML, total spine bytes and embedded image bytes are bounded.

The synthetic fixture checks that the spine controls reading order, chapter links resolve and active markup and local file references are absent. `segmentStep_root_parent` states the archive path fold refuses a parent segment at the root. This is one path property, not an end-to-end archive safety proof. The EPUB 3.3 specification is at https://www.w3.org/TR/epub-33/.
