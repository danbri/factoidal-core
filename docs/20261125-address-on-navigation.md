# Address and tab title on navigation

The [published Linux FrogFind run](https://github.com/danbri/factoidal-builds/actions/runs/45657707584)
proved that Enter and a click loaded and rendered live search results. In both screenshots
the address bar still displayed the homepage. The frame used the old address field while
compiling the new document. The host changed the field after presentation, with no further
frame required for a settled page.

Build the chrome for the same document as the frame. Use its address and tab title when
committing a page. Preserve the address field during an active edit. Strengthen the
existing daily-use search tests to check the address used for the presented frame.
