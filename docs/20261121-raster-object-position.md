# Raster image object position

Foafnaut used the centre of the content box whenever it painted an image. Resolve the CSS position against the space left by `object-fit`, which can be negative for `cover`, and clip the result to the existing content box. This keeps the selected part of the image in view in cropped cards and thumbnails.

The Lean statements `Rendering.Layout.pictureOffset_default` and `Rendering.Layout.pictureOffset_percent` cover the default centring formula and the explicit percentage formula. The layout guards exercise author positions through the declaration reader and paint output. The pinned WPT PNG reference pages are `css/css-images/object-position-png-001i.html` and `object-position-png-002i.html`. Their pixel comparison is a separate check of the rendering path.

On November 22 the change was reconciled with main after raster CSS backgrounds landed. That enables the pinned reference pages to use the same image pipeline as ordinary pages.
