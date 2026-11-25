# Preserve SVG clip definitions during browser image import

The archived Wikipedia wordmark and tagline each place their paths inside a group with a rectangular clip path. The strict SVG parser already accepts their rectangle form. The browser's forgiving normalization removed the clip definition before the strict reader indexed references, so the repair pass discarded the group.

Retain the definition through normalization and use the existing strict validation and CPU/GPU clipping path. A guard checks both a pixel inside and two pixels outside the clip. The paired fixture also keeps the same archived wordmark with its clip omitted as a control.
