# Suppress paint under zero CSS opacity

The Wikipedia Vector menu uses a fully transparent checkbox over a visual trigger. Paired CPU pixels show Foafnaut painting the checkbox over its trigger and painting content under a zero-opacity ancestor. The patch separates zero-opacity paint exclusion from visibility and tracks it through descendants independently of their own opacity. Its selector, layout, and hit-region inputs remain intact.

Partial alpha needs group compositing. The control fixture, standard color reftests, and native pointer checks need to pass before merge. The Wikipedia icons separately need masking support.
