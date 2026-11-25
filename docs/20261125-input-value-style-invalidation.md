# Avoid full CSS recascade for input value requests that leave the DOM unchanged

The page host handled every input value operation that was not a read as a full-style invalidation. Operation 169 can update the dirty value or return an attribute action to the guest. The guest carries out that action through the ordinary attribute write path.

Compare the dirty value immediately before and after the operation. Preserve pending restyles when it stays the same. Actual dirty-value changes still force full style invalidation. The browser continues to advance the DOM version for non-read requests. A Lean guard exercises the two invalidation paths.

The remaining full recascade on the captured Chinese Wikipedia page was attributed to this operation in issue #871. The effect on that capture needs a paired native replay.
