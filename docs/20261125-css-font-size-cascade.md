# Parse winning font sizes once

A first full cascade was the dominant native stack in the MDN display
startup task. Sites including MDN and Wikipedia specify font sizes
through custom properties, relative units, and percentages. In the
layout cascade, a winning font size was checked with the property
table to choose its inherited base. The fallback then parsed that
specified value again.

Try the existing direct parser once. If it cannot read the size, reuse
the specified value for the computed conversion against the parent's
font size. Keep the previous declaration path as the reference for the
theorem and for a declaration with another property name.

The equality proof was checked against the isolated function model
with the production control flow. The full Lean build validates the
proof with the actual style type and property table. Page replays
determine whether this saves time on the sampled workloads.
