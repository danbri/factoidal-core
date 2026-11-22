# Vertical right-to-left grid alignment

The grid lays out physical rows in logical order and reflects the final row
coordinate for a bottom-to-top inline axis. Until now it compared each item's
physical vertical start side against the top before doing that reflection.
Alignment now compares the item's start side against the grid's actual inline
start. It also converts the line-relative left and right values before the
reflection and supplies the physical bottom auto margin first in that axis.

In the [pinned baseline](https://github.com/danbri/factoidal-builds/actions/runs/45057393069),
`grid-self-alignment.html` passed 48 of 72 cases. All 24 failures were
`offsetTop` reads with the expected 0 px and 10 px positions exchanged.
The candidate repeats all 293 baseline names at WPT
`4b26db8978f6024d3184ca483d74afbc354b35de`. The scope is in-flow grid layout.

[CSS Box Alignment §4.1](https://www.w3.org/TR/css-align-3/#positional-values)
