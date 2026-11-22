# Unicode wrap opportunities in inline layout

The 22 November full WPT run on a512ab918913 showed 407 failures in the
css3-text-line-break-baspglwj family. The tests measure whether text wraps
after Unicode separators and historic punctuation. The inline tokenizer had
restricted the existing UAX 14 algorithm to boundaries next to a hand-written
CJK character range. This excluded zero-width space, em space and break-after
punctuation from otherwise breakable tokens.

Use the engine's existing strict, normal or loose Unicode tailoring on text
tokens. Preserve code-point offsets for geometry and selection. Keep a fast
path for ASCII letters and digits. Space collapsing, explicit breaks and
decisions to disable wrapping stay in the existing inline layout code. The
preserved white-space modes still share a separate limitation in that code.

Lean 4.33.1 compiled the exact Unicode dependency sources and the extracted
candidate function with warnings treated as errors. The existing Arabic,
CJK and kana guards pass, along with guards for hyphen, zero-width space,
em space, word joiner and no-break space. These guards check tokenization.
Full engine compilation and WPT outcomes are tracked in the PR.
