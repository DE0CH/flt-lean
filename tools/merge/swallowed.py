#!/usr/bin/env python3
"""Find declarations that a merge wound has hidden INSIDE a block comment.

WHY THIS EXISTS (2026-07-31, flt-lean-282, release 27's X0 blocker).

`flt-comment-balance.py` reports the NET comment depth of a file.  That number
cancels: a file with a dropped closing delimiter in one place and an orphaned
body in another scores exactly zero and reads as healthy.  `X0.lean` scored net
zero and had SIX wounds, two of which were structural -- one docstring had
swallowed `structure IsAtkinLehnerFactorwise` and ~1200 lines after it, another
had swallowed the entire 1150-line rigidification section (~15 declarations,
including `Gamma0GITPresentation.toOverSpecQ` and `bcQuotient_of_field`).

The invisibility is a property of the METRIC, not of the defect.  Comment depth
AT EACH LINE does not cancel, so:

    a declaration header sitting at comment depth > 0 is a swallowed
    declaration, always.

That is what this script reports.  Seconds, no build -- against ~35 minutes to
elaborate `X0.lean`, which additionally needs its whole import cone built first
because `lake env lean` does not rebuild imports.

    python3 tools/merge/swallowed.py [ROOT]      # default ROOT = Fermat

READING THE OUTPUT.  This project's docstrings are English prose, so a line
beginning "structure morphism is flat...", "theorem to cite." or "class in
H^1(G_Q, mu_n)." matches any keyword regex.  A naive scan gives 345 hits on
`X0.lean` against ~15 real ones, which is useless.  Two syntactic filters cut it
to nothing, and hits are bucketed rather than dropped:

*   `SWALLOWED` -- act on these.  The keyword is followed by a Lean-shaped name
    (camelCase, snake_case or dotted) and then by binders, `:`, `where` or end of
    line.  This is a declaration the compiler cannot see.
*   `[fenced]`  -- inside a ``` block in a docstring, i.e. a quoted signature.
    Not a defect; `X0.lean` has one, a retired statement in a falsity audit.
*   `[prose?]`  -- the name is a bare lowercase English word with no separator
    ("morphism", "map", "nowhere").  Almost certainly prose.  NOT dropped,
    because a genuine `theorem foo :` would look identical; skim them.

A file is printed only if it has at least one `SWALLOWED` hit, a nonzero net
depth, or a stray closer.  Exit status is always 0 -- this is a report, not a
gate, because the `[prose?]` bucket needs a human eye.
"""

import os
import re
import sys

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:private |protected |noncomputable |partial |unsafe |scoped )*"
    r"(theorem|lemma|def|structure|instance|abbrev|class|inductive)\s+"
    r"([A-Za-z_Ͱ-Ͽᴀ-ᶿ][A-Za-z0-9_.'Ͱ-Ͽ₀-ₜ]*)"
    # A real header is followed by binders, a type ascription, `where`, or end of
    # line -- never by more English.  Without this clause the scan drowns in this
    # project's prose docstrings ("structure morphism is flat...", "theorem to
    # cite.", "class in H^1(G_Q, mu_n)."): 345 hits on X0.lean instead of ~15.
    r"\s*(?:[{(\[:]|where\b|$)"
)


def depths(src):
    """Comment depth at the start of each 1-indexed line, and stray closers.

    Mirrors Lean's lexer closely enough for this purpose: `--` line comments and
    string literals shadow `/-` only OUTSIDE a block comment, and block comments
    NEST.  A closer at depth 0 is recorded and the depth clamped, so that one
    wound does not corrupt the reading of every later line.
    """
    i, n, depth, line = 0, len(src), 0, 1
    at = {1: 0}
    strays = []
    while i < n:
        c = src[i]
        if c == "\n":
            line += 1
            at[line] = depth
            i += 1
            continue
        if depth == 0:
            if c == '"':
                i += 1
                while i < n and src[i] != '"':
                    if src[i] == "\\":
                        i += 1
                    if i < n and src[i] == "\n":
                        line += 1
                        at[line] = depth
                    i += 1
                i += 1
                continue
            if src.startswith("--", i):
                while i < n and src[i] != "\n":
                    i += 1
                continue
        if src.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if src.startswith("-/", i):
            depth -= 1
            if depth < 0:
                strays.append(line)
                depth = 0
            i += 2
            continue
        i += 1
    return at, depth, strays


def fenced_lines(lines):
    """1-indexed line numbers inside a ``` fenced block."""
    inside, out = False, set()
    for ln, t in enumerate(lines, 1):
        if t.lstrip().startswith("```"):
            inside = not inside
            continue
        if inside:
            out.add(ln)
    return out


def scan(path):
    with open(path, encoding="utf-8") as f:
        src = f.read()
    at, final, strays = depths(src)
    lines = src.split("\n")
    fenced = fenced_lines(lines)
    hits = []
    for ln, t in enumerate(lines, 1):
        if at.get(ln, 0) > 0 and (m := DECL.match(t)):
            name = m.group(2)
            # A Lean name in this project is camelCase, snake_case or dotted.  A
            # bare all-lowercase word with no separator ("morphism", "map",
            # "nowhere") is English, not a declaration.  Reported as `[prose?]`
            # rather than dropped, because `theorem foo :` would look the same.
            strong = not name.endswith(".") and (
                "_" in name or "." in name or any(c.isupper() for c in name)
            )
            kind = "[fenced] " if ln in fenced else ("SWALLOWED " if strong else "[prose?] ")
            hits.append((ln, kind, t.strip()[:90]))
    return hits, final, strays


def main():
    root = sys.argv[1] if len(sys.argv) > 1 else "Fermat"
    if os.path.isfile(root):
        paths = [root]
    else:
        paths = [
            os.path.join(d, f)
            for d, _, fs in os.walk(root)
            for f in sorted(fs)
            if f.endswith(".lean")
        ]
    bad = 0
    for path in sorted(paths):
        hits, final, strays = scan(path)
        real = [h for h in hits if h[1].startswith("SWALLOWED")]
        if not real and final == 0 and not strays:
            continue
        bad += 1
        print(f"{path}  net_depth={final}  stray_closers={strays}")
        for ln, kind, t in hits:
            print(f"    {ln}: {kind}{t}")
    if bad == 0:
        print(f"{root}: no swallowed declarations, no stray closers")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
