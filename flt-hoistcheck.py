#!/usr/bin/env python3
"""Can a block of a Lean file be MOVED to another position in the same file?

A leaf is sometimes open for no mathematical reason at all: everything its
proof needs is declared *below* it, and Lean's declaration order is the only
blocker.  The repair is to relocate a block — either the leaf's cluster down,
or the machinery up — and the question that decides whether that is cheap is
always the same:

    does the block use any name declared in the region it would jump over?

This answers exactly that, mechanically, in a couple of seconds, so the
decision is made on evidence instead of on how frightening a 3000-line move
looks.  Used on 2026-07-31 to hoist `X0.lean`'s `j`-section subsection nine
thousand lines and close `exists_jSection_algClosModel`: 146 declarations were
jumped over and the block used NONE of them.

    ./flt-hoistcheck.py Fermat/FLT/ModularCurve/X0.lean --block 24429 27394 --to 15851

`--block A B` is the span to move (1-indexed, inclusive) and `--to L` the line
it would be inserted BEFORE.  Both directions are handled: hoisting up reports
the declarations between `L` and `A`, moving down those between `B` and `L`.

TWO THINGS IT CANNOT SEE, and both must be eyeballed:

* ANONYMOUS instances (`instance : Foo := …`).  They have no name to scan for,
  and typeclass synthesis will silently pick them up or lose them.  They are
  listed separately in the output — read that list.
* `namespace` / `section` / `variable` / `open` scoping.  If the block would
  land inside a section it is not in now, section variables and `local
  instance`s change under it.  Straddling `namespace`/`end` pairs are reported.

Note the identifier tokeniser deliberately does NOT use a `\\w`-style regex:
Lean names contain `₀₁₂` and Unicode letters, and Python's `\\w` splits on the
subscripts, which turns `c₄_nonCMModelElevenA` into a spurious hit on `c`.
The same class of bug (a regex range swallowing `⟨⟩←▸`) has already made two
dependency scans in this project agree with each other and both be wrong.
"""

import argparse
import re
import sys

DECL = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)?'
    r'(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+)*'
    r'(theorem|lemma|def|abbrev|structure|inductive|instance|class|opaque)\s+'
    r'([^\s:({\[]+)')
ANON_INSTANCE = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|scoped\s+|local\s+)*instance\s*[:({\[]')
SCOPING = re.compile(r'^\s*(namespace|end|section)\b(.*)$')


def strip_comments(lines):
    """Drop `--` line comments and (nested) `/- -/` blocks, keeping line count."""
    out, depth = [], 0
    for ln in lines:
        res, i = [], 0
        while i < len(ln):
            if depth == 0 and ln.startswith("--", i):
                break
            if ln.startswith("/-", i):
                depth += 1
                i += 2
                continue
            if depth > 0 and ln.startswith("-/", i):
                depth -= 1
                i += 2
                continue
            if depth == 0:
                res.append(ln[i])
            i += 1
        out.append("".join(res))
    return out


def tokens(text):
    """Identifier-ish tokens.  See the module docstring on why not a regex."""
    out, cur = set(), []
    for ch in text:
        if ch.isalnum() or ch in "_.'!?" or (ord(ch) > 127 and ch.isalpha()):
            cur.append(ch)
        elif cur:
            out.add("".join(cur))
            cur = []
    if cur:
        out.add("".join(cur))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("file")
    ap.add_argument("--block", nargs=2, type=int, required=True, metavar=("A", "B"),
                    help="first and last line of the block to move (1-indexed, inclusive)")
    ap.add_argument("--to", type=int, required=True, metavar="L",
                    help="line the block would be inserted BEFORE")
    args = ap.parse_args()
    a, b = args.block
    dest = args.to
    raw = open(args.file).read().split("\n")
    clean = strip_comments(raw)

    if dest < a:
        lo, hi, direction = dest, a, "UP"
    elif dest > b:
        lo, hi, direction = b + 1, dest, "DOWN"
    else:
        sys.exit("--to lies inside --block; nothing to check")

    jumped = [(i + 1, DECL.match(clean[i]).group(2))
              for i in range(lo - 1, hi - 1) if DECL.match(clean[i])]
    anon = [i + 1 for i in range(lo - 1, hi - 1) if ANON_INSTANCE.match(clean[i])]
    blocktext = "\n".join(clean[a - 1:b])
    tk = tokens(blocktext)
    hits = [(l, n) for (l, n) in jumped if n in tk or n.split('.')[-1] in tk]

    print(f"moving {direction}: block {a}..{b} ({b - a + 1} lines) "
          f"past region {lo}..{hi - 1} ({len(jumped)} declarations)")
    print(f"HITS: {len(hits)}")
    for l, n in hits:
        print(f"  {args.file}:{l}  {n}")
    if anon:
        print(f"ANONYMOUS INSTANCES in the jumped region (invisible to the scan, "
              f"check by hand): {len(anon)}")
        for l in anon:
            print(f"  {args.file}:{l}  {raw[l - 1].strip()[:90]}")

    def scoping(lo_, hi_, label):
        depth = 0
        marks = []
        for i in range(lo_ - 1, hi_):
            m = SCOPING.match(clean[i])
            if m:
                depth += -1 if m.group(1) == "end" else 1
                marks.append((i + 1, clean[i].strip()))
        if depth != 0:
            print(f"UNBALANCED namespace/section in {label} (net {depth:+d}) — "
                  f"the move changes what scope the block is in:")
            for l, s in marks:
                print(f"  {args.file}:{l}  {s}")
        return depth

    scoping(lo, hi - 1, "the jumped region")
    scoping(a, b, "the block itself")
    print("\nA hit count of 0 with no unbalanced scoping means the move is "
          "dependency-free; it does NOT mean the build is green — run it.")


if __name__ == "__main__":
    main()
