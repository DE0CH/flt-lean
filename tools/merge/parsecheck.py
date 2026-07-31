#!/usr/bin/env python3
"""parsecheck.py — find every comment-delimiter wound in a Lean file IN ONE PASS.

WHY THIS EXISTS (2026-07-31, flt-lean-327).

Release 27 did not publish, and its sole blocker was `ModularCurve/X0.lean`
failing to parse.  The handover (`tools/merge/RELEASE-27-HANDOVER.md`) records
the cost precisely:

    "Fix PARSE errors first, and expect more each round.  One parse error
     truncates the file, so every later error is invisible until it is fixed —
     which is why the count fell only 248 -> 193 while nine real wounds were
     repaired."

That is the whole problem.  The compiler reports these wounds ONE AT A TIME,
and each round costs a ~35-minute elaboration of a 108k-line file, so a
multi-wound file takes a multi-hour serial grind to clear.  The wounds
themselves are not semantic and do not need a build, an olean, or an import
cone to find — they are delimiter damage, visible to a scanner in under a
second.  This finds ALL of them at once.

THE DOMINANT WOUND SHAPE, and why it is exactly detectable.

The merge-time damage is a lost `/--` opener: a docstring's prose survives, its
opening delimiter does not.  The paragraph then sits at top level as code, and
the docstring's `-/` survives as a CLOSER WITH NO OPENER.  From X0.lean at
`merger`, around line 80434:

    ... a prover should NOT attack miracle flatness. -/     <- real docstring ends
    Nothing here is specific to Jacobians or to `169`; it is stated over an
    abstract `G` so that the geometry stays in the leaf below. -/   <- ORPHAN
    theorem finite_subtype_of_fg_of_forall_isOfFinAddOrder ...

An unmatched `-/` is not merely a heuristic for this: it is not legal Lean 4 at
all, in any context, so a hit is a wound with no false-positive branch.  The
mirror image — a lost `-/`, leaving a block comment that swallows the rest of
the file — shows up as nonzero comment depth at EOF, and is reported too.

DO NOT CHASE THE COMPILER'S LINE NUMBERS PAST THE FIRST WOUND.

The handover lists eight positions still reported after round 2: 80434, 80524,
80542, 82118, 82209, 82217, 95137, 97943.  Three of those are not wounds at
all.  82118 sits INSIDE a properly delimited comment — the compiler only
reported it because, having hit the unmatched `-/` above, its idea of where
comments begin and end had already diverged from the file's.  Once the first
delimiter wound is repaired, every later number in such a log has to be
re-derived.  That is a large part of why the count fell only 248 -> 193 while
nine real wounds were fixed.  Fix everything this reports, in one pass, and
only then rebuild.

CALIBRATION, and please keep it.

Run against a GREEN tree the two hard checks must be silent, because every file
in a published release parses.  At `main` = 5162faa1 (release 26's tree, whose
snapshot is `~/.flt-release-lake/build`) this reports 0 errors over 359 files,
and at `merger` 0 over the 376 files other than the two it wounds.  If a hard
check ever fires on a file that really compiles, that is a bug in the whitelist
— add the starter, do not weaken the check.

COVERAGE, honestly.

Caught: a lost `/--` whose `-/` survived (unmatched closer); a lost `-/`
(unterminated opener); a lost `/--` whose `-/` went with it, leaving naked
prose in column 0 — including a markdown `## heading`, which is NOT a Lean `#`
command.

NOT caught: an orphaned fragment that is INDENTED.  X0.lean at 1ead8a94 had one
at 95137 — a binder list `(_hthree : ∀ …)` left behind under a finished proof
by a retyped header.  Column 0 is what makes the other shapes decidable without
a parser, and an indented `(…)` after a tactic line is too often legitimate to
flag.  So a clean run here does not promise the file parses; it promises the
delimiters are sound.  Build to be sure.

USAGE

    tools/merge/parsecheck.py <file.lean> [<file.lean> ...]
    tools/merge/parsecheck.py --all                    # every Fermat/**.lean, working tree
    tools/merge/parsecheck.py --git <rev> [<path> ...] # a revision; no path = all of Fermat/

The last form needs no checkout and no build, so THE MERGE WORKER SHOULD RUN IT
AFTER EVERY MERGE — the whole tree takes ~30 s.  A wound found there costs one
`git checkout` to fix; the same wound found at release-build time costs a
35-minute elaboration round, and hides every error below it.

Exit status is 1 if any hard wound was found, else 0, so it can gate a merge.
Advisory findings never affect exit status.
"""

from __future__ import annotations

import bisect
import re
import subprocess
import sys
from pathlib import Path

# ---------------------------------------------------------------------------
# The scanner.
#
# Lean 4 lexical facts this relies on, all of them load-bearing:
#   * `/-` opens a block comment and they NEST; `-/` closes one.  `/--`
#     (docstring) and `/-!` (module doc) are `/-` plus a marker character, so
#     they nest identically and need no special case here.
#   * `--` opens a line comment, but ONLY outside a block comment and outside a
#     string.  Inside a block comment `--` is ordinary text.
#   * String literals `"..."` (with backslash escapes) and char literals
#     `'c'` can contain `/-`, `-/` and `--` as ordinary characters, so they
#     must be skipped.  Inside a block comment, quotes are NOT special.
# ---------------------------------------------------------------------------


_TOKEN = re.compile(r'/-|-/|--|"|\'')


def _pos(text: str, idx: int, nl: list[int]) -> tuple[int, int]:
    """(line, col) of a character offset, via a precomputed newline index."""
    ln = bisect.bisect_right(nl, idx)
    start = nl[ln - 1] + 1 if ln else 0
    return ln + 1, idx - start + 1


def scan(text: str):
    """Return (unmatched_closers, unterminated_openers).

    `unmatched_closers` is a list of (line, col) where a `-/` appeared at
    comment depth 0 — a docstring opener was deleted and left its terminator.

    `unterminated_openers` is a list of (line, col) for block comments still
    open at end of file — a terminator was deleted and the comment has
    swallowed everything after it.

    Implemented by jumping between interesting tokens rather than walking
    characters: on a 4.7 MB file the difference is ~18 s versus well under a
    second, which is what makes a whole-tree sweep practical.
    """
    nl = [m.start() for m in re.finditer("\n", text)]
    unmatched: list[int] = []
    open_stack: list[int] = []  # offsets of each live `/-`

    i = 0
    n = len(text)
    while i < n:
        m = _TOKEN.search(text, i)
        if not m:
            break
        i = m.start()
        tok = m.group()

        if open_stack:
            # Inside a block comment: only `/-` and `-/` are special.
            if tok == "/-":
                open_stack.append(i)
                i += 2
            elif tok == "-/":
                open_stack.pop()
                i += 2
            else:
                i += len(tok)
            continue

        # At top level.
        if tok == "--":
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif tok == "/-":
            open_stack.append(i)
            i += 2
        elif tok == "-/":
            # THE WOUND: a closer with no opener.  Not legal Lean anywhere.
            unmatched.append(i)
            i += 2
        elif tok == '"':
            i += 1
            while i < n:
                if text[i] == "\\":
                    i += 2
                    continue
                if text[i] == '"':
                    i += 1
                    break
                i += 1
        else:  # `'`
            # Only a real char literal consumes; a bare `'` is common in Lean
            # identifiers (`h'`, `foo'`) and must not swallow to the next quote.
            if i + 3 < n and text[i + 1] == "\\":
                k = text.find("'", i + 2)
                i = k + 1 if 0 <= k <= i + 6 else i + 1
            elif i + 2 < n and text[i + 2] == "'" and text[i + 1] != "\n":
                i += 3
            else:
                i += 1

    return ([_pos(text, o, nl) for o in unmatched],
            [_pos(text, o, nl) for o in open_stack])


# ---------------------------------------------------------------------------
# Advisory check: a declaration header with no body.
#
# The handover's second named shape.  A header is suspicious when, between it
# and the next top-level declaration or docstring, there is no `:=`, no
# `where`, and no `by`.  Benign instances exist (`opaque`, `axiom`, a
# `structure` with only fields, `class` with no body), so this never sets the
# exit status.
# ---------------------------------------------------------------------------

_DECL_KWS = ("theorem", "lemma", "def", "instance", "abbrev", "example")
_MODIFIERS = (
    "private ", "protected ", "public ", "noncomputable ", "nonrec ",
    "partial ", "unsafe ", "scoped ", "local ",
)


def _strip_modifiers(s: str) -> str:
    changed = True
    while changed:
        changed = False
        for m in _MODIFIERS:
            if s.startswith(m):
                s = s[len(m):]
                changed = True
    return s


def blank_comments(text: str) -> str:
    """Replace every comment's content with spaces, preserving line structure.

    Uses the same scanner discipline so that the header check never trips on
    prose. Unmatched closers are simply skipped here.
    """
    spans: list[tuple[int, int]] = []  # half-open comment spans to blank
    i = 0
    n = len(text)
    depth = 0
    start = 0
    while i < n:
        m = _TOKEN.search(text, i)
        if not m:
            break
        i = m.start()
        tok = m.group()

        if depth > 0:
            if tok == "/-":
                depth += 1
                i += 2
            elif tok == "-/":
                depth -= 1
                i += 2
                if depth == 0:
                    spans.append((start, i))
            else:
                i += len(tok)
            continue

        if tok == "--":
            j = text.find("\n", i)
            end = n if j < 0 else j
            spans.append((i, end))
            i = end
        elif tok == "/-":
            depth = 1
            start = i
            i += 2
        elif tok == "-/":
            i += 2
        elif tok == '"':
            i += 1
            while i < n:
                if text[i] == "\\":
                    i += 2
                    continue
                if text[i] == '"':
                    i += 1
                    break
                i += 1
        else:  # `'`
            if i + 3 < n and text[i + 1] == "\\":
                k = text.find("'", i + 2)
                i = k + 1 if 0 <= k <= i + 6 else i + 1
            elif i + 2 < n and text[i + 2] == "'" and text[i + 1] != "\n":
                i += 3
            else:
                i += 1

    if depth > 0:
        spans.append((start, n))

    if not spans:
        return text
    out = []
    prev = 0
    for a, b in spans:
        out.append(text[prev:a])
        out.append(re.sub(r"[^\n]", " ", text[a:b]))
        prev = b
    out.append(text[prev:])
    return "".join(out)


# ---------------------------------------------------------------------------
# Second hard check: a stray top-level line.
#
# The delimiter check above catches a lost `/--` whose `-/` survived.  It
# CANNOT catch a lost `/--` whose `-/` went with it — then the delimiters are
# balanced and only the prose is naked.  X0.lean at `merger` has one, at 97943:
#
#     ## OPEN FAITHFULNESS QUESTION: the `∀ (A, c)` quantification
#     /-- **THE PERIOD OF AN ATKIN-LEHNER-MINUS EIGENFORM ...
#
# and the same shape covers an orphaned binder fragment left behind when a
# header is retyped (95137's `(_hthree : ∀ ...)` sitting after a finished
# proof).  Both are lines that begin in column 0 and cannot begin a Lean
# command.
#
# This is a whitelist, so it is only as good as its calibration.  It is
# calibrated against the whole of a GREEN `main`: every `Fermat/**/*.lean` in
# the published release parses, so any hit there would be a false positive.
# Keep it that way — if this ever fires on a file that really compiles, add the
# starter to the list rather than weakening the check.
# ---------------------------------------------------------------------------

_TOPLEVEL_STARTERS = {
    # declarations
    "theorem", "lemma", "def", "abbrev", "instance", "example", "structure",
    "inductive", "class", "axiom", "opaque", "mutual", "where", "deriving",
    "extends", "alias", "recall",
    # modifiers (a line may start with one and continue on the next)
    "private", "protected", "public", "noncomputable", "nonrec", "partial",
    "unsafe", "scoped", "local", "meta",
    # module structure
    "namespace", "end", "section", "open", "variable", "variables", "universe",
    "import", "module", "export", "include", "omit",
    # commands
    "set_option", "attribute", "run_cmd", "initialize", "builtin_initialize",
    "add_decl_doc", "library_note", "assert_not_exists", "suppress_compilation",
    "register_simp_attr", "declare_syntax_cat",
    # syntax / notation
    "macro", "macro_rules", "syntax", "notation", "infix", "infixl", "infixr",
    "prefix", "postfix", "elab", "elab_rules", "binder_predicate",
}

# Lines starting with one of these characters are legal continuations or
# commands in column 0 and are never flagged.
_TOPLEVEL_PUNCT = ("@[", "|", "--", "/-", ")", "]", "}", "⟩")


def stray_toplevel_lines(text: str) -> list[tuple[int, str]]:
    lines = blank_comments(text).split("\n")
    raw = text.split("\n")
    out: list[tuple[int, str]] = []
    for idx, ln in enumerate(lines):
        if not ln or ln[0].isspace():
            continue
        s = ln.rstrip()
        if not s:
            continue
        if s.startswith(_TOPLEVEL_PUNCT):
            continue
        # A `#` command is always `#` immediately followed by an identifier
        # (`#check`, `#assert_no_sorry`).  A markdown heading — `## …`, `# …` —
        # is NOT one, and that is exactly the residue of a `/--` deleted
        # together with its `-/` (X0.lean at `merger`, 97943).
        if s.startswith("#"):
            if re.match(r"#[A-Za-z_]", s):
                continue
        # Take the LEADING identifier only.  A starter is routinely followed
        # directly by punctuation — `scoped[FLT] notation …`, `infixr:25 …` —
        # and stripping punctuation out of the whole token instead yields
        # `scopedFLT` / `infixr25` and misses the whitelist.
        km = re.match(r"[A-Za-z_][A-Za-z0-9_]*", s)
        if km and km.group() in _TOPLEVEL_STARTERS:
            continue
        out.append((idx + 1, raw[idx].strip()[:110] if idx < len(raw) else s[:110]))

    # One wound is one finding.  An orphaned docstring body is a whole
    # paragraph, and reporting forty consecutive prose lines buries the next
    # wound; collapse a run (blank lines do not break it) into its first line.
    runs: list[tuple[int, str, int]] = []
    for ln, txt in out:
        if runs and ln - runs[-1][2] <= 3:
            runs[-1] = (runs[-1][0], runs[-1][1], ln)
            continue
        runs.append((ln, txt, ln))
    return [(a, (f"{t}   [{b - a + 1} lines, to {b}]" if b > a else t))
            for a, t, b in runs]


def bodyless_headers(text: str) -> list[tuple[int, str]]:
    lines = blank_comments(text).split("\n")
    starts: list[int] = []
    for idx, ln in enumerate(lines):
        if not ln or ln[0].isspace():
            continue
        s = _strip_modifiers(ln.strip())
        if any(s.startswith(k + " ") or s == k for k in _DECL_KWS):
            starts.append(idx)

    findings: list[tuple[int, str]] = []
    for pos, idx in enumerate(starts):
        end = starts[pos + 1] if pos + 1 < len(starts) else len(lines)
        chunk = "\n".join(lines[idx:end])
        if ":=" in chunk:
            continue
        if "where" in chunk.split() or " by" in chunk or chunk.rstrip().endswith("by"):
            continue
        findings.append((idx + 1, lines[idx].strip()[:100]))
    return findings


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------


def check(name: str, text: str) -> int:
    unmatched, unterminated = scan(text)
    bad = len(unmatched) + len(unterminated)
    lines = text.split("\n")

    for ln, col in unmatched:
        print(f"{name}:{ln}:{col}: ERROR unmatched `-/` "
              f"(a `/--` opener was deleted; its terminator survives)")
        lo = max(0, ln - 4)
        for k in range(lo, min(len(lines), ln)):
            print(f"    {k + 1:>7} | {lines[k][:110]}")
    for ln, col in unterminated:
        print(f"{name}:{ln}:{col}: ERROR block comment opened here is never "
              f"closed (a `-/` was deleted; it swallows the rest of the file)")

    stray = stray_toplevel_lines(text)
    bad += len(stray)
    for ln, txt in stray:
        print(f"{name}:{ln}: ERROR stray top-level line — cannot begin a Lean "
              f"command (a `/--` was deleted with its `-/`, or a header "
              f"fragment was orphaned): {txt}")

    for ln, txt in bodyless_headers(text):
        print(f"{name}:{ln}: advisory declaration header with no `:=`/`where`/`by`: {txt}")

    if bad == 0:
        print(f"{name}: delimiters OK ({len(lines)} lines)")
    return bad


def main(argv: list[str]) -> int:
    args = argv[1:]
    if not args:
        print(__doc__)
        return 0

    bad = 0
    if args[0] == "--git":
        rev = args[1]
        paths = args[2:]
        if not paths:
            # Whole revision: every Lean file under Fermat/.  This is the form
            # the merge worker wants — it needs no checkout and no build, so it
            # can be run on a merge result before committing it.
            paths = [p for p in subprocess.run(
                ["git", "ls-tree", "-r", "--name-only", rev, "Fermat/"],
                capture_output=True, text=True, check=True,
            ).stdout.split("\n") if p.endswith(".lean")]
        for path in paths:
            blob = subprocess.run(
                ["git", "show", f"{rev}:{path}"],
                capture_output=True, text=True, check=True,
            ).stdout
            bad += check(f"{rev}:{path}", blob)
    elif args[0] == "--all":
        for p in sorted(Path("Fermat").rglob("*.lean")):
            bad += check(str(p), p.read_text(encoding="utf-8", errors="replace"))
    else:
        for a in args:
            bad += check(a, Path(a).read_text(encoding="utf-8", errors="replace"))

    if bad:
        print(f"\n{bad} hard delimiter wound(s) — the file cannot parse.")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
