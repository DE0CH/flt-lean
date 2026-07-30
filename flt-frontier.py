#!/usr/bin/env python3
"""List the DIRECT sorry frontier: declarations whose own body contains `sorry`.

WHY THIS EXISTS. Three different numbers get called "the frontier" and only this
one names leaves that can be WORKED ON (CLAUDE.md):

  * DIRECT     -- the declaration's own body has `sorry`. What Lean's
                  "declaration uses 'sorry'" warning reports. THIS SCRIPT.
  * TRANSITIVE -- sorried OR consuming something sorried (ProgressCensus.lean).
                  A consumer has nothing to prove; dispatching there wastes a
                  worker, which happened to two whole clusters on 2026-07-25.
  * ERRORED    -- fails to elaborate. sorryAx-tainted, but emits no warning and
                  contains no `sorry` token, so it is invisible to BOTH of the
                  above. Only a build or per-file diagnostics finds those.

Rebuilt from scratch by at least three separate agents before being committed,
each time re-deriving the same two traps:

  1. A naive `grep sorry` counts the word inside DOCSTRINGS, and this
     development's docstrings discuss sorried leaves constantly -- that inflated
     one scan to 144 against a true 85. So comments (nested `/- -/`, `--`) and
     string literals are stripped first.
  2. Attribution must walk BACKWARDS to the nearest declaration header. Walking
     FORWARDS assigns a later declaration's sorry to an earlier proven one,
     which is exactly how `exists_hardlyRamifiedLift` was twice mislabelled open
     when it is proven.

Validated against the compiler on 2026-07-25: on all 9 modules that built, the
output matched the warning set exactly, line for line, both directions.

    python3 flt-frontier.py                # every leaf, grouped by module
    python3 flt-frontier.py --names        # bare names, one per line
    python3 flt-frontier.py Deformation    # only modules matching a substring
"""

import collections
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent
SRC = ROOT / "Fermat"

# A declaration header at column 0. `example` is deliberately absent: it binds no
# name, so a sorry inside one is not a dispatchable leaf.
HEADER = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|class)\s+"
    r"([^\s:{\[(]+)")


def strip_noncode(text):
    """Blank out comments and string literals, PRESERVING newlines so that line
    numbers survive. Handles nested `/- -/`, which Lean allows and this
    development uses."""
    out = []
    i, n = 0, len(text)
    depth = 0
    while i < n:
        two = text[i:i + 2]
        if depth:
            if two == "/-":
                depth += 1; out.append("  "); i += 2; continue
            if two == "-/":
                depth -= 1; out.append("  "); i += 2; continue
            out.append("\n" if text[i] == "\n" else " "); i += 1; continue
        if two == "/-":
            depth = 1; out.append("  "); i += 2; continue
        if two == "--":
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j; continue
        if text[i] == '"':
            out.append(" "); i += 1
            while i < n and text[i] != '"':
                if text[i] == "\\":
                    out.append(" "); i += 1
                    if i < n:
                        out.append("\n" if text[i] == "\n" else " "); i += 1
                    continue
                out.append("\n" if text[i] == "\n" else " "); i += 1
            if i < n:
                out.append(" "); i += 1
            continue
        out.append(text[i]); i += 1
    return "".join(out)


def scan(path):
    """[(name, line)] for declarations in `path` whose body contains `sorry`."""
    lines = strip_noncode(path.read_text(encoding="utf-8")).splitlines()
    # Where each declaration starts, so a sorry can be attributed backwards.
    headers = []
    for idx, line in enumerate(lines):
        m = HEADER.match(line)
        if m:
            # `theorem foo.{u} ...` -- a universe binder, not part of the name.
            # Names may legitimately contain dots (namespaces), so only a
            # TRAILING one is stripped.
            headers.append((idx, m.group(2).rstrip(".")))
    found, seen = [], set()
    for idx, line in enumerate(lines):
        if not re.search(r"\bsorry\b", line):
            continue
        # BACKWARDS: the last header at or before this line owns it.
        owner = None
        for hidx, name in headers:
            if hidx <= idx:
                owner = (hidx, name)
            else:
                break
        # Key the dedupe on the header's LINE, not its NAME.  One declaration may
        # hold several `sorry`s and must be counted once -- that is what this is
        # for -- but a NAME may legitimately be declared more than once in a file,
        # in different namespaces, and those are DIFFERENT leaves.  Keying on the
        # name silently dropped the second: `two_divisible_pic` is declared twice
        # in `ModularCurve/HyperellipticJacobian.lean` (line 4864 for level 18,
        # line 5334 for level 13) and only the first was ever reported, so the
        # scan read 351 against the compiler's 352 and nobody could be dispatched
        # at the level-13 one.  Found by diffing this scan against the release
        # build's `declaration uses 'sorry'` warning set, which is the check that
        # validates it -- run that diff, do not assume agreement.
        if owner and owner[0] not in seen:
            seen.add(owner[0])
            found.append((owner[1], owner[0] + 1))
    return found


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    names_only = "--names" in sys.argv[1:]
    as_json = "--json" in sys.argv[1:]

    by_module = collections.OrderedDict()
    for path in sorted(SRC.rglob("*.lean")):
        rel = str(path.relative_to(ROOT))
        if args and not any(a in rel for a in args):
            continue
        leaves = scan(path)
        if leaves:
            by_module[rel] = leaves

    total = sum(len(v) for v in by_module.values())
    # `--json`: the machine-readable form the Stop hook consumes (2026-07-26,
    # when the hook's census route was retired — it read oleans this checkout
    # never builds under the release model, so it failed open at every stop).
    # One object per leaf; `module` is the repo-relative source path, which is
    # what the hook prints back to the orchestrator.
    if as_json:
        import json
        print(json.dumps([{"name": n, "module": rel, "line": ln}
                          for rel, leaves in by_module.items()
                          for n, ln in leaves]))
        return 0
    if names_only:
        for leaves in by_module.values():
            for name, _ in leaves:
                print(name)
        return 0

    for rel, leaves in sorted(by_module.items(), key=lambda kv: -len(kv[1])):
        print(f"{rel}  ({len(leaves)})")
        for name, line in leaves:
            print(f"    {line:>6}  {name}")
    print(f"\nDIRECT frontier: {total} leaves across {len(by_module)} modules")
    return 0


if __name__ == "__main__":
    sys.exit(main())
