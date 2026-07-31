#!/usr/bin/env python3
"""flt-merge-audit.py — did a merge commit actually take its branch's changes?

THE FAILURE MODE
================

Observed 2026-07-29 on this repository: `git merge flt-lean-243` printed

    error: Unable to write index

and *still produced a merge commit* whose tree was byte-identical to the
pre-merge tree — none of the branch's changes — while recording the branch as
an ancestor.  `git status` then said "All conflicts fixed but you are still
merging" and `git commit --no-edit` sealed it without complaint.  The suspected
trigger is the background `git gc` that git itself starts during a preceding
merge, so the risk is highest when several branches are merged in a row
(`git config --local gc.auto 0` in the worktree prevents it).

Why this is worse than an ordinary failed merge: **the result compiles
perfectly**.  A green `lake build` proves nothing, because the branch's payload
simply is not there.  The merged branch is now an ancestor, so every ownership
check in the fleet reports its leaves as closed; the file says otherwise and no
tool looks.

The first audit written for this only checked

    tree(merge) == tree(first parent)   and   second parent not already merged

which catches a **TOTAL** drop, where the whole payload vanished.  A **PARTIAL**
drop — the merge writes some hunks and silently loses others — has exactly the
same cause (a half-written index) and that check cannot see it at all: the tree
did change, so the merge looks fine.  This script closes that gap by asking,
per file, whether the second parent's changes actually landed.

WHAT IT CHECKS
==============

For a merge commit M with first parent P1 (the trunk), second parent P2 (the
branch) and merge base B = merge-base(P1, P2), for every path the branch
touched between B and P2:

  * **CLEAN-PATH case — the strong check.**  If the trunk did NOT touch the file
    (blob at P1 == blob at B), a correct merge must produce the branch's file
    verbatim: blob at M == blob at P2.  Anything else is either a drop or a
    hand resolution, and both deserve a look.  This is exact, not heuristic,
    and it is what catches partial drops.

      - M == P1 == B  -> DROP-TOTAL   (file reverted to trunk; nothing landed)
      - M != P2       -> DROP-PARTIAL (file changed, but not to the branch's
                                       content, with nothing to conflict with)

  * **CONTESTED-PATH case — the heuristic.**  If both sides touched the file, no
    exact answer exists: a real conflict resolution legitimately differs from
    both.  So we measure *landing rate*: of the lines the branch ADDED (B->P2),
    how many are present in M?  Of the lines it REMOVED, how many are still
    gone?  A resolution that takes the branch scores ~100%; a dropped payload
    scores ~0% while the file still differs from P1, which is invisible to any
    tree-level check.

  * **Whole-merge total no-op**, the original check, is reported too:
    tree(M) == tree(P1) while P2 was not already an ancestor of P1.

DELIBERATE DECLINES ARE NOT DEFECTS
===================================

Most zero-landing merges in this repository are *correct*: the merge worker
resolves a rival route wholly to HEAD on purpose and explains why in the commit
message ("RIVAL ROUTE ... a no-op merge", "RIVAL PROOF, superseded",
"NO-OP: its content was TRANSITIVE", "declined").  Of 15 total no-ops found in
the last 400 merges on `main`, 11 said so in the message and the remaining 3
audited (d0f901cb5 / flt-lean-360, 85dae0117 / flt-lean-156, 3e8b728bb /
flt-lean-48) turned out to say so too, in wording the keyword grep missed.

So this script does NOT decide.  It flags the merge, prints the commit subject,
and marks `[msg: decline?]` when the message contains decline vocabulary.  A
flagged merge with an explanation is a judgement call; a flagged merge with a
message that is just "Merge branch 'flt-lean-N' into merger" is the one to
investigate.  Read the message before reverting anything.

WHAT THE FIRST FULL RUN FOUND — calibration for the next reader
===============================================================

`--range main~400..main --path-filter 'Fermat/'`, 2026-07-29, 2 minutes:
**33 merges flagged, 30 LOW-LANDING, 3 DROP-TOTAL, 2 DROP-PARTIAL — and after
reading every one, ZERO genuine content losses.**  Every flag was a documented
decline, a documented re-sync, or a rival module.  So the merge worker did NOT
have a systematic problem in that window, and a flag here should be read as
"explain this", not "repair this".  Worked examples, because each one is a
distinct innocent shape you will meet again:

* `36e66b161` (flt-lean-77) DROP-TOTAL of a whole new module — a `-s ours`
  decline whose message explains it: the hoist it carried had already landed
  from a rival branch under a different home, and taking both would declare the
  same name twice.

  **This bullet used to end with a claim that was FALSE, and it manufactured a
  standing recovery task** (corrected 2026-07-30, flt-lean-187).  It said the
  `-s ours` "also discards files that had nothing to do with the rivalry" and
  that the hoist "should be redone later — a real cost, correctly paid".  It
  was not a cost and there was nothing to redo.  Branch `flt-lean-77` touched
  exactly three `.lean` files against its merge base `99681f7f`:
  `MazurTorsion.lean` (+202), `Interface.lean` (−460), and the new module
  `GaloisRepresentation/CyclotomicInertiaSurjective.lean` (+513).  That module
  contains exactly ONE declaration —
  `GaloisRepresentation.Modularity.exists_mem_localInertiaGroup_cyclotomicCharacter_toZModPow_eq`
  — which IS the disputed theorem, so the module was 77's relocation
  destination, not unrelated collateral.  The theorem is on the trunk at
  `FreyCurve/MazurTorsion.lean:7245` in the same namespace, `diff`-identical
  over all 423 proof lines except the binder placement of `{p} [Fact p.Prime]`
  and eleven `IsIntegral` → `_root_.IsIntegral` disambiguations forced by the
  enclosing namespace.  It is sorry-free and elaborates, as does the leaf it
  was hoisted for (`exists_mem_localInertiaGroup_cyclotomicCharacterModL_eq`,
  line 7695).

  Note this script's OWN per-file verdict for that path was right all along —
  `RELOCATED?  … a rename or a rival module, not a loss`.  The prose above
  contradicted the tool's output, and the prose is what got believed.  **When
  the calibration notes and a per-file verdict disagree, the verdict wins.**
  What remains of the merge message's recommendation is an optional refactor
  (move the theorem out of the 75 000-line `MazurTorsion.lean`), not a
  recovery — and see the caution against it under `decl_names`.
* `ee55a94dc` (flt-lean-15) DROP-PARTIAL at 99% landed — the merge deliberately
  substituted main's CURRENT text of a relocated block for the branch's stale
  base copy, which had been written before main grew twelve new declarations in
  it.  Taking the branch verbatim would have deleted those twelve silently.
  **A DROP-PARTIAL near 100% is usually this**, not a half-written index.
* `e220e654d` (flt-lean-349) DROP-TOTAL of a new module, message just
  `Merge branch '…'` plus git's conflict list — the shape that most deserves
  investigation.  It was still correct: the trunk already carried the same
  three theorems in `Mathlib/AlgebraicGeometry/IrreducibleNhds.lean` under
  different names, and that module's docstring records the block having been
  written three independent times.  Finding this needed a by-name search, and
  the first version of that search got it WRONG in the other direction — see
  `Git.defines` for why a substring grep is worse than useless here.
* `ab4ad3864` (flt-lean-106) DROP-TOTAL of a new module,
  `Mathlib/NumberTheory/ClassGroupNormSubgroup.lean` — the shape to study,
  because the by-name relocation search finds NOTHING for it and it is still a
  correct decline.  Its three declarations are absent from the merge tree and
  not even mentioned there.  They relocated under RENAMED spellings:
  `normClassSubgroup` -> `relNormClassSubgroup` and
  `finrank_le_index_normClassSubgroup` -> `finrank_le_index_relNormClassSubgroup`,
  both in `NumberField/UnramifiedClassFieldBound.lean` (lines 161 and 318),
  which is also where the consumer the module existed to serve,
  `finrank_le_card_classGroup_of_unramified_abelian_of_isUnramifiedAtInfinitePlaces`,
  now sits PROVEN (line 358) — exactly as the merge message says.  So **a
  silent relocation section is not evidence of loss**; it is the expected
  output whenever the rival route renamed things, which is most of the time.
  Follow the CONSUMER named in the dropped module's docstring, not the names.

  Before the comment-stripping fix this entry read "1 of its 4 sampled
  declarations ARE defined elsewhere ... may be a partial relocation".  All
  three parts of that were wrong: the file defines 3 declarations, not 4 — the
  fourth was `number`, harvested from the docstring line "class number `2`, so
  its narrow Hilbert class field is a QUADRATIC extension" — and `number` was
  also the single one that "resolved", against other files' docstrings.  The
  reassurance was 100% phantom and it concerned a name that does not exist.
* `d74aa7eaa`, `cdc865a5d` — flagged by the tree-only check as total no-ops,
  but their branches change no path at all against the merge base.  An empty
  payload cannot be dropped; this script says so and does not flag them.

USAGE
=====

    # one merge commit
    ./flt-merge-audit.py d0f901cb5

    # a range — every merge commit in it, newest first
    ./flt-merge-audit.py --range main~400..main
    ./flt-merge-audit.py --range merger~50..merger

    # only show merges with something to answer for
    ./flt-merge-audit.py --range main~400..main --only-suspect

    # restrict to the Lean sources (skips CLAUDE.md, tooling, PROGRESS.md)
    ./flt-merge-audit.py --range main~400..main --path-filter 'Fermat/'

    # machine-readable
    ./flt-merge-audit.py --range main~400..main --json

Options:
    --repo DIR          repository (default: the script's directory)
    --range REV..REV    audit every merge commit in the range
    --only-suspect      print only merges with at least one flagged file
    --path-filter STR   only consider paths containing STR
    --min-landed PCT    contested-path landing rate below this is flagged
                        (default 50)
    --json              emit JSON instead of text
    --quiet-clean       suppress the per-file OK lines

Exit status is 0 when nothing is flagged, 1 when something is.  It is a report,
not a gate: a nonzero exit means "read this", not "revert this".

REPAIRING A REAL DROP
=====================

    git reset --hard HEAD^        # if the bad merge is your tip
    git merge <branch>            # re-merge; it went clean on the observed case
    git diff --stat HEAD^1 HEAD   # MUST be non-empty

If the bad merge is buried in history, merge the branch again on top: git will
not replay it (it is already an ancestor), so use
`git merge --no-commit -X theirs <branch>` or cherry-pick the payload by path
with `git checkout <branch> -- <paths>`, and verify with this script afterwards.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from collections import Counter

DECLINE_WORDS = [
    "no-op", "noop", "no op", "declin", "supersed", "rival", "resolved wholly",
    "resolved to head", "kept main", "kept head", "revert", "duplicate",
    "already", "transitive", "wholesale", "not wanted", "abandon", "discard",
]


class Git:
    def __init__(self, repo: str):
        self.repo = repo

    def run(self, *args: str, text: bool = True) -> str:
        return subprocess.run(
            ["git", "-C", self.repo, *args],
            check=True, capture_output=True, text=text,
        ).stdout

    def try_run(self, *args: str) -> str | None:
        p = subprocess.run(
            ["git", "-C", self.repo, *args], capture_output=True, text=True
        )
        return p.stdout if p.returncode == 0 else None

    def rev(self, spec: str) -> str:
        return self.run("rev-parse", "--verify", spec).strip()

    def parents(self, commit: str) -> list[str]:
        return self.run("rev-list", "-1", "--parents", commit).split()[1:]

    def subject(self, commit: str) -> str:
        return self.run("log", "-1", "--format=%s", commit).strip()

    def message(self, commit: str) -> str:
        return self.run("log", "-1", "--format=%B", commit)

    def tree(self, commit: str) -> str:
        return self.run("rev-parse", f"{commit}^{{tree}}").strip()

    def merge_base(self, a: str, b: str) -> str | None:
        out = self.try_run("merge-base", a, b)
        return out.strip() if out else None

    def is_ancestor(self, a: str, b: str) -> bool:
        return subprocess.run(
            ["git", "-C", self.repo, "merge-base", "--is-ancestor", a, b],
            capture_output=True,
        ).returncode == 0

    def changed_paths(self, a: str, b: str) -> list[str]:
        out = self.run("diff", "--name-only", "-z", a, b)
        return [p for p in out.split("\0") if p]

    def blob_map(self, commit: str, paths: list[str]) -> dict[str, str]:
        """path -> blob sha at `commit`, for the given paths only. Missing = absent."""
        if not paths:
            return {}
        res: dict[str, str] = {}
        # chunk to stay under ARGV limits on large payloads
        for i in range(0, len(paths), 400):
            chunk = paths[i:i + 400]
            out = self.run("ls-tree", "-r", "-z", commit, "--", *chunk)
            for rec in out.split("\0"):
                if not rec:
                    continue
                meta, _, path = rec.partition("\t")
                fields = meta.split()
                if len(fields) >= 3:
                    res[path] = fields[2]
        return res

    def diff_lines(self, a: str | None, b: str | None) -> tuple[list[str], list[str]]:
        """Lines added / removed going from blob `a` to blob `b`.

        Either side may be None: a file the branch CREATED has no blob at the
        merge base, and a file it DELETED has none at its tip."""
        if a is None and b is None:
            return [], []
        if a is None:
            return self.blob_lines(b), []
        if b is None:
            return [], self.blob_lines(a)
        out = self.try_run("diff", "--no-color", "--unified=0", a, b)
        if out is None:
            return [], []
        added, removed = [], []
        for line in out.splitlines():
            if line.startswith("+++") or line.startswith("---"):
                continue
            if line.startswith("+"):
                added.append(line[1:])
            elif line.startswith("-"):
                removed.append(line[1:])
        return added, removed

    def blob_lines(self, sha: str | None) -> list[str]:
        if sha is None:
            return []
        out = self.try_run("cat-file", "blob", sha)
        return out.splitlines() if out else []

    def grep_files(self, commit: str, pattern: str, pathspec: str,
                   fixed: bool = False) -> list[str]:
        mode = "--fixed-strings" if fixed else "-E"
        out = self.try_run("grep", "-l", mode, pattern, commit, "--", pathspec)
        if not out:
            return []
        return [l.split(":", 1)[1] for l in out.splitlines() if ":" in l]

    def defines(self, commit: str, name: str, pathspec: str = "*.lean") -> list[str]:
        """Files at `commit` that DEFINE `name` — a declaration header, not a
        mention.

        A plain substring grep is worthless here and actively misleading: this
        development's docstrings discuss declarations by name constantly. On
        2026-07-29 a substring version of this check reported all three
        theorems of a dropped module as "present elsewhere" when every hit was
        a docstring sentence and none of the three was defined anywhere in the
        tree. A grep proves a spelling present, not a theorem present.

        The header pattern below narrows that a great deal but does NOT close
        it, because `git grep` cannot tell code from comment either: a prose
        line that happens to begin "theorem was proven on ..." matches the
        header pattern exactly. So the grep is used only to pick candidate
        FILES, and each candidate is then confirmed against the
        comment-stripped text. See `strip_lean_comments`.
        """
        esc = re.escape(name).replace("/", r"\/")
        pat = (r"^(private |protected |noncomputable |public |@\[[^]]*\] *)*"
               r"(theorem|lemma|def|abbrev|instance|structure|class|inductive) +"
               + esc + r"( |\(|\{|\[|:|$)")
        rx = re.compile(pat)
        confirmed = []
        for path in self.grep_files(commit, pat, pathspec):
            blob = self.try_run("show", f"{commit}:{path}")
            if blob is None:
                # unreadable blob: keep the candidate rather than silently
                # downgrading a real definition to an absence
                confirmed.append(path)
                continue
            if any(rx.match(l) for l in strip_lean_comments(blob.splitlines())):
                confirmed.append(path)
        return confirmed


def strip_lean_comments(lines: list[str]) -> list[str]:
    """Blank out Lean comments, preserving line count and column alignment.

    Every name-based scan in this repository needs this, and CLAUDE.md says so:
    the modules open with 80-line block comments whose prose routinely begins a
    sentence with "theorem ...", "def ..." or "instance ...", so a raw scan
    harvests those sentences as declaration names.

    Measured 2026-07-30 on the very module this script's calibration notes
    discuss: `CyclotomicInertiaSurjective.lean` defines exactly ONE theorem and
    the unstripped scan reported TWO. The phantom was named `was`, from the
    header sentence "theorem was proven on 2026-07-24 inside ...", and it then
    "resolved" against other files' docstrings because `Git.defines` was blind
    in the same way. Here that produced the right verdict by luck — the one
    real name is genuinely defined on the trunk — but the failure is not benign
    in general:

      * a phantom name that fails to resolve breaks `len(hits) == len(names)`
        and DOWNGRADES a correct RELOCATED? to "partial relocation — check the
        rest by name", which is exactly the shape that gets read as a loss and
        dispatched as a recovery task; and
      * `decl_names` samples only the FIRST `limit` matches, so in a
        comment-heavy module the budget is spent on prose and the file's REAL
        declarations are never checked at all.

    Handles nested block comments (`/- /- -/ -/` is legal in Lean, and this
    also covers doc comments `/-- ... -/`), line comments, and string literals
    with backslash escapes — an unguarded `/-` inside a string would otherwise
    open a phantom comment and swallow every declaration after it.
    """
    out: list[str] = []
    depth = 0
    for line in lines:
        buf: list[str] = []
        i, n = 0, len(line)
        in_str = False
        while i < n:
            if depth > 0:
                if line.startswith("-/", i):
                    depth -= 1
                    buf.append("  ")
                    i += 2
                elif line.startswith("/-", i):
                    depth += 1
                    buf.append("  ")
                    i += 2
                else:
                    buf.append(" ")
                    i += 1
                continue
            if in_str:
                ch = line[i]
                if ch == "\\" and i + 1 < n:
                    buf.append(ch)
                    buf.append(line[i + 1])
                    i += 2
                    continue
                buf.append(ch)
                if ch == '"':
                    in_str = False
                i += 1
                continue
            if line[i] == '"':
                in_str = True
                buf.append('"')
                i += 1
            elif line.startswith("/-", i):
                depth += 1
                buf.append("  ")
                i += 2
            elif line.startswith("--", i):
                buf.append(" " * (n - i))
                i = n
            else:
                buf.append(line[i])
                i += 1
        out.append("".join(buf))
    return out


DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|public\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+"
    r"([A-Za-z_][A-Za-z0-9_.'!?₀-₉]*)")


def decl_names(lines: list[str], limit: int = 12) -> list[str]:
    """Top-level Lean declaration names defined in a file, best effort.

    Used only to answer "did this file's CONTENT survive somewhere else in the
    merge tree?" — absence by NAME is not absence by CONTENT, and the commonest
    innocent reason a whole new module is dropped is that the trunk already
    carried a rival module with the same theorems under a different path.

    A RELOCATED? verdict answers "is the content still here", NOT "is the file
    where it should be". `36e66b161` is the worked example: the theorem landed
    from the rival branch into `MazurTorsion.lean`, which at 75 000 lines is one
    of the two most expensive files in the tree, and the merge message
    recommends moving it to a small upstream module. That recommendation is a
    refactor, not a recovery, and it should be priced as one — the file is under
    heavy concurrent edit, so deleting a 470-line block from it generates merge
    conflicts for a sub-1% gain in a single-threaded elaboration.
    """
    names: list[str] = []
    for line in strip_lean_comments(lines):
        m = DECL_RE.match(line)
        if m and m.group(1) not in names:
            names.append(m.group(1))
            if len(names) >= limit:
                break
    return names


def significant(line: str) -> bool:
    """Ignore whitespace-only and trivially-common lines: they carry no evidence."""
    s = line.strip()
    return len(s) > 2 and s not in ("end", "```", "-/", "/-", "--", "})", "))")


def audit_merge(g: Git, commit: str, path_filter: str | None,
                min_landed: float, check_relocated: bool = True) -> dict:
    sha = g.rev(commit)
    parents = g.parents(sha)
    result: dict = {
        "commit": sha[:9],
        "subject": g.subject(sha),
        "parents": [p[:9] for p in parents],
        "files": [],
        "notes": [],
        "suspect": False,
    }
    if len(parents) < 2:
        result["notes"].append("not a merge commit (skipped)")
        return result

    p1, p2 = parents[0], parents[1]
    msg = g.message(sha).lower()
    result["decline_worded"] = any(w in msg for w in DECLINE_WORDS)

    if g.is_ancestor(p2, p1):
        result["notes"].append(
            "second parent was ALREADY an ancestor of the first — nothing to land")
        return result

    base = g.merge_base(p1, p2)
    if base is None:
        result["notes"].append("no merge base (unrelated histories)")
        return result

    all_paths = g.changed_paths(base, p2)

    # --- whole-merge total no-op, the original check -----------------------
    # Guarded by "the branch actually had a payload": a branch whose commits net
    # to zero change against the merge base (an edit and its revert, a merge of
    # the trunk, a branch reset back) produces a merge tree identical to the
    # first parent's for an entirely innocent reason. Two of the 400 merges
    # audited on 2026-07-29 were exactly this, and the tree-only check called
    # both of them drops.
    if g.tree(sha) == g.tree(p1):
        if not all_paths:
            result["notes"].append(
                "merge tree equals the first parent's, but the second parent "
                "changes NO path relative to the merge base — an empty payload, "
                "nothing could be dropped")
        else:
            result["notes"].append(
                "TOTAL NO-OP: merge tree is byte-identical to the first parent's; "
                "the entire payload of the second parent is absent")
            result["suspect"] = True
            result["total_noop"] = True

    paths = all_paths
    if path_filter:
        paths = [p for p in paths if path_filter in p]
    if not paths:
        result["notes"].append("second parent changed no matching path")
        return result

    b_map = g.blob_map(base, paths)
    p1_map = g.blob_map(p1, paths)
    p2_map = g.blob_map(p2, paths)
    m_map = g.blob_map(sha, paths)

    for path in sorted(paths):
        b, q1, q2, m = (b_map.get(path), p1_map.get(path),
                        p2_map.get(path), m_map.get(path))
        if q2 == b:
            continue  # branch did not really change it (mode-only, or renamed away)

        entry: dict = {"path": path}

        if q1 == b:
            # ---- CLEAN PATH: exact answer available -----------------------
            entry["case"] = "clean"
            if m == q2:
                entry["verdict"] = "OK"
            elif m == q1:
                entry["verdict"] = "DROP-TOTAL"
                entry["detail"] = ("trunk never touched this file, so the merge had "
                                   "nothing to resolve — yet the file is byte-identical "
                                   "to the trunk. The branch's changes are gone.")
                entry["suspect"] = True
                if q1 is None and check_relocated:
                    # The branch CREATED this file and the merge does not have it.
                    # Before calling that a loss, ask whether its declarations
                    # landed somewhere else in the merge tree: the trunk having a
                    # rival module with the same theorems under a different path
                    # is the usual innocent explanation, and it is invisible to
                    # any path-based check.
                    names = decl_names(g.blob_lines(q2))
                    defined = {n: g.defines(sha, n) for n in names}
                    hits = {n: f for n, f in defined.items() if f}
                    entry["decls_checked"] = len(names)
                    entry["decls_defined_elsewhere"] = len(hits)
                    if names and len(hits) == len(names):
                        entry["verdict"] = "RELOCATED?"
                        entry["suspect"] = False
                        where = sorted({f for fs in hits.values() for f in fs})
                        entry["detail"] = (
                            f"the file is absent from the merge, but all {len(names)} "
                            "declarations it defines are DEFINED elsewhere in the merge "
                            "tree (" + ", ".join(where[:3]) +
                            (", …" if len(where) > 3 else "") +
                            ") — a rename or a rival module, not a loss.")
                    else:
                        if hits:
                            entry["detail"] += (
                                f" {len(hits)} of its {len(names)} sampled declarations "
                                "ARE defined elsewhere in the merge tree, so this may be "
                                "a partial relocation — check the rest by name.")
                        # Names that are only MENTIONED point at the rival module
                        # that displaced this one, which is the commonest reason a
                        # whole new module is declined. Report where to look; do
                        # NOT treat a mention as evidence the theorem survived.
                        mentioned = sorted({
                            f for n in names if not defined[n]
                            for f in g.grep_files(sha, n, "*.lean", fixed=True)})
                        if mentioned:
                            entry["mentioned_in"] = mentioned[:5]
                            entry["detail"] += (
                                " Undefined names are still MENTIONED in " +
                                ", ".join(mentioned[:3]) +
                                (", …" if len(mentioned) > 3 else "") +
                                " — read those docstrings: a rival module under "
                                "different names is the usual explanation, and a "
                                "mention is NOT evidence the theorem survived.")
            else:
                entry["verdict"] = "DROP-PARTIAL"
                entry["detail"] = ("trunk never touched this file, so a correct merge "
                                   "must reproduce the branch's file verbatim — it does "
                                   "not. Some hunks landed and some did not, or the "
                                   "merge was edited by hand.")
                entry["suspect"] = True
                added, removed = g.diff_lines(b, q2)
                entry.update(landing_stats(g, added, removed, m))
        else:
            # ---- CONTESTED PATH: heuristic landing rate --------------------
            entry["case"] = "contested"
            added, removed = g.diff_lines(b, q2)
            stats = landing_stats(g, added, removed, m)
            entry.update(stats)
            rate = stats["landed_pct"]
            if rate is None:
                entry["verdict"] = "OK"
            elif rate < min_landed:
                entry["verdict"] = "LOW-LANDING"
                entry["detail"] = (
                    f"only {rate:.0f}% of the lines this branch added are present in "
                    "the merge result. Both sides touched this file, so a hand "
                    "resolution can legitimately look like this — read the commit "
                    "message before concluding anything.")
                entry["suspect"] = True
            else:
                entry["verdict"] = "OK"

        if entry.get("suspect"):
            result["suspect"] = True
        result["files"].append(entry)

    return result


def landing_stats(g: Git, added: list[str], removed: list[str],
                  merged_blob: str | None) -> dict:
    """How much of `added` survives into the merged blob, and how much of
    `removed` stayed removed. Counted as multisets so a line added five times
    and kept once scores 20%, not 100%."""
    merged = Counter(g.blob_lines(merged_blob))
    add_sig = [l for l in added if significant(l)]
    rem_sig = [l for l in removed if significant(l)]

    landed = 0
    budget = Counter(merged)
    for line in add_sig:
        if budget[line] > 0:
            budget[line] -= 1
            landed += 1

    still_removed = sum(1 for l in rem_sig if merged[l] == 0)

    return {
        "added": len(add_sig),
        "added_landed": landed,
        "landed_pct": (100.0 * landed / len(add_sig)) if add_sig else None,
        "removed": len(rem_sig),
        "removed_still_gone": still_removed,
        "removed_pct": (100.0 * still_removed / len(rem_sig)) if rem_sig else None,
    }


def print_report(r: dict, quiet_clean: bool) -> None:
    flag = "SUSPECT" if r["suspect"] else "ok"
    print(f"=== {r['commit']}  [{flag}]  {r['subject']}")
    if r.get("decline_worded") and r["suspect"]:
        print("    [msg: decline vocabulary present — likely a deliberate resolution;"
              " read the message]")
    for note in r["notes"]:
        print(f"    * {note}")
    for e in r["files"]:
        if e["verdict"] == "OK" and quiet_clean:
            continue
        line = f"    {e['verdict']:<13} {e['path']}  ({e['case']})"
        if e.get("landed_pct") is not None:
            line += (f"  added {e['added_landed']}/{e['added']}"
                     f" = {e['landed_pct']:.0f}%")
        if e.get("removed_pct") is not None:
            line += (f"; removals kept {e['removed_still_gone']}/{e['removed']}"
                     f" = {e['removed_pct']:.0f}%")
        print(line)
        if e.get("detail"):
            print(f"        {e['detail']}")


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Report, per file, whether a merge commit actually took its "
                    "second parent's changes.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="See the module docstring for the failure mode this detects.")
    ap.add_argument("commits", nargs="*", help="merge commits to audit")
    ap.add_argument("--range", dest="rng",
                    help="audit every merge commit in REV..REV")
    ap.add_argument("--repo", default=os.path.dirname(os.path.abspath(__file__)))
    ap.add_argument("--only-suspect", action="store_true")
    ap.add_argument("--path-filter")
    ap.add_argument("--min-landed", type=float, default=50.0)
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--quiet-clean", action="store_true")
    ap.add_argument("--no-check-relocated", action="store_true",
                    help="skip the by-name search for a dropped new module's "
                         "declarations elsewhere in the merge tree")
    args = ap.parse_args()

    g = Git(args.repo)

    commits = list(args.commits)
    if args.rng:
        commits += g.run("rev-list", "--merges", args.rng).split()
    if not commits:
        ap.error("give at least one merge commit, or --range REV..REV")

    reports = [audit_merge(g, c, args.path_filter, args.min_landed,
                          not args.no_check_relocated)
               for c in commits]
    if args.only_suspect:
        reports = [r for r in reports if r["suspect"]]

    if args.json:
        json.dump(reports, sys.stdout, indent=2)
        print()
    else:
        for r in reports:
            print_report(r, args.quiet_clean)
        n = sum(1 for r in reports if r["suspect"])
        print(f"\n{len(commits)} merge commit(s) audited; {n} flagged.")
        if n:
            print("A flag is a REPORT, not a verdict: most zero-landing merges in "
                  "this repository are deliberate declines that say so in the "
                  "commit message. Read it before reverting anything.")

    return 1 if any(r["suspect"] for r in reports) else 0


if __name__ == "__main__":
    sys.exit(main())
