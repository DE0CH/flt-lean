#!/usr/bin/env python3
"""flt-carrier-sweep.py — hunt statements whose hypotheses constrain a CARRIER
TYPE instead of the bundled object.

THE DEFECT.  For `K : CommRingCat`, the binder `[Field K]` elaborates as
`Field ↥K` — a field structure on the *carrier type*, whose ring operations are
a fresh structure field provably unrelated to `K.str`, the ring structure
`Spec K` is actually built from.  The two `CommSemiring ↥K` paths
(`CommRing.toCommSemiring` via `CommRingCat` versus
`Field.toSemifield.toCommSemiring`) are not definitionally equal.  So the
hypothesis says only "the carrier of `K` is in bijection with some field"; it
does not constrain `K`.  Statements written that way are at best strictly
harder than intended and are routinely FALSE:
`isIso_appTop_of_isProper_over_field` was refuted with
`K = CommRingCat.of (ZMod 4)`, `Z = Spec (ZMod 2)` (a four-element type carries
`𝔽₄`, so `[Field ↥K]` holds while `K.str` is the ordinary `ZMod 4`).

THE REPAIR is to state the hypothesis against the object — `(hK : IsField ↥K)`
— or to switch the binder to mathlib's idiom `(K : Type u) [Field K]` with base
`Spec (CommRingCat.of K)`.  Consumers supply `Field.toIsField _`, so downstream
statements do not change.

WHY THIS SCRIPT EXISTS.  The defect has been reintroduced repeatedly — in
`Modularity/AbelianSchemeIsogeny.lean` it was found three separate times, once
in a declaration opened *after* the file had been repaired.  A file that mixes
the two conventions is worse than one with the bug throughout: with a bundled
`K` and a local `[Field ↥K]` both in scope, instance search for `CommRing ↥K`
is ambiguous at every boundary between the styles.

WHAT IT CHECKS.  For every `.lean` file under the given root it collects the
names bound at a bundled-category type — in signatures AND in `variable`
blocks, with local rebindings at `Type*` correctly shadowing the `variable`
context — and reports every instance binder `[C … x …]` where `C` is a
structure-carrying class and `x` is such a name.  Prop mixins (`IsDomain`,
`IsReduced`, `IsLocalRing`, …) are reported separately and are BENIGN: they are
propositions over the instance found from `K.str`, not a second structure.

VALIDATION.  `--selftest` reconstructs the historical defect from git
(`b162b7c5`, `isIso_appTop_of_isProper_over_field` with `[Field K]`) and asserts
this scanner flags it.  Run it before trusting a clean report.

A STRONGER, SLOWER CHECK EXISTS and was run once by hand on 2026-07-28: a Lean
metaprogram importing all 320 project modules, walking `forallTelescope` over
every one of the 18936 project declarations and reporting each class binder
mentioning a bundled-category variable.  It found 57, all benign (55 morphism
properties on `g : X ⟶ Spec K`, one `IsLocalRing ↑R`, one `Algebra ℚ ↑A`) — the
same verdict as this script, which is what licenses using the fast one.  Redo
the Lean version only if this one's assumptions come into doubt; it costs a
full project import.

Usage:
    python3 flt-carrier-sweep.py [ROOT]      # default: ./Fermat
    python3 flt-carrier-sweep.py --selftest  # requires a git checkout
Exit status: 0 if no DATA-class hit, 1 otherwise.
"""

import os
import re
import subprocess
import sys
import tempfile

BUNDLED = (r"(?:CommRingCat|RingCat|SemiRingCat|CommSemiRingCat|AlgebraCat|CommAlgCat"
           r"|ModuleCat|FGModuleCat|GroupCat|CommGrpCat|AddCommGrpCat|MonCat|CommMonCat"
           r"|BialgebraCat|HopfAlgebraCat|CoalgebraCat|Grp|CommGrp|AddCommGrp|Ab|TopCat"
           r"|Rep|SheafOfModules|PresheafOfModules)")

# Classes that CARRY DATA already supplied by the bundled instance: adding one
# creates a second, incoherent structure on the same carrier.  These are defects.
DATA_CLASSES = set("""Field CommRing Ring Semiring CommSemiring DivisionRing Semifield
EuclideanDomain PrincipalIdealRing NormedField NormedRing NormedCommRing
AddCommGroup AddCommMonoid AddGroup AddMonoid Monoid CommMonoid Group CommGroup
Mul Add Zero One Neg Inv Sub Div Module MulAction DistribMulAction SMul
TopologicalSpace MetricSpace UniformSpace Lattice Preorder PartialOrder LinearOrder
Fintype""".split())

# Propositions over the structure that is already there.  Benign; reported for review.
PROP_MIXINS = set("""IsDomain IsReduced IsNoetherianRing Nontrivial CharZero
IsLocalRing LocalRing IsField""".split())

# `Algebra R A` between two bundled objects is genuine data but sits OVER the
# existing structures rather than replacing one, so it is not in DATA_CLASSES.

DECL_KW = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:public\s+|protected\s+|private\s+|noncomputable\s+"
    r"|partial\s+|unsafe\s+|scoped\s+|open\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|instance|inductive|example"
    r"|variable|namespace|end|section)\b")

ANY_BINDER = re.compile(
    r"[({\[]\s*([A-Za-z_][\w'₀-₉]*(?:\s+[A-Za-z_][\w'₀-₉]*)*)\s*:\s*"
    r"([^)}\]]{0,120})")
INST_BINDER = re.compile(r"\[\s*(?:[A-Za-z_][\w']*\s*:\s*)?([A-Za-z_][\w'.]*)([^\[\]]*)\]")
BUND_HEAD = re.compile(r"^\s*" + BUNDLED + r"\b")
IDENT = re.compile(r"[A-Za-z_][\w'₀-₉]*")


def strip_comments(s):
    """Drop nested `/- -/` blocks and `--` line comments, preserving line numbers.

    Mandatory: this development's docstrings discuss the defect constantly, and
    a scan that does not strip them reports its own audit notes as hits.
    """
    out, i, depth, n = [], 0, 0, len(s)
    while i < n:
        if s.startswith("/-", i):
            depth += 1
            i += 2
            out.append("  ")
        elif s.startswith("-/", i) and depth:
            depth -= 1
            i += 2
            out.append("  ")
        elif depth:
            out.append("\n" if s[i] == "\n" else " ")
            i += 1
        elif s.startswith("--", i):
            j = s.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i))
            i = j
        else:
            out.append(s[i])
            i += 1
    return "".join(out)


def units(lines):
    """Split a file into declaration-sized units, each starting at a decl keyword."""
    start, cur = 1, []
    for i, line in enumerate(lines, 1):
        if DECL_KW.match(line) and cur:
            yield start, "\n".join(cur)
            cur, start = [], i
        if not cur:
            start = i
        cur.append(line)
    if cur:
        yield start, "\n".join(cur)


def scan_file(path):
    src = strip_comments(open(path, encoding="utf-8").read())
    if not re.search(BUNDLED, src):
        return []
    hits, varctx = [], set()
    for start, text in units(src.split("\n")):
        head = text.lstrip()
        bound_bundled, bound_other = set(), set()
        for m in ANY_BINDER.finditer(text):
            target = bound_bundled if BUND_HEAD.match(m.group(2)) else bound_other
            target.update(m.group(1).split())
        # a local rebinding at a non-bundled type shadows the `variable` context
        scope = (varctx - bound_other) | bound_bundled
        if scope:
            for j, line in enumerate(text.split("\n")):
                for m in INST_BINDER.finditer(line):
                    base = m.group(1).split(".")[-1]
                    if base not in DATA_CLASSES and base not in PROP_MIXINS:
                        continue
                    bad = [t for t in IDENT.findall(m.group(2)) if t in scope]
                    if bad:
                        hits.append((path, start + j,
                                     "DATA" if base in DATA_CLASSES else "PROP",
                                     base, bad, line.strip()[:150]))
        if head.startswith("variable"):
            varctx = (varctx - bound_other) | bound_bundled
        elif head.startswith("end"):
            varctx = set()
    return hits


def sweep(root):
    hits = []
    for dirpath, _, files in os.walk(root):
        for f in sorted(files):
            if f.endswith(".lean"):
                hits.extend(scan_file(os.path.join(dirpath, f)))
    return hits


def report(hits):
    data = [h for h in hits if h[2] == "DATA"]
    for h in sorted(hits, key=lambda x: (x[2] != "DATA", x[0], x[1])):
        print(f"[{h[2]}] {h[0]}:{h[1]}: {h[3]} on {h[4]}\n      {h[5]}")
    print(f"\n{len(data)} DATA hits (defects), {len(hits) - len(data)} PROP hits (benign)")
    return 1 if data else 0


def selftest():
    """Assert the scanner flags the historical defect at b162b7c5."""
    sha, path = "b162b7c5", "Fermat/FLT/Mathlib/AlgebraicGeometry/ProperPushforward.lean"
    blob = subprocess.run(["git", "show", f"{sha}:{path}"],
                          capture_output=True, text=True, check=True).stdout
    with tempfile.TemporaryDirectory() as d:
        f = os.path.join(d, "ProperPushforward.lean")
        open(f, "w", encoding="utf-8").write(blob)
        hits = [h for h in scan_file(f) if h[2] == "DATA"]
    want = [h for h in hits if h[3] == "Field" and h[4] == ["K"]]
    if not want:
        print("SELFTEST FAILED: did not flag `[Field K]` on `{K : CommRingCat.{u}}` "
              f"in {path} at {sha}")
        return 1
    print(f"SELFTEST OK: flagged {len(want)} historical defect(s), e.g. {want[0][5]}")
    return 0


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--selftest":
        sys.exit(selftest())
    sys.exit(report(sweep(sys.argv[1] if len(sys.argv) > 1 else "Fermat")))
