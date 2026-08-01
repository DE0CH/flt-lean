#!/usr/bin/env python3
"""Calibration for the duplicate scans.  Run it whenever you touch them.

    python3 tools/merge/test_dupscan.py        # prints PASS/FAIL, exits 1 on FAIL

CLAUDE.md's standing rule for these scanners is that **a scan reporting nothing
is indistinguishable from a scan that is broken**, and the release process leans
on exactly that reading -- `xdup.py` printing `0 pair(s)` is what licenses a
release.  Release 27 shipped a tree that would not build while the qualified
pass printed zero, because a bare `end` had broken namespace attribution.

So this file plants KNOWN duplicates in a throwaway tree and asserts the scans
find them.  It is a positive control, not a search.

The second case is the one that motivated the file (2026-08-02).  The name
character class in `xdup.py`, `blocks.py` and `frontier.py` contains `.`,
because names are namespace-qualified -- so on

    theorem foo.{u} ...            -- an EXPLICIT UNIVERSE list

the match stops at `{` and captures `foo.`, WITH A TRAILING DOT.  Consequences,
all measured on the 2026-08-02 tree:

  * `xdup.py`'s last-component pass took `q.split('.')[-1]`, which is then the
    EMPTY STRING and matches every other such name.  196 declarations in the
    tree carry explicit universes, and they formed one complete graph:
    **6008 of 7538 review pairs, 80% of the list, were this single bug.**
    Fixed, the list is 1544 -- small enough to actually read.
  * `blocks.py` (hence `dedup_cross.py`) keyed `foo.{u}` as `foo.` and a plain
    `foo` as `foo`, so a rival copy written with explicit universes in one file
    and without them in the other WAS NEVER PAIRED.  No live instance in the
    tree on 2026-08-02 -- but universe-differing rival copies are precisely the
    shape these scans exist to catch (the `relPicEquiv_tensor_left` duplicate
    that release 29 removed differed in exactly that way, `Scheme.{0}` against
    `Scheme.{u}`).
  * `frontier.py` emitted rows ending in `.`, and CLAUDE.md's queue audit keys
    on the last component -- so an un-normalised row matched EVERY task.  That
    workaround is documented for consumers; it is now unnecessary, because the
    normalisation happens at source.

A Lean identifier can never end in `.`, so `rstrip('.')` is always safe.
"""
import os, shutil, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))

UP = """module
namespace Fermat
theorem cal_dup_plain (n : Nat) : n = n := rfl
theorem cal_dup_univ.{u} (a : Type u) : a = a := rfl
theorem cal_unique_up (n : Nat) : n = n := rfl
end Fermat
"""

DOWN = """module
public import Fermat.FLT.Cal.Up
namespace Fermat
theorem cal_dup_plain (n : Nat) : n = n := rfl
theorem cal_dup_univ (a : Type u) : a = a := rfl
theorem cal_unique_down (n : Nat) : n = n := rfl
end Fermat
"""


def run(*argv):
    return subprocess.run([sys.executable] + list(argv), capture_output=True,
                          text=True).stdout


def main():
    root = tempfile.mkdtemp(prefix='dupscan-cal-')
    try:
        d = os.path.join(root, 'Fermat', 'FLT', 'Cal')
        os.makedirs(d)
        up, down = os.path.join(d, 'Up.lean'), os.path.join(d, 'Down.lean')
        open(up, 'w').write(UP)
        open(down, 'w').write(DOWN)

        fails = []

        out = run(os.path.join(HERE, 'xdup.py'), root)
        for name in ('cal_dup_plain', 'cal_dup_univ'):
            if 'XDUP Fermat.%s ' % name not in out:
                fails.append('xdup.py MISSED the duplicate %r' % name)
        if 'cal_unique_up' in out or 'cal_unique_down' in out:
            fails.append('xdup.py reported a NON-duplicate')

        out = run(os.path.join(HERE, 'dedup_cross.py'), down, up)
        try:
            n = int(out.split('duplicated names present in both:')[1].split()[0])
        except Exception:
            n = -1
        if n != 2:
            fails.append('dedup_cross.py paired %s names, expected 2 '
                         '(the universe-only pair is the regression)' % n)

        # No scanned name may end in '.' -- that is the bug this file guards.
        sys.path.insert(0, HERE)
        import blocks
        for p in (up, down):
            for (_, q, _, _, _) in blocks.blocks(p)[1]:
                if q and q.endswith('.'):
                    fails.append('blocks.py emitted a trailing-dot name %r' % q)

        for f in fails:
            print('FAIL: ' + f)
        print('PASS' if not fails else 'FAILED (%d)' % len(fails))
        return 1 if fails else 0
    finally:
        shutil.rmtree(root, ignore_errors=True)


if __name__ == '__main__':
    sys.exit(main())
