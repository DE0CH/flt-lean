---
name: flt-scanner-name-regex-eats-universes
description: tools/merge scanners captured `foo.` from `theorem foo.{u}` — 80% of xdup's review list was that one bug, plus a latent false negative in dedup_cross
metadata:
  type: project
---

The shared declaration-name regex in `tools/merge/{xdup,blocks,frontier}.py`
has `.` in its character class (names are namespace-qualified), so on a
declaration with an explicit universe list — `theorem foo.{u}` — the match stops
at `{` and captures **`foo.`**, with a trailing dot. A Lean identifier can never
end in `.`. Fixed at source on 2026-08-02 with `rstrip('.')` in all three.

Measured on that tree (196 declarations carry explicit universes):

* `xdup.py`'s last-component review pass keys on `q.split('.')[-1]`, which is the
  EMPTY STRING for all 196 — one complete graph of false positives.
  **6008 of 7538 pairs, 80% of the list.** After the fix: 1544.
* `blocks.py` → `dedup_cross.py`: a copy written `foo.{u}` in one file and `foo`
  in the other keys as `foo.` vs `foo` and is **never paired** — a latent false
  negative, verified by planting that pair. Zero live instances that day, but
  release 29's `relPicEquiv_tensor_left` duplicate differed exactly so
  (`Scheme.{0}` vs `Scheme.{u}`).
* `frontier.py` emitted rows ending in `.`, which CLAUDE.md's queue audit had a
  documented workaround for. Now unnecessary.

**Why:** normalise at the SOURCE, not per consumer — a documented workaround is a
permanent tax on everyone downstream and silently wrong for anyone who misses it.
Confirm a fix like this is rename-only where it matters: `frontier.py`'s row count
was 382 before and after, which is what shows the release coverage invariant was
untouched.

**How to apply:** `tools/merge/test_dupscan.py` is the positive control — it plants
a plain duplicate and a universe-differing one and asserts both are found. Run it
whenever you touch a scanner. It fails on the pre-fix scanners with all three
symptoms, which is the only reason to believe it tests anything. These scans are
trusted precisely when they print `0 pair(s)`, so [[flt-rerun-a-checker-you-just-fixed]]
and the standing "a scan that reports nothing is indistinguishable from a scan that
is broken" apply with full force; release 27 shipped an unbuildable tree on that
reading. When you write a new scanner, write its positive control in the same commit.
