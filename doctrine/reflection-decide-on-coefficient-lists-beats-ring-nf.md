## Reflection (`decide` on coefficient lists) beats `ring_nf` 400× on olean size — and `decide +kernel` grows with file position

(2026-08-04, flt-lean-155, measured on shadowcat while closing the two `p = 37`
Mazur rows at `ℓ = 1259`.)

**The problem class.** A generated certificate module proves hundreds of small
`F_q[X]` identities (`a·b = f·Q + c`, Bézout combinations, staged products).
The established shape — `simp only [defs]; reduce_mod_char; ring_nf;
reduce_mod_char` per identity — costs ~1.5–2.7 s per step AND stores a ~2.4 MB
proof term per step: the `p = 17` factor modules are **794 MB of
`.olean.private` each**.  At `p = 37` scale (36 modules × 594 steps) that is
~50 GB of oleans — more than the release snapshot's whole volume had free.
Olean size, not wall clock, was the binding constraint.

**The fix that worked.** Represent polynomials as `List ℕ` of mod-`q`-reduced
coefficients; define `nadd/nscale/nmul/npow/nneg/ntrim` reducing mod `q` at
every entry; bridge once with `npoly : List ℕ → (ZMod q)[X]` and ~8
homomorphism lemmas (~150 lines, `Fermat/FLT/EllipticCurve/MazurNonCMReflect.lean`).
Every computational fact becomes ONE `decide` on a list identity, glued by a
per-shape discharge lemma (`dvd_sq_of_lists`, `isCoprime_of_lists`, …).
Measured: **1.9 MB `.olean.private` per 594-step factor module (410× smaller),
~200 s wall, 2.9 GB RSS** — and `lake build` of all 36 modules runs them
concurrently.

Key design points, each of which was load-bearing:

- **Lists of `ℕ`, not `ZMod q`/`Fin`**: the kernel evaluates plain `Nat`
  literal arithmetic on its GMP fast path; `OfNat`/`Fin` wrappers are what it
  is slow at.  Reduce mod `q` inside every op so emitted literals stay small
  and both sides of any identity are canonical.
- **A Python mirror of the Lean ops, exact to the padding**: the generator
  computes every `decide` target with structurally identical functions and
  asserts it before emission.  Fixed-width padding (accumulators and
  remainders always `deg f` long, cofactors `deg f − 1`) is what makes the
  early chain steps (short polynomials) literally true as list equations —
  trimmed lists break on trailing zeros.
- **Algebraic glue is shape-independent**: after `rw`-ing atoms to `npoly`
  form, `simp only [← npoly_npow, ← npoly_nmul, sub_eq_add_neg, ← npoly_nneg,
  ← npoly_nadd]` folds ANY product/power/difference expression into one
  `npoly <closed list expr>`, and `exact congrArg (npoly q) (by decide)`
  finishes.  No fighting `norm_num`'s output shape; the degree-`684`
  `preΨ' 37 = C 37 · D · H` identity went through this way in one ~6 s decide.
- **Big one-shot decides are fine**: the 18-fold degree-666 product
  (`~2·10⁵` mult-mods) is ~50 s decide + ~50 s kernel re-check.  Kernel
  throughput ≈ 4k list mult-mods/s.

**THE TRAP: `decide +kernel` type-check time GROWS ~0.31 s PER DECLARATION
with file position.** Measured twice on 24-declaration probes, once chained
and once with independent seeds and once in reversed order — the growth
follows file position, not data or dependency structure.  Over a 578-step
chain that is quadratic death (hours), while plain `decide` is FLAT
(1.4–1.8 s + 0.43–0.66 s kernel per step under fleet load, ~0.34 s/step total
in a quiet `lake build`).  Use plain `decide` in generated chain modules;
never `+kernel` there.

**Retro-fit opportunity (open as of 2026-08-04):** the eight `p = 11`/`p = 17`
factor modules under `MazurNonCMFrobenius/` still carry the `ring_nf` shape —
~6.4 GB of `.olean.private` and ~2 h of release-critical-path elaboration that
the reflection shape would collapse to ~15 MB and minutes.  `gen_thirtyseven.py`
contains everything needed; a successor can generalise it over `(q, m, tag)`.
