## AN EQUALIZER IS CLOSED BECAUSE IT CONTAINS AN OPEN SUBGROUP — you do not have to topologize the TARGET
(2026-08-02, `flt-lean-45`, `HardlyRamified/Deformation.lean`.)  The standard
"two continuous ring homs agreeing on a topologically generating set are equal"
argument — this file's `isUniversal_of_isWeaklyUniversal_isTraceGenerated` is
the template — needs the EQUALIZER to be closed, and gets that from *continuity
of both maps plus a Hausdorff target*.  So a leaf that wants the same argument
with the target replaced by a ring carrying no topology reads as blocked on
building `TopologicalSpace`, `IsTopologicalRing`, `IsLocalRing`, `IsAdic` and
`IsAdicComplete` instances for that ring — which is exactly what the
`DualNumberDeformation` docstring in that module declines to do, calling it
"none of them deep, all of them work, and all of it avoidable".
**It is avoidable in the proof too, and the substitute is one line of ideal
theory.**  A subgroup is closed as soon as it is OPEN, and it is open as soon as
it CONTAINS an open subgroup (`AddSubgroup.isOpen_mono`, then
`AddSubgroup.isClosed_of_isOpen`).  Here every `k[ε]`-point of `R` kills `𝔪²`
— `(f x).fst = π x` puts `f 𝔪` inside the square-zero ideal `(ε)` — so any two
of them have an equalizer containing `𝔪²`, which the adic topology makes open.
No property of the TARGET is used at all; `D.isAdic` on the SOURCE is the whole
input.
**The generalisable question, and it costs one look at the hypotheses: does
every map in sight kill some open ideal of the source?**  If so, the topological
half of a closure argument is free and the target may be any ring whatever.
Maps into an artinian/square-zero/finite-length ring almost always do, which is
the commonest case in deformation theory.
Two riders from the same proof.
* **A general uniqueness lemma with an `IsLocalRing` hypothesis can be beaten by
  a direct computation at a square-zero extension.**  The Teichmüller step of
  that argument is normally `eq_of_mem_teichmullerRoots`, which asks for a local
  ring in which `ℓ` is a nonunit.  In `k[ε]` with `char k = ℓ` the computation is
  two lines and gives MORE: `(a + bε)^(m+1) = a^(m+1) + (m+1)a^m b ε`, so
  `u ^ (ℓ ^ n) = u` with `n ≥ 1` forces `u.snd = 0` outright — a Teichmüller root
  of `k[ε]` is `inl` of its residue, not merely determined by it.  State the
  power formula at `m + 1` so no truncated subtraction appears.
* **To get SURJECTIVITY of the compatible map between two universal data, inline
  the `g ∘ g' = 𝟙` argument; do not call `exists_ringEquiv_of_isUniversal`.**
  That theorem returns a bare `RingEquiv` carrying only `ℤ_ℓ`-compatibility, so
  it cannot be composed with charpoly or reduction data — whereas what a
  transport needs is that the map *whose compatibility clauses you are using* is
  onto.  The inline version is fifteen lines (the identity is the unique
  compatible endomorphism) and is the idiom `moduleFinite_of_isUniversal` in the
  same file already uses.
**And report an equality obtained this way honestly: it closes NO leaf and opens
none.**  What it buys is that a peel `a ≤ b ≤ c` stops being a strengthening of
`a ≤ c` — the two become formally equivalent, and the "this statement is a priori
STRONGER" bullet that every such cut's faithfulness audit is obliged to carry can
be struck.  Strike it in place rather than deleting it: the equivalence is what
licenses inheriting anything between the two audits, so the next reader needs to
see why.
