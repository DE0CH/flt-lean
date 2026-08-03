## AN ENDOMORPHISM OF `Spec K` FIXING A NONEMPTY `K`-SCHEME IS `𝟙` — and `Hom(Spec K, Spec K)` is NOT a subsingleton
(Same task; ~15 lines, and it is the step every "transport nonconstancy across an
adjunction" argument in this tree will need.)  Given `cstr : C ⟶ Spec K` and
`t : Spec K ⟶ Spec K` with `cstr ≫ t = cstr`, `t = 𝟙` **provided `C` is
nonempty** — and the hypothesis is not decoration, because `Hom(Spec K, Spec K)`
is `Hom(K, K)`, which has Frobenius in it over `𝔽_p(t)` and complex conjugation
over `ℚ(i)`.
The proof, and every name in it is at this pin:
    haveI : Nonempty ((⊤ : C.Opens) : Type) := ⟨⟨hne.some, trivial⟩⟩
    haveI : Nontrivial (Scheme.Γ.obj (Opposite.op C) : CommRingCat) :=
      (inferInstance : Nontrivial Γ(C, ⊤))          -- Scheme.component_nontrivial
    -- a ring hom out of a FIELD into a nonzero ring is injective, hence mono
    ConcreteCategory.mono_of_injective _ (RingHom.injective _)
    -- then cancel_mono on  Γ(t) ≫ Γ(cstr) = 𝟙 ≫ Γ(cstr)
    -- and AlgebraicGeometry.ext_to_Spec returns `t = 𝟙`
Three traps, each one round:
* **`Scheme.component_nontrivial` gives `Nontrivial Γ(C, ⊤)` and the goal is
  `Nontrivial (Scheme.Γ.obj (op C))`.**  They are defeq and instance search does
  not cross it; one `haveI := (inferInstance : …)` does.
* **`set β := Scheme.Γ.map cstr.op` breaks the next `rw`.**  With the `set` in
  place, `rw [← Scheme.Γ.map_comp]` failed with "did not find an occurrence" on a
  goal that displayed the pattern, and the note said the target was not
  type-correct at `instances` transparency.  Without the `set` the same rewrite
  works.  This is the standing let-binding trap; do not name a categorical
  composite you are about to rewrite under.
* **`mono_of_mono_fac` is the wrong tool for "iso ≫ f is mono ⟹ f is mono".**
  `mono_comp _ _` on `i.hom ≫ (i.inv ≫ β)` followed by `simpa` is two lines and
  works.
### A CONSUMER SCAN THAT EXCLUDES A PRECEDING `.` REPORTS A LIVE CHAIN AS DEAD
(Same task, and it nearly turned a correct result into a false "this leaf is
dead" report.)  The standard token guard for attributing a name in
comment-stripped source is
    (?<![A-Za-z0-9_.'])NAME(?![A-Za-z0-9_'])
and the `.` in the LOOKBEHIND is there for a good reason — it stops
`Foo.bar` matching `bar`.  It also stops `Fermat.myTheorem` matching
`myTheorem`, and **this tree qualifies names across module boundaries as a
matter of course**: `MazurTorsion.lean` reaches into `X1.lean` as
`Fermat.exists_cuspidalCountingDatum_twentyFive`, never unqualified, because
it is not inside `namespace Fermat`.
Chasing consumers upward from `exists_nonconstant_toAbelianScheme_of_finiteEtale_descent`
with that guard produced a nine-link chain ending in `NO CONSUMER (top)` —
i.e. the whole `Γ₁` genus chain reported as free-floating.  One `grep -rn` for
the bare name, with no guard at all, found the two qualified uses one module
away and the chain was live all along.
**So run the reachability check in two passes**: the guarded one to ATTRIBUTE a
hit to its enclosing declaration, and an UNGUARDED `grep -rn` on any name the
guarded pass calls consumerless, before writing the word "dead" anywhere.  A
consumerless verdict is the one output of that scan that changes what a worker
does, so it is the one that has to survive the cheaper, noisier check.
