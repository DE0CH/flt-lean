/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Fermat.FLT.GaloisRepresentation.Chebotarev
public import Fermat.FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
public import Fermat.FLT.KnownIn1980s.PGL2.Basic

/-!
# The global norm-index inequality of class field theory

This module holds ONE statement: the norm-index inequality

  `[I_F(mm) : P⁺_{F,mm} · N_{M/F} I_M(mm)] ≥ [M : F]`

for the finite cyclic extension `M/F` cut out by a character `χ` of `Γ F`, written
in the divisor (`Finsupp`) language of
`Fermat/FLT/GaloisRepresentation/HardlyRamified/ModThree.lean`'s ray-class cluster.

## Why it is a module of its own

It was hoisted out of `ModThree.lean` on 2026-07-31. That file is ~60 000 lines and
elaborates single-threaded, so an edit/verify cycle there costs of the order of an hour.
The inequality is not a leaf that anybody will close in one sitting: the audits collected
below (and in `ModThree.lean`, at the docstring of
`exists_natCard_charDivisorImage_le_ray_class`) establish that it is a THEORY-BUILDING
project — Herbrand quotients and the local norm index on the algebraic side, or the
narrow ray class group with its characters, their `L`-series and the non-vanishing
`L(1, ψ) ≠ 0` on the analytic side — and NONE of that machinery exists in the pin, in
`~/cs/FLT`, or here. Whoever builds it will iterate hundreds of times. Doing that against
this module, whose import cone is `Chebotarev` and whose own elaboration is a few
declarations, costs seconds per cycle rather than an hour.

Nothing here is `ModThree`-specific. The module is deliberately placed so that it can be
imported by anything downstream of `Chebotarev`; see the CROSS-REFERENCE section in
`ModThree.lean`, which records that `Modularity/Interface.lean`'s
`finrank_le_card_classGroup_of_unramified_abelian` and
`NumberField/UnramifiedClassFieldExistence.lean`'s
`exists_unramifiedAbelian_card_classGroup_le_finrank` are the SAME theorem at modulus `1`,
and that all three should end up citing one statement.
-/

@[expose] public section

namespace GaloisRepresentation.IsHardlyRamified

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

universe u

/-- **ARTIN RECIPROCITY AT A PRIME-POWER MODULUS, THE `ray ⊆ ker` CONTAINMENT ONLY**
(SORRY LEAF, cut 2026-07-31 (`flt-lean-167`) out of
`exists_natCard_charDivisorImage_le_normIndex_primePow_ray_class` below, which is now
PROVEN over it in eighteen lines of index bookkeeping).

Unwound: for the finite cyclic `M/F` cut out by `χ`, there is a modulus `mm₀ ^ (t+1)`
such that every totally positive `δ ≡ 1 (mod mm₀ ^ (t+1))` has trivial Artin symbol,
`c ((δ)) = 1`. Classically: `mm₀ ^ (t+1)` is admissible for `M/F`, and the narrow ray
group `P⁺_{F, mm₀^(t+1)}` lies in the kernel of the Artin map. Childress ch. 5
(pp. 113–114 for the base case, pp. 121–123 for the descent); Neukirch VI (7.3);
Janusz V; Lang *ANT* X.

## Why the leaf below was recut onto this, and what the recut costs

The parent's own docstring (retained verbatim below) recorded, correctly, that the
containment route needs `P ≤ φ.ker`, that this is Artin reciprocity, and that
reciprocity is mathematically deeper than the inequality it proves — so that trading
the inequality for reciprocity would be a REGRESSION unless the new citation also
discharged `NumberField.artinMap_toPrincipalIdeal` in
`Fermat/FLT/NumberField/ArtinSymbol.lean`. **That unification is NOT available, and
this file should stop recommending it; see the section after next.** What makes the
recut worth making anyway is a different fact, which the parent's route inventory
missed:

**`ModThree.lean` ALREADY CONTAINS A RAY-CLASS ARTIN RECIPROCITY DEVELOPMENT, in this
exact formalism, following Childress, and the base case of THIS leaf is PROVEN in it.**
The inventory looked for reciprocity under `Fermat/FLT/NumberField/` and found only the
modulus-`1`, `artinMap`-language cluster; the ray-class one is 13 000 lines away in
`ModThree.lean` under names beginning `artin…_ray_class`, and none of them contains the
word "reciprocity". Concretely, and all checked against `main` at `fe5131ca`:

* `artinSymbol_span_eq_one_of_cyclotomic_ray_class` (`ModThree.lean:50045`) — **PROVEN**.
  This IS the statement below, for `F` replaced by any number field and the modulus
  replaced by `(m)` with `χ` CYCLOTOMIC of level `m`. Childress pp. 113–114.
* `artinDivisorSymbol_span_eq_one_of_cyclotomic_ray_class` (`:58238`) — **PROVEN**, the
  same thing transported to the divisor group.
* `exists_artinAuxiliaryNumberField_ray_class` (`:54540`) — **PROVEN**: Artin's auxiliary
  field `E` realised as a number field in `Type u`, with `M ∩ E = F`, `M ⊆ E(ζ_m)`,
  `globalFrob p ∈ H`, and the base-change clause that puts `χ ∘ ι` in the scope of the
  cyclotomic case at `E`.
* `exists_relNormDivisorHom_ray_class` (`:62157`) — **PROVEN**: the relative-norm
  homomorphism on divisors with its compatibility `c (N_{E/F} 𝔄) = c' 𝔄`.

So the descent apparatus that carries the cyclotomic base case down to a general `F` and
a general modulus is BUILT and green; what is missing is one assembly, in the same shape
as `exists_artinNormSubgroups_ramified_ray_class` (`:63121`, proven glue) but for the
opposite containment. That is why the recut is a decomposition rather than a trade: this
leaf is strictly weaker than "ray class Artin reciprocity" as the parent's audit priced
it, being only one of the two containments, with no Artin map, no surjectivity, no
`Subgroup`, no `relIndex` and no divisor group in its statement.

**AND THE TWO DIRECTIONS DO NOT COLLIDE — checked, because the obvious fear is
circularity.** `exists_artinNormSubgroups_ramified_ray_class` proves
`φ.ker ⊓ Im ≤ P ⊔ N` (the `ker ⊆ ray · norms` direction, which yields `h ≤ n`) and it
takes `hidx₂ : A.relIndex Im ≤ (P ⊔ N).relIndex Im` — *the parent leaf's own conclusion,
`n ≤ h`* — as a HYPOTHESIS. So the in-tree reciprocity development consumes the
inequality in the `ker ⊆ ray·norms` direction and cannot be used to prove it, while the
`ray ⊆ ker` direction asked for here is not used by it anywhere. Anyone tempted to close
this leaf by citing `exists_artinNormSubgroups_ramified_ray_class` should read its
`hidx₂` binder first.

## The unification with `ArtinSymbol.lean` is NOT available (verdict, 2026-07-31)

The parent recommended stating ray class reciprocity ONCE, upstream of both this module
and `Fermat/FLT/NumberField/ArtinSymbol.lean`, and proving both
`artinMap_toPrincipalIdeal` and this leaf over it — `2` leaves for `1`. It was attempted
and abandoned, for a reason that is structural rather than a matter of effort: **the two
modules are written in two different formalisms and there is no dictionary between them
in this tree.** `ArtinSymbol.lean` is deliberately mathlib-only (`frobAt`,
`Algebra.IsUnramifiedAt`, `IsUnramifiedAtInfinitePlaces`, an abstract `L` with
`[IsGalois K L]`); everything here is absolute-Galois (`Γ F`, `globalFrob`,
`localInertiaGroup`, characters of `Γ F`). Deriving `artinMap_toPrincipalIdeal` from a
`Γ F`-character reciprocity needs FOUR bridges, of which exactly one exists:

1. `restrictNormalHom L (globalFrob v) = frobAtBelow K L v` — **available**, from
   `Chebotarev.lean`'s `exists_isArithFrobAt_restrictNormalHom_globalFrob` (`:12351`,
   PROVEN, pointwise at every `v`, no unramifiedness needed) together with
   `ArtinSymbol.lean`'s `frobAtBelow_eq_frobAt` and `eq_of_isUnramifiedAt`.
2. *Finite inertia*: `(∀ Q, Algebra.IsUnramifiedAt (𝓞 K) Q) → the image of
   `localInertiaGroup w` in `Gal(L/K)` is trivial`. **Absent.** This is the local–global
   comparison of inertia; nothing in `Fermat/` relates `localInertiaGroup` to
   `Algebra.IsUnramifiedAt`.
3. *Archimedean*: `IsUnramifiedAtInfinitePlaces K L → χ` kills the decomposition group at
   each real place. **Absent.**
4. Transport of an abstract Galois `L/K` to an `IntermediateField K (AlgebraicClosure K)`,
   which is what (1) is stated for. **Absent.**

Bridges 2 and 3 are theorems of the same order as the leaves they would serve, so the
unification is `2` leaves for `1 + 2` — a regression, and a several-thousand-line one.
It would also drag `Chebotarev.lean`'s 13 479-line cone into `ArtinSymbol.lean`, whose
own docstring says it "deliberately uses NO vocabulary from either" consumer. **Do not
re-attempt it as stated.** If the two clusters are ever to share a statement, the cheap
order is to build bridge 2 FIRST as a leaf in its own right — it is wanted by
`hmm₀ram`-style hypotheses all over `ModThree.lean` — and only then ask about a shared
reciprocity.

## FALSITY AUDIT (run from scratch, 2026-07-31). VERDICT: TRUE AS STATED

* *Monotone in `t`, the right way.* Raising `t` SHRINKS `mm₀ ^ (t+1)`, hence shrinks the
  set of admissible `δ`, hence WEAKENS the conclusion. So `∃ t` is satisfiable as soon as
  one admissible `t` exists and every larger `t` works too — the same check that the
  parent's audit identified as load-bearing there, and it runs the same way here. (Had it
  run the other way, `∃ t` would be dischargeable at a degenerate `t` and useless at every
  admissible one.)
* *Identification with the classical theorem.* `χ` has open kernel (`hVopen`, `hVker`) and
  exponent dividing `ℓ ^ k` (`hord`), so it cuts out a finite abelian — in fact cyclic, see
  the parent's docstring — extension `M/F` of `ℓ`-power degree, and `c` is its Artin symbol
  on ideals (`hcmul`, `hcfrob`). The conductor `𝔣(M/F)` is supported at the primes ramified
  in `M`, which `hmm₀ram` places inside `supp mm₀`; so for `t` large `mm₀ ^ (t+1)` is
  divisible by `𝔣(M/F)` and is ADMISSIBLE, and Artin reciprocity says the ray group mod an
  admissible modulus is in the kernel. Passing from the wide ray group to the narrow one
  only shrinks the hypothesis set, so total positivity is free here.
* *`hmm₀ram` is load-bearing, with an explicit refutation.* Drop it and take `F = ℚ`, `χ`
  the quadratic character cutting out `ℚ(i)` (so `ℓ = 2`, `k = 1`), and `mm₀ = (3)` — which
  misses the ramified prime `2`. For any `t`, Dirichlet gives a prime `p ≡ 1 (mod 3^{t+1})`
  with `p ≡ 3 (mod 4)`; then `δ = p` is totally positive and `≡ 1 (mod 3^{t+1})`, while
  `c ((p)) = χ (Frob_p) = (−1/p) = −1 ≠ 1`. So no `t` works and the leaf is FALSE without
  `hmm₀ram`. This is the same shape as the second refutation recorded on
  `ModThree.lean`'s `exists_artinDivisorNormIndex_le_ray_class`.
* *Total positivity is load-bearing*, for the reason recorded at the base case
  (`artinSymbol_span_eq_one_of_cyclotomic_ray_class`, step 4): without it `Algebra.norm ℤ δ`
  may be negative, `absNorm ((δ))` picks up the absolute value, and the norm is `≡ −1` rather
  than `≡ 1` modulo the level, on which the character need not be trivial. Verified
  numerically there at `F = ℚ(√3)`.
* *The `mm₀ = ⊤` branch is real and survives.* `hmm₀ram` is then vacuous only if `χ` is
  unramified at every finite place; `⊤ ^ (t+1) = ⊤` and `δ - 1 ∈ ⊤` always, so the claim
  becomes "every totally positive principal ideal has trivial Artin symbol", i.e.
  reciprocity for the NARROW Hilbert class field. True and nontrivial. **Any proof that
  begins "let `v` be a prime dividing the modulus" is wrong on this branch.**
* *Nothing is pinned by junk.* `c` is universally quantified OUTSIDE the leaf and pinned on
  the height-one primes by `hcfrob` and multiplicatively by `hcmul`, hence determined on
  every nonzero ideal by unique factorisation in `𝓞 F`; the conclusion is a genuine
  constraint on it and not dischargeable by a degenerate witness.

**The check that would refute it**: a number field `F`, a character `χ` as above, an `mm₀`
divisible by every prime at which `χ` is ramified, and for EVERY `t` a nonzero totally
positive `δ ≡ 1 (mod mm₀ ^ (t+1))` with `c ((δ)) ≠ 1`. -/
theorem exists_artinSymbol_span_eq_one_narrowRay_ray_class
    (F : Type u) [Field F] [NumberField F]
    (χ : Γ F → Dickson.K 3)
    (hmul : ∀ a b : Γ F, χ (a * b) = χ a * χ b)
    (V : Subgroup (Γ F)) (hVopen : IsOpen (V : Set (Γ F)))
    (hVker : ∀ a ∈ V, χ a = 1)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (k : ℕ)
    (hord : ∀ a : Γ F, χ a ^ (ℓ ^ k) = 1)
    (c : Ideal (NumberField.RingOfIntegers F) → Dickson.K 3)
    (hcmul : ∀ I J : Ideal (NumberField.RingOfIntegers F), I ≠ ⊥ → J ≠ ⊥ →
      c (I * J) = c I * c J)
    (hcfrob : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      c v.asIdeal = χ (globalFrob v))
    (mm₀ : Ideal (NumberField.RingOfIntegers F)) (hmm₀ : mm₀ ≠ ⊥)
    (hmm₀ram : ∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      (∃ a : Γ F, ∃ σ ∈ localInertiaGroup w,
        χ (a * Field.absoluteGaloisGroup.map
          (algebraMap F (IsDedekindDomain.HeightOneSpectrum.adicCompletion F w)) σ * a⁻¹)
          ≠ 1) →
      w.asIdeal ∣ mm₀) :
    ∃ t : ℕ, ∀ δ : NumberField.RingOfIntegers F, δ ≠ 0 →
      (∀ ψ : F →+* ℝ, 0 < ψ (algebraMap (NumberField.RingOfIntegers F) F δ)) →
      δ - 1 ∈ mm₀ ^ (t + 1) →
      c (Ideal.span {δ}) = 1 :=
  sorry

/-- **THE GLOBAL NORM-INDEX INEQUALITY, AT A PRIME-POWER MODULUS AND WITH THE TRIVIAL
CASE ALREADY DISCHARGED** (**PROVEN 2026-07-31** (`flt-lean-167`) as containment glue over
`exists_artinSymbol_span_eq_one_narrowRay_ray_class` just above; created 2026-07-31 by
hoisting the irreducible
core of `ModThree.lean`'s `exists_natCard_charDivisorImage_le_ray_class` into this module;
that theorem is now PROVEN as glue over
`exists_natCard_charDivisorImage_le_normIndex_ray_class` just below, which is in turn glue
over this one).

**WHICH CLASSICAL THEOREM THIS IS.** Every `v ∤ mm` is unramified for `χ` (`hmm₀ram` puts
the ramified primes into `mm₀`, and `mm = mm₀ ^ (t+1)` has the same prime support), so for
such a `v` the number `orderOf (χ (globalFrob v))` IS the residue degree `f_v` of `v` in
the cyclic extension `M/F` cut out by `ker χ`. Hence

* `N = ⟨ v ^ f_v : v ∤ mm ⟩ = N_{M/F}(divisors of M supported away from mm)`,
* `P` is the totally-positive ray group mod `mm`,
* `Nat.card (Im.map φ) = [M : F]` (`φ` is the Frobenius character on divisors),

and the conclusion is verbatim `[I_mm : P_mm · N_{M/F} I_mm(M)] ≥ [M : F]`
(Childress §5, Janusz IV, Neukirch VI §7 in the idele language). It is proved either by
Chevalley's ambiguous class number formula / Herbrand quotients (the algebraic route, which
needs the CYCLICITY that is handed over here as a hypothesis) or analytically from
`L(1, ψ) ≠ 0` for ray class characters — but see the correction near the end of this
docstring: **the analytic route proves the OPPOSITE inequality.**

**THE ROUTE THAT WAS TAKEN, 2026-07-31 (`flt-lean-167`): the containment, over the
`ray ⊆ ker` half of ray-class Artin reciprocity.** Everything below this paragraph is the
docstring as it stood while this was a `sorry`, and it is kept because its audits are what
the new leaf inherits. One verdict in it is now superseded and is corrected here rather
than deleted, because the reasoning that produced it is still worth reading:

> **It is NOT obtainable from the Artin map**: the containment route `P ⊔ N ≤ φ.ker` needs
> `P ≤ φ.ker`, which is Artin reciprocity, and reciprocity is strictly harder than the
> inequality it would prove here. Three independent audits in `ModThree.lean` reached that
> verdict; it stands.

Both sentences are true of *full* ray-class Artin reciprocity, and the containment route is
taken anyway, because what the route consumes is strictly less than that and is already
half-built in this tree. It consumes only `P ≤ φ.ker` — one of the two containments, with
no Artin map, no surjectivity and no reverse inclusion — and that is now the named leaf
`exists_artinSymbol_span_eq_one_narrowRay_ray_class` above, whose CYCLOTOMIC BASE CASE is
PROVEN in `ModThree.lean` (`artinSymbol_span_eq_one_of_cyclotomic_ray_class`, `:50045`,
and its divisor form at `:58238`) and whose descent apparatus is PROVEN there too
(`exists_artinAuxiliaryNumberField_ray_class`, `exists_relNormDivisorHom_ray_class`). See
that leaf's docstring for the full inventory, for the check that this does NOT create a
cycle with `ModThree.lean`'s reciprocity development, and for the verdict — negative — on
unifying with `Fermat/FLT/NumberField/ArtinSymbol.lean`'s `artinMap_toPrincipalIdeal`.

The leaf count is UNCHANGED, `1 → 1`. What the trade buys is that the surviving statement
mentions no `Subgroup`, no `relIndex`, no divisor group and no `Im`/`P`/`N`: it is a
statement about an ideal and a character, in the same vocabulary as the base case that is
already proven one file away.

**WHAT THIS FORM CHANGES relative to the `ModThree.lean` statement, and why each change
is faithful.**

1. *The modulus is a POWER of `mm₀`, and the existential is over the exponent `t` rather
   than over an ideal.* The parent's conclusion quantified over an `mm` with
   `mm₀ ∣ mm` and `∀ w, w.asIdeal ∣ mm → w.asIdeal ∣ mm₀` — i.e. an enlargement of `mm₀`
   in the EXPONENTS only. `mm₀ ^ (t+1)` is such an enlargement, and the parent's own
   FAITHFULNESS paragraph names exactly this witness class: "True with `mm` any common
   multiple of `mm₀` and the conductor of `M/F` supported inside `supp mm₀` — e.g. a
   sufficiently high power of `mm₀`, using that the conductor is supported at the ramified
   primes and `hmm₀ram` places those in `supp mm₀`." So this is a STRENGTHENING of the leaf
   to precisely the witnesses for which its truth was established, not a new claim. The
   glue below recovers the parent's existential form from it.
2. *`Im` and `N` are pinned by `mm₀`, `P` by `mm₀ ^ (t+1)`.* This is not a further change:
   `Im` and `N` depend on the modulus only through its prime SUPPORT (they are cut out by
   `v.asIdeal ∣ mm` and `¬ v.asIdeal ∣ mm` respectively), and a height-one prime divides
   `mm₀ ^ (t+1)` exactly when it divides `mm₀`. Writing them at `mm₀` makes visible what
   the enlargement is doing — it shrinks `P` and nothing else, which is the whole content
   of "choose an admissible modulus".
3. *`1 < Nat.card (Im.map φ)` is assumed.* Free: at `Nat.card (Im.map φ) ≤ 1` the
   conclusion is `≤ 1 ≤ (P ⊔ N).relIndex Im`, and `(P ⊔ N).relIndex Im ≠ 0` follows from
   the hypothesis `P.relIndex Im ≠ 0` by `Subgroup.relIndex_dvd_of_le_left` at
   `P ≤ P ⊔ N`. The glue below does exactly that, so a prover here may assume `χ` cuts out
   a NONTRIVIAL extension — which every route needs, since all of them begin by choosing a
   nontrivial character of the relevant quotient.

**FALSITY: the two refutations of earlier forms transfer verbatim and are the reason the
hypotheses look the way they do.** They are recorded in full at
`ModThree.lean`'s `exists_artinDivisorNormIndex_le_ray_class`; in one line each:

* with `mm` UNIVERSALLY quantified and constrained only by "divisible by the ramified
  primes", `F = ℚ` with `χ` cutting out `ℚ(i)` and `mm = (2)` gives `2 ≤ 1` — the ramified
  SUPPORT is `(2)` but the conductor is `(4)`, so a support condition never suffices and
  the modulus must be an OUTPUT;
* with `mm` an output but `mm₀` unconstrained, the support clause confines `supp mm` to
  `supp mm₀`, and `mm₀ = ⊤` (or `(3)`) with the same `χ` gives `2 ≤ 1` again — whence
  `hmm₀ram`, which the consumer already holds as the `mpr` of an iff it was discarding.

**And the `mm₀ = ⊤` branch is REAL, not a corner case to exclude.** `hmm₀ram` is vacuous
when `χ` is unramified at every finite place, so `mm₀ = ⊤` is admissible input and forces
`t` to be irrelevant (`⊤ ^ (t+1) = ⊤`), `Im = ⊤`, `P` the narrow principal divisors and `N`
generated over EVERY `v`. The statement is then the inequality against the narrow class
number `h⁺(F)`, and it is true and nontrivial: `F = ℚ(√-5)` has `h = h⁺ = 2` and the
quadratic `χ` cutting out its Hilbert class field gives `2 ≤ 2`. **Any proof that begins
"let `v` be a prime dividing `mm`" is wrong on this branch**, and neither `ℚ(i)`
counterexample warns you, because `χ` is ramified at `2` in both.

**What is NOT this leaf's to discharge** (all handed down as hypotheses, all PROVEN in
`ModThree.lean`): the cyclicity and `ℓ ^ k`-torsion of `Im.map φ`; `N ≤ φ.ker`, which is
the non-reciprocity half of the containment (`φ` sends the generator `single v (f_v)` to
`χ (globalFrob v) ^ f_v = 1`); `P ≤ Im` and `N ≤ Im`; and the finiteness
`P.relIndex Im ≠ 0` of the narrow ray class group, which is
`relIndex_narrowRayGroup_ne_zero_ray_class` and contains no class field theory at all.

**Check that would refute this form**: hypotheses as stated, together with a `χ` and an
`mm₀` divisible by every ramified prime such that for EVERY `t` there are `φ`, `d`, `Im`,
`P`, `N` meeting the pinning clauses with `1 < Nat.card (Im.map φ)` and
`(P ⊔ N).relIndex Im < Nat.card (Im.map φ)`. Both refutations above are of that shape and
both were possible only because the modulus could fail to be admissible; here it is
`t` that buys admissibility, and the classical theorem says a large enough `t` always
does.

**SECOND FALSITY AUDIT, RUN FROM SCRATCH (2026-07-31, `flt-lean-330`). VERDICT: TRUE AS
STATED.** `CLAUDE.md`'s rule is that a leaf restated a SECOND time voids its earlier audit
rather than inheriting it — this statement is the composite of the 2026-07-30 weakening
(`P ≤ Im`, `N ≤ Im`, `P.relIndex Im ≠ 0` received rather than proved) and the 2026-07-31
prime-power hoist, and no audit had ever been run against the composite. What was checked,
in the order it was checked:

* *`φ` and `d` are PINNED, so the `∀` is not an attack surface.* The elements
  `Multiplicative.ofAdd (Finsupp.single v 1)` generate the free abelian group
  `Multiplicative (HeightOneSpectrum (𝓞 F) →₀ ℤ)`, so `hφv` determines `φ` uniquely; `hφd`
  is then a CONSEQUENCE of `hcmul`/`hcfrob` and not a further constraint. `hd` pins `d` as
  the valuation vector, and `hIm`, `hN` pin `Im`, `N` outright. Given `t`, the family
  quantified over is a single point up to equality, which is what makes the `∃ t ∀ …` shape
  safe — contrast the FIRST refutation above, where the modulus was universally quantified
  and a wrong one was reachable.
* *`P ≤ Im` costs nothing and hides nothing.* `δ - 1 ∈ mm₀ ^ (t+1)` forces `δ ≡ 1 mod v`,
  hence `ord_v δ = 0`, at every `v ∣ mm₀`.
* *MONOTONICITY IN `t`, and it runs the RIGHT WAY — this is the load-bearing check.*
  Raising `t` SHRINKS `P` (fewer admissible `δ`), hence shrinks `P ⊔ N`, hence ENLARGES
  `(P ⊔ N).relIndex Im`, while `Im`, `N` and `Nat.card (Im.map φ)` do not move. So the
  conclusion is monotone INCREASING in `t`: one admissible `t` suffices and every larger one
  works too, which is exactly what `∃ t` asserts. Had the dependence run the other way, `∃ t`
  would have been a trap (satisfiable at a degenerate `t` and useless at every admissible
  one), and that is the shape to check first in any leaf whose witness is an exponent.
* *Identification with the classical theorem.* For `t` large, `mm := mm₀ ^ (t+1)` is
  divisible by the conductor `𝔣(M/F)` — `𝔣` is supported at the primes ramified in `M`, and
  `hmm₀ram` places those in `supp mm₀` — so `mm` is ADMISSIBLE. Then `Im = I(mm)`,
  `N = N_{M/F} I_M(mm)`, `P = P⁺_{F,mm}`, and Takagi gives
  `[I(mm) : P_{F,mm} · N] = [M : F] = Nat.card (Im.map φ)`; passing from `P_{F,mm}` to the
  smaller narrow `P⁺_{F,mm}` only increases the index. Hence `n ≤ h`.
* *The `mm₀ = ⊤` branch survives it.* No height-one prime divides `⊤`, so `hmm₀ram` forces
  `χ` unramified at every finite place; the claim becomes the inequality against the NARROW
  class number, `n ≤ h⁺(F)`, which is the `mm = 1` case of the same theorem.

**THE DIRECTION OF THE INEQUALITY, AND A ROUTE OFFERED ABOVE THAT PROVES THE OPPOSITE ONE**
(correction, 2026-07-31). The head of this docstring says the theorem is proved "either by
Chevalley's ambiguous class number formula / Herbrand quotients … or analytically from
`L(1, ψ) ≠ 0` for ray class characters". **The second alternative is for the OTHER
inequality**, and the error is expensive rather than academic, because `Chebotarev.lean` —
13 479 lines, and in THIS module's own import cone — already carries most of the analytic
machinery it names, so the route looks not merely available but half-built.

Write `n := Nat.card (Im.map φ) = [M : F]` and `h := (P ⊔ N).relIndex Im = [I(mm) : P·N]`.
The analytic input `L(1, ψ) ≠ 0` for the nontrivial characters `ψ` of `I(mm)/(P·N)` gives
each class of that quotient Dirichlet density `1/h`. A prime `v ∤ mm` that SPLITS COMPLETELY
in `M` has `f_v = 1`, so `v = v ^ {f_v} ∈ N` and `v` lies in the TRIVIAL class; and the split
primes have density `1/n`, read off `ζ_M(s)` alone with no reciprocity anywhere. The
inclusion of a density-`1/n` set in a density-`1/h` set gives `1/n ≤ 1/h`, i.e. **`h ≤ n`** —
the reverse of what is wanted here. The direction stated in this file, `n ≤ h`, is the
COHOMOLOGICAL one: the Herbrand quotient of the idele class group of a CYCLIC extension, or
Chevalley's ambiguous class number formula. That is also what `IsCyclic (Im.map φ)` is doing
in the hypothesis list; the analytic argument has no use for it.

**INVENTORY OF THE THREE ROUTES AGAINST THE TREE AS IT STANDS (2026-07-31), so that nobody
re-derives it.**

1. *Analytic — largely PRESENT, and aimed at the other inequality.*
   `Fermat/FLT/GaloisRepresentation/Chebotarev.lean` has narrow ray class equivalence
   (`IsNarrowRayEquiv`, `narrowRaySetoid`, `finite_quotient_narrowRaySetoid`), the
   ideal-counting theorem in a narrow ray class
   (`exists_forall_abs_natCard_isNarrowRayEquiv_sub_mul_le_rpow`), ray class `L`-series with
   their behaviour near `s = 1`, and full Frobenius density (`dense_conjClasses_globalFrob`).
   By the paragraph above, none of it proves `n ≤ h`.
2. *Cohomological — NOTHING, here or upstream.* No Herbrand quotient, no cohomology of the
   idele class group, no ambiguous class number formula: `grep -i herbrand` over `Fermat/`
   returns prose only, and `~/cs/FLT` has none of it either. This is the honest cost of the
   route the head of this docstring recommends, and it is a development, not a leaf.
3. *Cite RECIPROCITY — which is what this project has ALREADY done at modulus `1`.*
   `Fermat/FLT/NumberField/ArtinSymbol.lean` carries `artinMap_toPrincipalIdeal` (Artin
   reciprocity at modulus `1`) as an OPEN LEAF, and
   `Fermat/FLT/NumberField/UnramifiedClassFieldBound.lean`'s
   `finrank_le_index_relNormClassSubgroup` — *this same inequality at modulus `1`* — is
   PROVEN over it by exactly the containment argument the head of this docstring calls
   unavailable. So "**NOT** obtainable from the Artin map" is a claim about mathematical
   depth, and it is correct as such; it is not a claim about what this development permits,
   and it had been read as one.

**THE RECUT THAT IS AVAILABLE, AND WHY IT WAS DELIBERATELY NOT TAKEN HERE.** Over a ray
class Artin reciprocity citation this leaf is about thirty lines: `P ≤ φ.ker` is the
citation, `N ≤ φ.ker` is already a hypothesis, so `P ⊔ N ≤ φ.ker ⊓ Im` and
`Subgroup.relIndex_le_of_le`/`Subgroup.index_ker` finish it. That trade is `1` leaf for `1`
STRICTLY HARDER leaf, hence a REGRESSION — *unless* the new citation also discharges
`artinMap_toPrincipalIdeal`, which it does. So the recut is worth making exactly ONCE, by an
agent who owns this module and `ArtinSymbol.lean` together and who states ray class
reciprocity in a module upstream of both. One design constraint for whoever does it, since
it is the thing that makes the two leaves look incompatible: this leaf uses the NARROW ray
group `P⁺` (total positivity is a conjunct of `hP`), whereas `artinMap_toPrincipalIdeal`
uses the WIDE one at modulus `1` and buys admissibility with
`IsUnramifiedAtInfinitePlaces` instead. A shared statement therefore needs a modulus with
BOTH a finite and an infinite part; specialising the infinite part to "all real places" gives
this leaf and specialising it to "none, under `IsUnramifiedAtInfinitePlaces`" gives that one.
Taking the recut here alone would trade a closed leaf for an open harder one, which is why
this file still ends in `sorry`. -/
theorem exists_natCard_charDivisorImage_le_normIndex_primePow_ray_class
    (F : Type u) [Field F] [NumberField F]
    (χ : Γ F → Dickson.K 3)
    (hmul : ∀ a b : Γ F, χ (a * b) = χ a * χ b)
    (V : Subgroup (Γ F)) (hVopen : IsOpen (V : Set (Γ F)))
    (hVker : ∀ a ∈ V, χ a = 1)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (k : ℕ)
    (hord : ∀ a : Γ F, χ a ^ (ℓ ^ k) = 1)
    (c : Ideal (NumberField.RingOfIntegers F) → Dickson.K 3)
    (hcmul : ∀ I J : Ideal (NumberField.RingOfIntegers F), I ≠ ⊥ → J ≠ ⊥ →
      c (I * J) = c I * c J)
    (hcfrob : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      c v.asIdeal = χ (globalFrob v))
    (mm₀ : Ideal (NumberField.RingOfIntegers F)) (hmm₀ : mm₀ ≠ ⊥)
    (hmm₀ram : ∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      (∃ a : Γ F, ∃ σ ∈ localInertiaGroup w,
        χ (a * Field.absoluteGaloisGroup.map
          (algebraMap F (IsDedekindDomain.HeightOneSpectrum.adicCompletion F w)) σ * a⁻¹)
          ≠ 1) →
      w.asIdeal ∣ mm₀) :
    ∃ t : ℕ,
      ∀ (φ : Multiplicative (IsDedekindDomain.HeightOneSpectrum
          (NumberField.RingOfIntegers F) →₀ ℤ) →* (Dickson.K 3)ˣ)
        (d : NumberField.RingOfIntegers F → Multiplicative
          (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) →₀ ℤ))
        (Im P N : Subgroup (Multiplicative
          (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) →₀ ℤ))),
        (∀ δ : NumberField.RingOfIntegers F, δ ≠ 0 →
          ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), ∀ n : ℕ,
            (v.asIdeal ^ n ∣ Ideal.span {δ} ↔ (n : ℤ) ≤ Multiplicative.toAdd (d δ) v)) →
        (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
          ((φ (Multiplicative.ofAdd (Finsupp.single v (1 : ℤ)))) : Dickson.K 3)
            = χ (globalFrob v)) →
        (∀ δ : NumberField.RingOfIntegers F, δ ≠ 0 →
          ((φ (d δ) : Dickson.K 3)) = c (Ideal.span {δ})) →
        (∀ x, x ∈ Im ↔ ∀ v : IsDedekindDomain.HeightOneSpectrum
          (NumberField.RingOfIntegers F), v.asIdeal ∣ mm₀ →
            Multiplicative.toAdd x v = 0) →
        P = Subgroup.closure {y | ∃ δ : NumberField.RingOfIntegers F, δ ≠ 0 ∧
          (∀ ψ : F →+* ℝ, 0 < ψ (algebraMap (NumberField.RingOfIntegers F) F δ)) ∧
          δ - 1 ∈ mm₀ ^ (t + 1) ∧ y = d δ} →
        N = Subgroup.closure {y | ∃ v : IsDedekindDomain.HeightOneSpectrum
          (NumberField.RingOfIntegers F), ¬ (v.asIdeal ∣ mm₀) ∧
          y = Multiplicative.ofAdd (Finsupp.single v (orderOf (χ (globalFrob v)) : ℤ))} →
        IsCyclic (Im.map φ) → Nat.card (Im.map φ) ∣ ℓ ^ k → N ≤ φ.ker →
        P ≤ Im → N ≤ Im → P.relIndex Im ≠ 0 →
        1 < Nat.card (Im.map φ) →
        Nat.card (Im.map φ) ≤ (P ⊔ N).relIndex Im := by
  obtain ⟨t, ht⟩ := exists_artinSymbol_span_eq_one_narrowRay_ray_class
    F χ hmul V hVopen hVker ℓ hℓ hℓ3 k hord c hcmul hcfrob mm₀ hmm₀ hmm₀ram
  refine ⟨t, ?_⟩
  intro φ d Im P N _hd _hφv hφd _hIm hP hN _hcyc _hcard hNker _hPIm _hNIm hPidx _hgt
  -- **RECIPROCITY**: the narrow ray group lies in the kernel of the divisor Artin map.
  -- `P` is generated by the `d δ` for `δ` in the ray, `hφd` identifies `φ (d δ)` with the
  -- ideal symbol `c ((δ))`, and the leaf above kills that.
  have hPker : P ≤ φ.ker := by
    rw [hP]
    refine (Subgroup.closure_le _).2 ?_
    intro y hy
    obtain ⟨δ, hδ0, hδpos, hδcong, rfl⟩ := hy
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    refine Units.ext ?_
    rw [hφd δ hδ0, Units.val_one]
    exact ht δ hδ0 hδpos hδcong
  -- `N ≤ φ.ker` is a hypothesis — it is the elementary half of the containment, `φ` sending
  -- the generator `single v (f_v)` to `χ (globalFrob v) ^ f_v = 1`.
  have hsup : P ⊔ N ≤ φ.ker := sup_le hPker hNker
  -- The index is FINITE, inherited from `P.relIndex Im ≠ 0` along `P ≤ P ⊔ N`.  Without
  -- this the `Nat.le_of_dvd` below is unavailable and the conclusion is false for the
  -- trivial reason that `relIndex` returns `0` for an infinite index.
  have hne : (P ⊔ N).relIndex Im ≠ 0 := fun h0 =>
    hPidx (zero_dvd_iff.mp (h0 ▸ Subgroup.relIndex_dvd_of_le_left Im le_sup_left))
  -- `Nat.card (Im.map φ) = (ker φ).relIndex Im` (`Subgroup.relIndex_ker`), and `relIndex`
  -- is antitone in its first argument, so the containment above IS the inequality.
  calc Nat.card (Im.map φ) = φ.ker.relIndex Im := (Subgroup.relIndex_ker (K := Im) φ).symm
    _ ≤ (P ⊔ N).relIndex Im :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero hne)
          (Subgroup.relIndex_dvd_of_le_left Im hsup)

/-- **THE GLOBAL NORM-INDEX INEQUALITY IN THE FORM THE RAY-CLASS CLUSTER CONSUMES**
(**PROVEN 2026-07-31** as glue over
`exists_natCard_charDivisorImage_le_normIndex_primePow_ray_class` above).

This is verbatim `ModThree.lean`'s `exists_natCard_charDivisorImage_le_ray_class`, with the
one cosmetic difference that the hypothesis `hmm₀ram` is written with the definition
`IsRamifiedCharRayClass` UNFOLDED — that definition lives in `ModThree.lean`, downstream of
this module, and unfolding it is the cheapest way to avoid moving it. The two statements
are definitionally equal, which is what `ModThree.lean`'s one-line glue checks.

The proof is bookkeeping in two steps.

* *The modulus.* Take `mm := mm₀ ^ (t + 1)` for the `t` produced above. Then `mm ≠ ⊥`,
  `mm₀ ∣ mm`, and a height-one prime divides `mm` exactly when it divides `mm₀` (`→` because
  such a prime is a prime element of the ideal monoid, `←` because `mm₀ ∣ mm₀ ^ (t+1)`).
  That same equivalence rewrites the consumer's `Im` and `N`, which are cut out by
  divisibility by `mm`, into the `mm₀`-forms the leaf above is stated in; `P`, which is cut
  out by the CONGRUENCE `δ - 1 ∈ mm`, is untouched and is where the enlargement acts.
* *The trivial case.* If `Nat.card (Im.map φ) ≤ 1` the conclusion needs only
  `(P ⊔ N).relIndex Im ≠ 0`, which follows from `P.relIndex Im ≠ 0` and `P ≤ P ⊔ N`. -/
theorem exists_natCard_charDivisorImage_le_normIndex_ray_class
    (F : Type u) [Field F] [NumberField F]
    (χ : Γ F → Dickson.K 3)
    (hmul : ∀ a b : Γ F, χ (a * b) = χ a * χ b)
    (V : Subgroup (Γ F)) (hVopen : IsOpen (V : Set (Γ F)))
    (hVker : ∀ a ∈ V, χ a = 1)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (k : ℕ)
    (hord : ∀ a : Γ F, χ a ^ (ℓ ^ k) = 1)
    (c : Ideal (NumberField.RingOfIntegers F) → Dickson.K 3)
    (hcmul : ∀ I J : Ideal (NumberField.RingOfIntegers F), I ≠ ⊥ → J ≠ ⊥ →
      c (I * J) = c I * c J)
    (hcfrob : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      c v.asIdeal = χ (globalFrob v))
    (mm₀ : Ideal (NumberField.RingOfIntegers F)) (hmm₀ : mm₀ ≠ ⊥)
    (hmm₀ram : ∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      (∃ a : Γ F, ∃ σ ∈ localInertiaGroup w,
        χ (a * Field.absoluteGaloisGroup.map
          (algebraMap F (IsDedekindDomain.HeightOneSpectrum.adicCompletion F w)) σ * a⁻¹)
          ≠ 1) →
      w.asIdeal ∣ mm₀) :
    ∃ mm : Ideal (NumberField.RingOfIntegers F), mm ≠ ⊥ ∧ mm₀ ∣ mm ∧
      (∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
        w.asIdeal ∣ mm → w.asIdeal ∣ mm₀) ∧
      ∀ (φ : Multiplicative (IsDedekindDomain.HeightOneSpectrum
          (NumberField.RingOfIntegers F) →₀ ℤ) →* (Dickson.K 3)ˣ)
        (d : NumberField.RingOfIntegers F → Multiplicative
          (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) →₀ ℤ))
        (Im P N : Subgroup (Multiplicative
          (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) →₀ ℤ))),
        (∀ δ : NumberField.RingOfIntegers F, δ ≠ 0 →
          ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), ∀ n : ℕ,
            (v.asIdeal ^ n ∣ Ideal.span {δ} ↔ (n : ℤ) ≤ Multiplicative.toAdd (d δ) v)) →
        (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
          ((φ (Multiplicative.ofAdd (Finsupp.single v (1 : ℤ)))) : Dickson.K 3)
            = χ (globalFrob v)) →
        (∀ δ : NumberField.RingOfIntegers F, δ ≠ 0 →
          ((φ (d δ) : Dickson.K 3)) = c (Ideal.span {δ})) →
        (∀ x, x ∈ Im ↔ ∀ v : IsDedekindDomain.HeightOneSpectrum
          (NumberField.RingOfIntegers F), v.asIdeal ∣ mm →
            Multiplicative.toAdd x v = 0) →
        P = Subgroup.closure {y | ∃ δ : NumberField.RingOfIntegers F, δ ≠ 0 ∧
          (∀ ψ : F →+* ℝ, 0 < ψ (algebraMap (NumberField.RingOfIntegers F) F δ)) ∧
          δ - 1 ∈ mm ∧ y = d δ} →
        N = Subgroup.closure {y | ∃ v : IsDedekindDomain.HeightOneSpectrum
          (NumberField.RingOfIntegers F), ¬ (v.asIdeal ∣ mm) ∧
          y = Multiplicative.ofAdd (Finsupp.single v (orderOf (χ (globalFrob v)) : ℤ))} →
        IsCyclic (Im.map φ) → Nat.card (Im.map φ) ∣ ℓ ^ k → N ≤ φ.ker →
        P ≤ Im → N ≤ Im → P.relIndex Im ≠ 0 →
        Nat.card (Im.map φ) ≤ (P ⊔ N).relIndex Im := by
  obtain ⟨t, ht⟩ := exists_natCard_charDivisorImage_le_normIndex_primePow_ray_class
    F χ hmul V hVopen hVker ℓ hℓ hℓ3 k hord c hcmul hcfrob mm₀ hmm₀ hmm₀ram
  -- `mm₀` and `mm₀ ^ (t+1)` have the SAME prime support: `→` because a height-one prime is
  -- a prime element of the ideal monoid, `←` because `mm₀ ∣ mm₀ ^ (t+1)`.
  have hdvd : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F),
      v.asIdeal ∣ mm₀ ^ (t + 1) ↔ v.asIdeal ∣ mm₀ :=
    fun v => ⟨fun h => ((Ideal.prime_iff_isPrime v.ne_bot).mpr v.isPrime).dvd_of_dvd_pow h,
      fun h => h.trans (dvd_pow_self mm₀ (Nat.succ_ne_zero t))⟩
  have hpow : mm₀ ^ (t + 1) ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot] at hmm₀ ⊢
    exact pow_ne_zero _ hmm₀
  refine ⟨mm₀ ^ (t + 1), hpow, dvd_pow_self mm₀ (Nat.succ_ne_zero t),
    fun w hw => (hdvd w).mp hw, ?_⟩
  intro φ d Im P N hd hφv hφd hIm hP hN hcyc hcard hNker hPIm hNIm hPidx
  by_cases hgt : 1 < Nat.card (Im.map φ)
  -- The substantive case, over the leaf above.  `Im` and `N` see only the SUPPORT of the
  -- modulus, so they transport along `hdvd`; `P` is the congruence group and is untouched.
  · refine ht φ d Im P N hd hφv hφd ?_ hP ?_ hcyc hcard hNker hPIm hNIm hPidx hgt
    · intro x
      rw [hIm x]
      exact ⟨fun h v hv => h v ((hdvd v).mpr hv), fun h v hv => h v ((hdvd v).mp hv)⟩
    · have hset : {y : Multiplicative (IsDedekindDomain.HeightOneSpectrum
          (NumberField.RingOfIntegers F) →₀ ℤ) | ∃ v : IsDedekindDomain.HeightOneSpectrum
            (NumberField.RingOfIntegers F), ¬ (v.asIdeal ∣ mm₀ ^ (t + 1)) ∧
            y = Multiplicative.ofAdd (Finsupp.single v (orderOf (χ (globalFrob v)) : ℤ))}
          = {y | ∃ v : IsDedekindDomain.HeightOneSpectrum
            (NumberField.RingOfIntegers F), ¬ (v.asIdeal ∣ mm₀) ∧
            y = Multiplicative.ofAdd
              (Finsupp.single v (orderOf (χ (globalFrob v)) : ℤ))} := by
        ext y
        simp only [Set.mem_setOf_eq]
        exact ⟨fun ⟨v, hv, hy⟩ => ⟨v, fun hcon => hv ((hdvd v).mpr hcon), hy⟩,
          fun ⟨v, hv, hy⟩ => ⟨v, fun hcon => hv ((hdvd v).mp hcon), hy⟩⟩
      rw [hN, hset]
  -- The trivial case: the conclusion needs only that the index is finite, and `P ≤ P ⊔ N`
  -- transports the hypothesised finiteness of `P.relIndex Im`.
  · have hdvd0 : (P ⊔ N).relIndex Im ∣ P.relIndex Im :=
      Subgroup.relIndex_dvd_of_le_left Im le_sup_left
    have hne : (P ⊔ N).relIndex Im ≠ 0 := fun h0 =>
      hPidx (zero_dvd_iff.mp (h0 ▸ hdvd0))
    exact (Nat.not_lt.mp hgt).trans (Nat.one_le_iff_ne_zero.mpr hne)

end GaloisRepresentation.IsHardlyRamified
