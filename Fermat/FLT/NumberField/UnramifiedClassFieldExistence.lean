/-
NumberField/UnramifiedClassFieldExistence.lean — own work for the Fermat
project (not vendored from the FLT project).
-/
module

public import Fermat.FLT.NumberField.UnramifiedClassFieldBound
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.NumberTheory.RamificationInertia.Unramified

/-!
# The unramified EXISTENCE theorem of class field theory, at modulus `1`

This file carries the **existence** half of unramified class field theory:
a number field `K` has, for every subgroup `N ≤ Cl(𝓞 K)`, a finite abelian
extension unramified at every finite prime and at every infinite place whose
norm class group is exactly `N` — in particular (at `N = ⊥`) it has a
**Hilbert class field**, of degree exactly `h_K`.

It is the companion of `Fermat/FLT/NumberField/UnramifiedClassFieldBound.lean`,
which carries the **upper bound** (`[L : K] ≤ h_K` for every such `L`), and it
deliberately sits beside it rather than under `Fermat/FLT/Mathlib/`: the two
halves of one correspondence share the vocabulary `relNormClassSubgroup`, and
splitting them across directories would make the second inequality unfindable
from the first. Both are cited from `Fermat/FLT/Modularity/Interface.lean`,
which elaborates for the better part of an hour on one core; everything here is
pure algebraic number theory that needs none of it, so a prover attacking the
open leaves below iterates against THIS file in seconds. Do not move the
material into `Interface.lean`.

## Main results

* `NumberField.exists_hilbertClassField_artinIso` — **OPEN LEAF, and this is
  where the class field theory is.** Unramified class field theory at modulus `1`
  in one statement: the Hilbert class field exists inside `AlgebraicClosure K`,
  the Artin map is an isomorphism `Cl(𝓞 K) ≃ Gal(HCF/K)`, and the norm class
  group of an intermediate field is the subgroup fixing it. Cut 2026-07-30 out
  of the existence theorem below, which it now proves.
* `NumberField.exists_classField_of_subgroup` — PROVEN from the leaf above by the
  Galois correspondence. The existence theorem at modulus `1`: every subgroup of
  `Cl(𝓞 K)` is the norm class group of a finite abelian extension unramified at
  every finite prime and at every infinite place.
* `NumberField.exists_surjective_aut_classGroupQuotient` — **OPEN LEAF.** The
  Artin map in the direction `Gal(L/K) ↠ Cl(𝓞 K) ⧸ relNormClassSubgroup K L`,
  cut out of the first inequality on 2026-07-30. The mirror image of the
  companion file's `exists_surjective_classGroupHom_aut_of_unramified_abelian`,
  and NOT implied by it: this one survives ramification at the infinite places.
* `NumberField.index_relNormClassSubgroup_le_finrank` — PROVEN from the leaf
  above by counting. The first inequality `[I_K : P_K · N_{L/K} I_L] ≤ [L : K]`,
  in the direction OPPOSITE to `finrank_le_index_relNormClassSubgroup` of the
  companion file.
* `NumberField.exists_classField_finrank_eq_index` — PROVEN from the two
  leaves above together with the companion file's
  `finrank_le_index_relNormClassSubgroup`, by `le_antisymm`.
* `NumberField.exists_hilbertClassField` — PROVEN, the case `N = ⊥`: `K` has a
  finite abelian extension unramified at every finite prime, of degree exactly
  `h_K`.

The ultimate consumer is
`GaloisRepresentation.Modularity.exists_unramifiedAbelian_primePow_dvd_finrank_of_dvd`
in `Fermat/FLT/Modularity/Interface.lean`, which is now proven over
`exists_hilbertClassField` and `Nat.ordProj_dvd` and nothing else.

## Where the rest of the cluster's mathematics now lives (2026-07-30)

The companion file `UnramifiedClassFieldBound.lean` is SORRY-FREE as of
2026-07-30. Its former leaf was decomposed one module further upstream into
`Fermat/FLT/NumberField/ArtinSymbol.lean`, which carries

* the Artin symbol itself — `NumberField.frobAt`, PROVEN well defined on primes
  of `𝓞 K` for abelian `Gal(L/K)`, with `frobAt ^ f(Q|𝓞 K) = 1` at an
  unramified prime (mathlib's `arithFrobAt` turned out to be present at this
  pin, which is what made this provable);
* `NumberField.exists_classGroupHom_eq_frobAt` — OPEN, Artin RECIPROCITY at
  modulus `1`;
* `NumberField.closure_frobAt_eq_top` — OPEN, CHEBOTAREV.

**Read that file before attacking either leaf below.** But note carefully that
neither of its two leaves is enough for `index_relNormClassSubgroup_le_finrank`:
both are stated at modulus `1`, i.e. under `IsUnramifiedAtInfinitePlaces`, and
that leaf deliberately does NOT assume it. See that leaf's docstring for what is
needed instead.
-/

@[expose] public section

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- **UNRAMIFIED CLASS FIELD THEORY AT MODULUS `1`, IN ONE STATEMENT: the Hilbert
class field `HCF` of `K` exists inside `AlgebraicClosure K`, the Artin map is an
ISOMORPHISM `Cl(𝓞 K) ≃ Gal(HCF/K)`, and under it the norm class group of every
intermediate field is exactly the subgroup fixing that field** (SORRY LEAF, cut
2026-07-30 out of `exists_classField_of_subgroup` below, which is now PROVEN from
it and from nothing else).

**THIS IS WHERE THE CLASS FIELD THEORY OF THIS CLUSTER NOW LIVES**, together with
`exists_surjective_aut_classGroupQuotient` below and the companion file's
`exists_surjective_classGroupHom_aut_of_unramified_abelian`. It is the canonical
form — Neukirch VI (6.9), the theorem that "the ideal group belonging to `H` is
`P_K · N_{H/K} I_H`" — rather than the "for every subgroup `N` there exists a
field" shape it replaces: the classical proof constructs ONE field `HCF` and one
map, and then the whole correspondence is the Galois correspondence, which is
exactly how the consumer below now reads.

**What is deep here, in decreasing order.** (i) `Art` is well defined on ideal
CLASSES — Artin reciprocity, that principal ideals go to `1`. (ii) `Art` is
SURJECTIVE — Chebotarev, or the analytic first inequality. (iii) The `≥` half of
the dictionary — that the norm classes of `F` already fill up
`Art⁻¹ Gal(HCF/F)`, again Chebotarev, applied to `HCF·F/F`. (iv) The `≤` half —
the Frobenius computation `Frob_𝔭^{f(𝔓/𝔭)} = 1`, cheap once (i) exists. (v) The
existence of `HCF` itself, i.e. the existence theorem. Nothing in the pin helps
with any of these; see the survey below.

**Soundness — the intended inhabitant.** `HCF` is the maximal abelian extension
of `K` inside `AlgebraicClosure K` unramified at every finite prime and at every
infinite place, `Art` is the Artin map `𝔭 ↦ Frob_𝔭` descended to `Cl(𝓞 K)`, and
the dictionary is the class field correspondence at modulus `1`.

**PINNING — this statement is far harder to satisfy cheaply than the leaf it
replaced.** `Art` is asked to be an ISOMORPHISM, so `[HCF : K] = h_K` is forced,
and with it the existence of an everywhere-unramified abelian extension of degree
exactly the class number. The two extreme intermediate fields pin the dictionary
at both ends and are worth checking against the classical statements:

* `F = ⊤` gives `relNormClassSubgroup K HCF = Art⁻¹ ⊥ = ⊥` — every ideal of `K`
  that is a norm from the Hilbert class field is principal, i.e. the ideal group
  belonging to `HCF` is `P_K`;
* `F = ⊥` gives `relNormClassSubgroup K K = Art⁻¹ ⊤ = ⊤`, which is the trivial
  sanity check that every class is the class of some ideal.

So an adversary cannot take `HCF = K` unless `h_K = 1`, and cannot weaken the
dictionary to an inclusion in either direction.

**Why `IntermediateField.lift F` and the `(_ : NumberField _)` binder.** The
consumer needs a subfield of `AlgebraicClosure K` — that is what
`exists_classField_of_subgroup` and the ultimate consumers in
`Modularity/Interface.lean` are stated with — while the Galois correspondence
lives among the `IntermediateField K HCF`. `lift` is the bridge, and stating the
dictionary on the `lift` side is what keeps the consumer free of a transfer along
`IntermediateField.liftAlgEquiv`: transferring `relNormClassSubgroup` or
`Algebra.IsUnramifiedAt` along a `K`-algebra isomorphism means transporting rings
of integers and their primes, for which the pin has no API. The
`NumberField ↥(lift F)` binder is needed because it cannot be synthesised:
`AlgebraicClosure K` is not finite over `K`, so the instance for intermediate
fields of a finite extension does not apply, and `NumberField.of_module_finite`
is a theorem rather than an instance. It costs the consumer one `inferInstance`.

**What the consumer's proof does — this plumbing is now PROVEN once, and is the
reusable part of this commit.** Given `N`, take `F` to be the fixed field of
`Art N` inside `HCF` and `H := lift F`. Then
`IntermediateField.fixingSubgroup_fixedField` and
`Subgroup.comap_map_eq_self_of_injective` turn the dictionary into
`relNormClassSubgroup K H = N`, and the five instance obligations of the leaf are
discharged as follows, none of them by hand:

* `FiniteDimensional K H` — `FiniteDimensional.of_injective` along the inclusion
  `H →ₐ[K] HCF`, whence `NumberField H` by `NumberField.of_module_finite`;
* `IsGalois K H` and the commutativity of `Gal(H/K)` — both at once from
  mathlib's `IsAbelianGalois.of_algHom` applied to that inclusion: an
  intermediate field of an abelian extension is abelian over the base, so
  nothing about normal subgroups or `restrictNormal` is needed;
* `IsUnramifiedAtInfinitePlaces K H` — `IsUnramifiedAtInfinitePlaces.bot` along
  the tower `K ⊆ H ⊆ HCF`;
* unramifiedness at the finite primes — going up (`Ideal.exists_ideal_over_prime`
  `_of_isIntegral_of_isDomain`) to a prime of `𝓞 HCF` over the given prime of
  `𝓞 H`, then `Algebra.IsUnramifiedAt.of_liesOver`, which is mathlib's descent of
  unramifiedness to an intermediate ring. That descent is the one step that
  looked like it would need `e(𝔓|𝔭) = e(𝔓|𝔮)·e(𝔮|𝔭)` by hand; it does not.

**⚠ `IsUnramifiedAtInfinitePlaces K HCF` IS LOAD-BEARING in the conclusion and
must not be dropped**, for the reason recorded on the consumer below and in the
companion file: without it the companion's
`finrank_le_index_relNormClassSubgroup` is FALSE (`K = ℚ(√3)` has `h_K = 1` but
narrow class number `2`), and it is that inequality which turns this leaf into
the degree statement `exists_classField_finrank_eq_index`. Equivalently, `1` is
an admissible modulus only for extensions unramified at the archimedean places
too, and `HCF` here is the SMALL (wide) Hilbert class field, not the narrow one.

**Route.** Neukirch VI (6.9) and (7.3) and the sections preceding them;
Childress ch. 4–5; Lang *ANT* ch. X; Cassels–Fröhlich ch. VII–VIII. The classical
proof reduces to a congruence subgroup of prime exponent, adjoins `ζ_ℓ`, runs
Kummer theory over `K(ζ_ℓ)`, and descends by the translation theorem
(Verschiebungssatz) — a descent of NORM GROUPS, which is why the dictionary
clause is phrased in norm groups and not in degrees. **Do not re-cut the naive
"descend an unramified abelian extension from `K(ζ_ℓ)`" leaf**: it is FALSE, with
the PARI/GP witness recorded on the consumer below (`K = ℚ(√29)`, `h = h⁺ = 1`,
`h(K(ζ_3)) = 3`).

**Mathlib survey (re-checked 2026-07-30 against this pin).** Absent: the Hilbert
class field, ray class groups, the Artin map, Artin reciprocity, Chebotarev
density, the idele class group, class formations, Herbrand quotients, Dedekind
zeta and Dirichlet density. Present and used by the consumer or worth knowing
about for a prover: `ClassGroup`, `ClassGroup.mk0` and its finiteness,
`ClassGroup.extendedHom` (the map `Cl(A) → Cl(B)` induced by extension of
ideals — the direction OPPOSITE to the norm, and there is still no norm map on
class groups), `Ideal.relNorm` with `relNorm_relNorm` (towers),
`relNorm_algebraMap` (`N(𝔞𝓞_L) = 𝔞^{[L:K]}`), `relNorm_map_algEquiv` and
`relNorm_eq_pow_of_isPrime_isGalois` (`N 𝔓 = 𝔭^{f}`, the Frobenius computation of
(iv) above), mathlib's **Frobenius elements** (`AlgHom.IsArithFrobAt`,
`IsArithFrobAt.exists_of_isInvariant`, `eq_of_isUnramifiedAt` for uniqueness) in
`Mathlib/RingTheory/Frobenius.lean`, `IsAbelianGalois`,
`Algebra.IsUnramifiedAt.of_liesOver`, `Ideal.ramificationIdx'_eq_one_iff`, and
Hilbert 90. A prover building the Artin map should start from
`Mathlib/RingTheory/Frobenius.lean` and `Mathlib/RingTheory/Invariant/Basic.lean`
— those did not exist when this cluster's earlier surveys were written.

**Coordinate before building.** `exists_totallyNegative_sub_one_mem_of_even_`
`nrRealPlaces` in `Fermat/FLT/Modularity/KhareWintenberger.lean` needs RAY class
groups, ray class fields, their Artin map and the quadratic Hilbert symbol.
Whoever builds class field theory should build it once, HERE, generalising this
statement to a modulus, and both leaves should cite it. The companion file's
`exists_surjective_classGroupHom_aut_of_unramified_abelian` is the same
mathematics again for an ABSTRACT `L`; deriving it from this node needs a
maximality clause (every finite abelian everywhere-unramified extension of `K`
embeds into `HCF`) plus transfer of unramifiedness and of the norm class group
along a `K`-algebra isomorphism, which the pin does not supply — that is the
next piece of plumbing to write, not a reason to prove the two separately.

**The check that would refute this leaf**: a number field `K` for which no
finite abelian extension inside `AlgebraicClosure K`, unramified at every finite
prime and at every infinite place, has Galois group isomorphic to `Cl(𝓞 K)`; or
one with such an extension for which some intermediate field's norm class group
is not the subgroup fixing it. -/
theorem exists_hilbertClassField_artinIso :
    ∃ (HCF : IntermediateField K (AlgebraicClosure K)) (_ : FiniteDimensional K HCF)
      (_ : NumberField HCF) (_ : IsAbelianGalois K HCF)
      (_ : IsUnramifiedAtInfinitePlaces K HCF),
      (∀ (Q : Ideal (𝓞 HCF)) (_ : Q.IsPrime), Q ≠ ⊥ →
        Algebra.IsUnramifiedAt (𝓞 K) Q) ∧
      ∃ Art : ClassGroup (𝓞 K) ≃* (HCF ≃ₐ[K] HCF),
        ∀ (F : IntermediateField K HCF) (_ : NumberField (IntermediateField.lift F)),
          relNormClassSubgroup K (IntermediateField.lift F) =
            (IntermediateField.fixingSubgroup F).comap
              (Art : ClassGroup (𝓞 K) →* (HCF ≃ₐ[K] HCF)) :=
  sorry

/-- **THE EXISTENCE THEOREM OF UNRAMIFIED CLASS FIELD THEORY, AT MODULUS `1`:
every subgroup `N` of `Cl(𝓞 K)` is the norm class group of a finite abelian
extension of `K` unramified at every finite prime and at every infinite place**
(cut 2026-07-29 out of `exists_unramifiedAbelian_primePow_dvd_finrank_of_dvd` in
`Fermat/FLT/Modularity/Interface.lean`; PROVEN 2026-07-30 from
`exists_hilbertClassField_artinIso` above by the Galois correspondence, and from
nothing else).

The class field theory this used to carry now lives in that node, which states
the correspondence once for the single field `HCF` instead of once per subgroup
`N`; see its docstring for what is deep, for the pinning, and for the list of
instance obligations the derivation below discharges. Everything else in the
Hilbert-class-field cluster — `exists_classField_finrank_eq_index` and
`exists_hilbertClassField` below, and the whole divisibility half in
`Modularity/Interface.lean` — is proven over this statement, over
`index_relNormClassSubgroup_le_finrank` below, and over the companion file's
`finrank_le_index_relNormClassSubgroup`.

**The step performed here.** `N` becomes the subgroup `Art N` of `Gal(HCF/K)`;
its fixed field `F` inside `HCF` has `fixingSubgroup F = Art N`
(`IntermediateField.fixingSubgroup_fixedField`, the Galois correspondence), so
the node's dictionary reads
`relNormClassSubgroup K (lift F) = (Art N).comap Art = N`, the last step by
injectivity of `Art`. The remaining clauses are instance plumbing on
`H := lift F`, listed in the node's docstring.

**Soundness — the intended inhabitant.** Let `𝐇` be the Hilbert class field of
`K` and `Art : Cl(𝓞 K) ≃ Gal(𝐇/K)` the Artin isomorphism. Take `H` to be the
fixed field of `Art N`. Then `Gal(H/K) ≃ Cl(𝓞 K) ⧸ N`, `H/K` is abelian and
unramified at every place (being a subextension of `𝐇/K`), and its norm class
group is exactly `N` — that last is the statement that `N` is "the ideal group
belonging to `H`", which is the definition of the class field correspondence at
modulus `1`. At `N = ⊥` the witness is `𝐇` itself, of degree `h_K`; at `N = ⊤`
it is `H = K`.

**Why the norm-group equality rather than a degree.** The degree is a
CONSEQUENCE here, not a hypothesis: combined with the first inequality below
and with the companion file's second inequality it forces
`[H : K] = N.index` (that is `exists_classField_finrank_eq_index` below).
Stating the leaf with `relNormClassSubgroup K H = N` rather than with
`Module.finrank K H = N.index` is deliberate and is the lesson of the
refutation recorded in the docstring of
`exists_unramifiedAbelian_primePow_dvd_finrank_of_dvd`:

> what descends from `K(ζ_ℓ)` to `K` is a NORM GROUP, not an extension,

so any decomposition of this node along the classical Kummer/translation axis
must carry the norm-group formalism through the cut. A statement phrased purely
in extensions and degrees cannot express the descent step, and the naive
"descend an unramified abelian extension from `K(ζ_ℓ)`" leaf is FALSE — witness
(PARI/GP, verified 2026-07-28 and re-checked 2026-07-29): `ℓ = 3`,
`K = ℚ(√29)` has `h_K = 1` and TRIVIAL narrow class group
(`bnfnarrow` returns `[1, [], []]`), so by the companion file's upper bound the
only admissible extension of `K` is `K` itself, yet
`F = K(ζ_3) = ℚ(√29, √-3)` has `h_F = 3`. `K = ℚ(√43)` refutes it identically
(`h = 1`, `h⁺ = 2`, `h(ℚ(√43, √-3)) = 6`). **Do not re-cut that leaf.**

**Non-vacuity.** At `N = ⊥` and `K = ℚ(√29, √-3)` the leaf demands a cyclic
cubic extension unramified at every finite place and at every infinite place,
which `H = K` does not provide (`h_K = 3`, verified with PARI/GP). It is
trivial exactly when `Cl(𝓞 K)` is trivial, or at `N = ⊤`.

**PINNING.** An adversary must produce `H` with norm class group EXACTLY `N`,
not merely contained in or containing it, so `H = K` (norm group `⊤`) does not
discharge the leaf for `N ≠ ⊤`, and the Hilbert class field does not discharge
it for `N ≠ ⊥`. The class field of `N` is unique among extensions inside a
fixed algebraic closure, so the existential is as pinned as an existential can
be here; the consumer uses only the stated clauses.

**⚠ `IsUnramifiedAtInfinitePlaces K H` IS LOAD-BEARING and must NOT be dropped,
even though the ultimate consumer does not ask for it.** It is what the
companion file's `finrank_le_index_relNormClassSubgroup` needs, and that
inequality is FALSE without it: `K = ℚ(√3)` has `h_K = 1` but narrow class
number `2` (PARI/GP: `bnfinit(x^2-3,1).no = 1`, `bnrinit(K,[1,[1,1]]).no = 2`),
so the narrow Hilbert class field is a quadratic extension of `K` abelian and
unramified at every FINITE place with `[L : K] = 2 > 1 = h_K`. Deleting the
hypothesis here would therefore break the glue below, not merely weaken it.
Equivalently: `1` is an admissible modulus only for extensions unramified at
the archimedean places too.

**Route.** Neukirch VI (6.9) and the sections preceding it; Childress ch. 4–5;
Lang *ANT* ch. X; Cassels–Fröhlich ch. VII–VIII. The classical proof reduces to
a congruence subgroup of prime exponent, adjoins `ζ_ℓ`, runs Kummer theory over
`K(ζ_ℓ)`, and descends by the translation theorem (Verschiebungssatz) — a
descent of NORM GROUPS, expressible now that this leaf is phrased in them.

**Mathlib survey (re-checked 2026-07-29 against this pin).** `ClassGroup`,
`ClassGroup.mk0`, its finiteness for number fields, `Ideal.relNorm` (in the
`Module.Free`-free form), `Ideal.ramificationIdx`, `Ideal.inertiaDeg`,
`Algebra.IsUnramifiedAt`, `IsUnramifiedAtInfinitePlaces`,
`Mathlib.FieldTheory.KummerExtension`, Dirichlet's unit theorem and Hilbert 90
(`Mathlib/RepresentationTheory/Homological/GroupCohomology/Hilbert90.lean`) are
all PRESENT. Absent: the Hilbert class field, ray class groups, the Artin map,
Artin reciprocity, the `S`-unit theorem, the idele class group, class
formations, Herbrand quotients, Dedekind zeta and any Dirichlet density
material — `Mathlib/RepresentationTheory/Homological/TateCohomology/` still
carries `Basic.lean` only. The gap is the whole existence theorem.

**Coordinate before building.** `exists_totallyNegative_sub_one_mem_of_even_nrRealPlaces`
in `Fermat/FLT/Modularity/KhareWintenberger.lean` is separately owned and needs
RAY class groups, ray class fields, their Artin map and the quadratic Hilbert
symbol. Whoever builds class field theory for either leaf should build it once,
in THIS file (generalising `relNormClassSubgroup` to a modulus), and both
should cite it.

**The check that would refute this leaf**: a number field `K` and a subgroup
`N ≤ Cl(𝓞 K)` for which no finite abelian extension of `K` unramified at every
finite prime and at every infinite place has norm class group exactly `N` — for
instance a `K` with `h_K > 1` admitting no everywhere-unramified extension of
degree `h_K`.

**Note on the `(_ : NumberField H)` binder.** It is REDUNDANT — it follows from
the preceding `FiniteDimensional K H` by `NumberField.of_module_finite` — and it
is present only because that is a `theorem`, not an `instance`, so
`relNormClassSubgroup K H` in the last clause has nothing to synthesise from.
Discharging it costs one `exact NumberField.of_module_finite`; do not read it as
an extra obligation. -/
theorem exists_classField_of_subgroup (N : Subgroup (ClassGroup (𝓞 K))) :
    ∃ (H : IntermediateField K (AlgebraicClosure K))
      (_ : FiniteDimensional K H) (_ : NumberField H) (_ : IsGalois K H)
      (_ : IsUnramifiedAtInfinitePlaces K H),
      (∀ a b : H ≃ₐ[K] H, a * b = b * a) ∧
      (∀ (Q : Ideal (𝓞 H)) (_ : Q.IsPrime), Q ≠ ⊥ →
        Algebra.IsUnramifiedAt (𝓞 K) Q) ∧
      relNormClassSubgroup K H = N := by
  classical
  obtain ⟨HCF, hfd, hnf, habgal, hinf, hunrHCF, Art, hdict⟩ :=
    exists_hilbertClassField_artinIso K
  -- The class field of `N`: the fixed field, inside the Hilbert class field, of the
  -- subgroup of `Gal(HCF/K)` that `N` becomes under the Artin isomorphism.
  set G : ClassGroup (𝓞 K) →* (HCF ≃ₐ[K] HCF) := (Art : ClassGroup (𝓞 K) →* (HCF ≃ₐ[K] HCF))
  set F : IntermediateField K HCF := IntermediateField.fixedField (N.map G)
  have hle : IntermediateField.lift F ≤ HCF := IntermediateField.lift_le F
  letI : Algebra (IntermediateField.lift F) HCF :=
    (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower K (IntermediateField.lift F) HCF :=
    IsScalarTower.of_algebraMap_eq' (IntermediateField.inclusion hle).comp_algebraMap.symm
  haveI : FiniteDimensional K (IntermediateField.lift F) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).injective
  haveI : NumberField (IntermediateField.lift F) :=
    NumberField.of_module_finite K (IntermediateField.lift F)
  haveI : IsAbelianGalois K (IntermediateField.lift F) :=
    IsAbelianGalois.of_algHom (IntermediateField.inclusion hle)
  haveI : Module.Finite (IntermediateField.lift F) HCF :=
    Module.Finite.of_restrictScalars_finite K _ _
  haveI : Algebra.IsAlgebraic (IntermediateField.lift F) HCF := Algebra.IsAlgebraic.of_finite _ _
  haveI : IsUnramifiedAtInfinitePlaces K (IntermediateField.lift F) :=
    IsUnramifiedAtInfinitePlaces.bot K (IntermediateField.lift F) HCF
  refine ⟨IntermediateField.lift F, inferInstance, inferInstance, inferInstance, inferInstance,
    fun a b => mul_comm' a b, ?_, ?_⟩
  · -- unramified at every finite prime: descend from `HCF` along the tower
    intro q hq hq0
    haveI := hq
    obtain ⟨Q, hQ, hQover⟩ :=
      q.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 HCF)
        (by
          have hinj : Function.Injective
              (algebraMap (𝓞 (IntermediateField.lift F)) (𝓞 HCF)) :=
            FaithfulSMul.algebraMap_injective _ _
          simp [(RingHom.injective_iff_ker_eq_bot _).mp hinj])
    haveI := hQ
    haveI : Q.LiesOver q := ⟨hQover.symm⟩
    haveI : Algebra.IsUnramifiedAt (𝓞 K) Q :=
      hunrHCF Q hQ (Ideal.ne_bot_of_liesOver_of_ne_bot hq0 Q)
    exact Algebra.IsUnramifiedAt.of_liesOver (𝓞 K) q Q
  · -- the norm class group is exactly `N`, by the Galois correspondence
    rw [hdict F inferInstance, IntermediateField.fixingSubgroup_fixedField (N.map G),
      Subgroup.comap_map_eq_self_of_injective Art.injective]

variable (L : Type*) [Field L] [NumberField L] [Algebra K L]

/-- **THE ARTIN MAP AT MODULUS `1`, IN THE DIRECTION `Gal(L/K) ↠ Cl(𝓞 K)/N`: for
`L/K` finite abelian and unramified at every finite prime there is a SURJECTIVE
homomorphism `Gal(L/K) →* Cl(𝓞 K) ⧸ relNormClassSubgroup K L`** (SORRY LEAF, cut
2026-07-30 out of `index_relNormClassSubgroup_le_finrank` below, which is now
proven from it by counting).

This is the mirror image of the cut the companion file made on 2026-07-28, where
`finrank_le_index_relNormClassSubgroup` was reduced to
`exists_surjective_classGroupHom_aut_of_unramified_abelian` — the surjection
`Cl(𝓞 K) ↠ Gal(L/K)`. **The two nodes are genuinely different theorems and
neither implies the other**: that one is FALSE for extensions ramified at an
infinite place (its docstring records `K = ℚ(√3)`, `h = 1`, narrow `h⁺ = 2`), and
this one is true for all of them — which is exactly why
`IsUnramifiedAtInfinitePlaces` must NOT be added here (see the ⚠ note on the
consumer below).

**Soundness — the intended inhabitant.** Let `𝐇` be the Hilbert class field of
`K` and `Art : Cl(𝓞 K) ≃ Gal(𝐇/K)` the Artin isomorphism. Both `𝐇/K` and `L/K`
are Galois, so `M := 𝐇 ∩ L` is Galois over `K`, and the class field
correspondence identifies `Art (N_{L/K} Cl(𝓞 L)) = Gal(𝐇/M)`, i.e.
`Cl(𝓞 K) ⧸ relNormClassSubgroup K L ≃ Gal(M/K)`. Since `M ⊆ L`, restriction
`Gal(L/K) ↠ Gal(M/K)` is surjective, and `ψ` is that restriction followed by the
inverse of the isomorphism above. Note the two inclusions in
`Art (N_{L/K} Cl(𝓞 L)) = Gal(𝐇/M)` are of very different depth: `≤` is the
Frobenius computation `Frob_𝔭^{f(𝔓/𝔭)} = 1`, while `≥` is Chebotarev applied to
`𝐇L/L`. It is the second one that makes this a genuine theorem of class field
theory rather than bookkeeping — an arbitrary subgroup of `Cl(𝓞 K)` is not the
norm group of anything, and the whole content is that the norm classes of `L`
already fill up `Art⁻¹ Gal(𝐇/(𝐇 ∩ L))`.

**Why a MONOID HOM and not merely a surjective function — this is the whole point
of the cut.** A surjective FUNCTION `Gal(L/K) → Cl(𝓞 K) ⧸ N` exists if and only
if the cardinality inequality below holds, so stating the node with a bare
function would make it logically equivalent to its own consumer and the
"decomposition" would be empty. Asking for a group homomorphism is strictly
stronger, it is what the Artin map actually is, and it is what makes the
consumer's proof three lines of counting.

**PINNING.** Only surjectivity is used, and the inequality below follows from ANY
surjective hom, so an adversary who post-composes an automorphism of the
quotient, or produces a different surjection, still yields a true consumer. The
intended `ψ` is the inverse Artin map and is canonical; asking for more (that `ψ`
send `Frob_𝔭` to the class of `𝔭`) would make the leaf harder without helping the
consumer, exactly as recorded for the companion file's sibling node.

**⚠ NEITHER HYPOTHESIS IS LOAD-BEARING** — the argument above never used them:
`M/K` is Galois whether or not `L/K` is abelian, and enlarging the modulus by the
ramified finite primes handles ramification (see the consumer's own audit, which
records `K = ℚ`, `L = ℚ(√5)`, index `1 ≤ 2` as the sanity check). They are kept
because every consumer already holds them, because the consumer's statement has
them, and because a prover who has the companion file's node in hand can then
reuse the same modulus. A prover who finds the general statement no harder is
free to prove that and specialise.

**Route.** Neukirch VI (7.3) and (6.9); Childress ch. 5; Lang *ANT* ch. X. The
mathlib survey in the companion file's
`exists_surjective_classGroupHom_aut_of_unramified_abelian` applies verbatim: ray
class groups, the Hilbert class field, the Artin map, reciprocity and Chebotarev
are all absent from this pin and from `~/cs/FLT`, so the correspondence must be
built. Whoever builds it should look at all three leaves of this cluster at once
— they are three faces of one theorem.

**The check that would refute it**: a finite abelian extension `L/K` of number
fields, unramified at every finite prime, for which no group homomorphism
`Gal(L/K) → Cl(𝓞 K) ⧸ relNormClassSubgroup K L` is surjective — equivalently
(by the counting below) one with `(relNormClassSubgroup K L).index > [L : K]`. -/
theorem exists_surjective_aut_classGroupQuotient [IsGalois K L]
    (habel : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (hunr : ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) Q) :
    ∃ ψ : (L ≃ₐ[K] L) →* ClassGroup (𝓞 K) ⧸ relNormClassSubgroup K L,
      Function.Surjective ψ :=
  sorry

/-- **THE FIRST INEQUALITY AT MODULUS `1`: for `L/K` finite abelian,
`[I_K : P_K · N_{L/K} I_L] ≤ [L : K]`** (cut 2026-07-29 out of
`exists_unramifiedAbelian_primePow_dvd_finrank_of_dvd` in
`Fermat/FLT/Modularity/Interface.lean`; PROVEN 2026-07-30 from
`exists_surjective_aut_classGroupQuotient` above by counting, and from nothing
else).

**The step performed here.** `Subgroup.index` IS `Nat.card` of the quotient by
definition, a surjection cannot increase `Nat.card` on a finite source
(`Nat.card_le_card_of_surjective`, applicable because `Gal(L/K)` is finite), and
`IsGalois.card_aut_eq_finrank` turns `Nat.card Gal(L/K)` into `[L : K]`. All the
mathematics is in the leaf above; nothing here is specific to number fields.

This is the direction OPPOSITE to the companion file's
`finrank_le_index_relNormClassSubgroup`, and the two together say that the norm
index equals the degree. The upper bound alone cannot produce a class field;
this is the inequality that converts "the norm class group of `H` is `⊥`" into
"`[H : K]` is at least `h_K`", which is exactly the content that the existence
statement above would be useless without.

**Soundness.** Choose the modulus `𝔪 = ∏_{v real} v`, which is admissible for
every finite abelian `L/K` unramified at the finite primes (and, with a finite
part added, for every finite abelian `L/K` whatsoever). Artin reciprocity gives
a surjection `I_K(𝔪) ↠ Gal(L/K)` whose kernel contains `P_K^{𝔪,1}` and
`N_{L/K} I_L`. Since `P_K^{𝔪,1} ≤ P_K`, the group `I_K/(P_K · N_{L/K} I_L)` —
whose order is `(relNormClassSubgroup K L).index` — is a further QUOTIENT of
`Gal(L/K)`, so its order divides, in particular does not exceed, `[L : K]`.

**⚠ NEITHER HYPOTHESIS IS LOAD-BEARING, and that is deliberate — read this
before "strengthening" the leaf.** The inequality is true without `habel` (the
norm index only ever sees the abelianization, so
`index ≤ |Gal(L/K)^{ab}| ≤ [L : K]`) and without any unramifiedness at all
(enlarge the modulus by the ramified finite primes; the argument above is
unchanged, because `P_K^{𝔪,1} ≤ P_K` for every modulus `𝔪`). Sanity check of
the ramified case: `K = ℚ`, `L = ℚ(√5)` is ramified at `5`, and
`(relNormClassSubgroup ℚ L).index = 1 ≤ 2`. Both hypotheses are nevertheless
kept, for two reasons: every consumer already holds them, and they let a prover
who has `exists_surjective_classGroupHom_aut_of_unramified_abelian` in hand
reuse the same modulus. A prover who finds the general statement no harder is
free to prove it and specialise — that is a strict improvement, not a change of
statement. **Do not, however, ADD `IsUnramifiedAtInfinitePlaces` here**: the
glue below applies this leaf and the companion file's opposite inequality to
the SAME `H`, and while the companion's needs that instance, this one must not,
or the asymmetry recorded in the companion file (`ℚ(√3)`, `h = 1`, `h⁺ = 2`)
would be lost from the record.

**Why this is not the same theorem as the companion's leaf.** The companion's
`exists_surjective_classGroupHom_aut_of_unramified_abelian` asks for a
surjection `Cl(𝓞 K) ↠ Gal(L/K)`; this leaf asks for the surjection the other
way, `Gal(L/K) ↠ Cl(𝓞 K) ⧸ relNormClassSubgroup K L`. Under full reciprocity
both are the Artin map and the two are inverse isomorphisms, but as separate
statements neither implies the other: the first is false for extensions
ramified at an infinite place, the second is true for all of them.

**Route.** Neukirch VI (7.3) and (6.9); Childress ch. 5; Lang *ANT* ch. X.

**The check that would refute it**: a finite abelian extension `L/K` of number
fields with `(relNormClassSubgroup K L).index > [L : K]` — equivalently, a norm
index exceeding the degree. -/
theorem index_relNormClassSubgroup_le_finrank [IsGalois K L]
    (habel : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (hunr : ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) Q) :
    (relNormClassSubgroup K L).index ≤ Module.finrank K L := by
  obtain ⟨ψ, hψ⟩ := exists_surjective_aut_classGroupQuotient K L habel hunr
  calc (relNormClassSubgroup K L).index
      = Nat.card (ClassGroup (𝓞 K) ⧸ relNormClassSubgroup K L) := rfl
    _ ≤ Nat.card (L ≃ₐ[K] L) := Nat.card_le_card_of_surjective _ hψ
    _ = Module.finrank K L := IsGalois.card_aut_eq_finrank K L

/-- **THE CLASS FIELD OF A SUBGROUP HAS DEGREE ITS INDEX: for every subgroup
`N ≤ Cl(𝓞 K)` there is a finite abelian extension of `K`, unramified at every
finite prime, with `[H : K] = N.index`** (PROVEN 2026-07-29 from
`exists_classField_of_subgroup` and `index_relNormClassSubgroup_le_finrank`
above together with `finrank_le_index_relNormClassSubgroup` of the companion
file, and from nothing else).

This is the numerical content of the class field correspondence at modulus `1`.
The existence leaf supplies `H` with norm class group `N`; the two inequalities
— one from each file — pin `[H : K]` to `N.index` by `le_antisymm`.

The `IsUnramifiedAtInfinitePlaces` instance produced by the existence leaf is
CONSUMED here (it is what makes the companion's inequality applicable) and is
deliberately NOT re-exported: the consumers in `Modularity/Interface.lean` ask
only for unramifiedness at the finite primes, and re-exporting it would make
this statement harder to satisfy for no gain. -/
theorem exists_classField_finrank_eq_index (N : Subgroup (ClassGroup (𝓞 K))) :
    ∃ (H : IntermediateField K (AlgebraicClosure K))
      (_ : FiniteDimensional K H) (_ : IsGalois K H),
      (∀ a b : H ≃ₐ[K] H, a * b = b * a) ∧
      (∀ (Q : Ideal (𝓞 H)) (_ : Q.IsPrime), Q ≠ ⊥ →
        Algebra.IsUnramifiedAt (𝓞 K) Q) ∧
      Module.finrank K H = N.index := by
  obtain ⟨H, hfd, hnf, hgal, hinf, habel, hunr, hnorm⟩ :=
    exists_classField_of_subgroup K N
  refine ⟨H, hfd, hgal, habel, hunr, le_antisymm ?_ ?_⟩
  · have h := finrank_le_index_relNormClassSubgroup K H habel hunr
    rwa [hnorm] at h
  · have h := index_relNormClassSubgroup_le_finrank K H habel hunr
    rwa [hnorm] at h

/-- **THE HILBERT CLASS FIELD EXISTS: a number field `K` has a finite abelian
extension, unramified at every finite prime, of degree exactly `h_K`** (PROVEN
2026-07-29 as the case `N = ⊥` of `exists_classField_finrank_eq_index` above).

`Subgroup.index_bot` turns `(⊥ : Subgroup (ClassGroup (𝓞 K))).index` into
`Nat.card (ClassGroup (𝓞 K))`. Together with the companion file's
`finrank_le_card_classGroup_of_unramified_abelian_of_isUnramifiedAtInfinitePlaces`
this says that `h_K` is EXACTLY the largest degree available, i.e. that the
extension produced here is the Hilbert class field.

Note the degree is an EQUALITY, which is strictly stronger than what the
consumer in `Modularity/Interface.lean` needs (divisibility by the `ℓ`-part of
`h_K`); the equality is what the correspondence gives, and weakening it here
would only hide the fact. -/
theorem exists_hilbertClassField :
    ∃ (H : IntermediateField K (AlgebraicClosure K))
      (_ : FiniteDimensional K H) (_ : IsGalois K H),
      (∀ a b : H ≃ₐ[K] H, a * b = b * a) ∧
      (∀ (Q : Ideal (𝓞 H)) (_ : Q.IsPrime), Q ≠ ⊥ →
        Algebra.IsUnramifiedAt (𝓞 K) Q) ∧
      Module.finrank K H = Nat.card (ClassGroup (𝓞 K)) := by
  simpa only [Subgroup.index_bot] using exists_classField_finrank_eq_index K ⊥

end NumberField
