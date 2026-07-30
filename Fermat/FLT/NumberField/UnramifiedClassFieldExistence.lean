/-
NumberField/UnramifiedClassFieldExistence.lean — own work for the Fermat
project (not vendored from the FLT project).
-/
module

public import Fermat.FLT.NumberField.UnramifiedClassFieldBound

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

* `NumberField.exists_classField_of_subgroup` — **OPEN LEAF.** The existence
  theorem at modulus `1`: every subgroup of `Cl(𝓞 K)` is the norm class group
  of a finite abelian extension unramified at every finite prime and at every
  infinite place. This is where the class field theory is.
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
-/

@[expose] public section

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- **THE EXISTENCE THEOREM OF UNRAMIFIED CLASS FIELD THEORY, AT MODULUS `1`:
every subgroup `N` of `Cl(𝓞 K)` is the norm class group of a finite abelian
extension of `K` unramified at every finite prime and at every infinite place**
(SORRY LEAF, cut 2026-07-29 out of
`exists_unramifiedAbelian_primePow_dvd_finrank_of_dvd` in
`Fermat/FLT/Modularity/Interface.lean`).

**THIS IS WHERE THE CLASS FIELD THEORY IN THIS CLUSTER NOW LIVES**, together
with `exists_surjective_classGroupHom_aut_of_unramified_abelian` in the
companion file (which is the RECIPROCITY direction). Everything else in the
Hilbert-class-field cluster — `exists_classField_finrank_eq_index` and
`exists_hilbertClassField` below, and the whole divisibility half in
`Modularity/Interface.lean` — is proven over this statement, over
`index_relNormClassSubgroup_le_finrank` below, and over the companion file's
`finrank_le_index_relNormClassSubgroup`.

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
      relNormClassSubgroup K H = N :=
  sorry

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
