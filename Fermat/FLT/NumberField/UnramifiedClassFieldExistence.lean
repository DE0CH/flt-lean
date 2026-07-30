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

* `NumberField.restrictNormalHom_frobAt` and `NumberField.restrictScalars_frobAt` —
  PROVEN 2026-07-30. Frobenius in a tower `K ⊆ M ⊆ L`: it restricts to the Frobenius of
  `M/K` below, and the Frobenius of `L/M` is `Frob_{L/K} ^ f(q | 𝓞 K)`. These are the two
  halves of the class field DICTIONARY, and they are pure ramification theory. They
  belong upstream in `ArtinSymbol.lean`; see their docstrings.
* `NumberField.exists_unramifiedAbelian_card_classGroup_le_finrank` — **OPEN LEAF, and
  it is now the ONLY missing input of the Hilbert-class-field half of this file.** The
  EXISTENCE theorem, alone: `K` has an abelian extension inside `AlgebraicClosure K`,
  unramified at every finite prime and at every infinite place, of degree at least `h_K`
  (hence, by the companion file's upper bound, exactly `h_K`). Cut 2026-07-30 out of the
  Artin-isomorphism node below.
* `NumberField.exists_hilbertClassField_artinIso` — **PROVEN 2026-07-30** from the
  existence leaf above and from `ArtinSymbol.lean`'s two leaves (RECIPROCITY and
  CHEBOTAREV), and from nothing else. Unramified class field theory at modulus `1` in one
  statement: the Hilbert class field exists inside `AlgebraicClosure K`, the Artin map is
  an isomorphism `Cl(𝓞 K) ≃ Gal(HCF/K)`, and the norm class group of an intermediate
  field is the subgroup fixing it. The isomorphism is surjectivity (Chebotarev) plus
  counting against the existence leaf; the dictionary is the two Frobenius tower lemmas,
  with Chebotarev applied a second time — to `HCF/F` rather than to `HCF/K` — for the
  inclusion that says the norm classes FILL UP the fixing subgroup.
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

**Read that file before attacking either leaf below.** Its two leaves, plus the
EXISTENCE leaf here, are now exactly the input of `exists_hilbertClassField_artinIso`.
But note carefully that they are NOT enough for
`index_relNormClassSubgroup_le_finrank`: all three are stated at modulus `1`, i.e. under
`IsUnramifiedAtInfinitePlaces`, and that leaf deliberately does NOT assume it. See
`exists_surjective_aut_classGroupQuotient`'s docstring for what is needed instead.

## Dependency direction inside this file — do not reverse it (2026-07-30)

`exists_hilbertClassField_artinIso` does NOT use
`exists_surjective_aut_classGroupQuotient`. That is deliberate and was paid for: an
earlier version of its proof got the `≥` half of the dictionary by counting, out of that
leaf, and the Chebotarev-over-`F` route was written precisely to remove the dependence.
The reason is that the natural route to that leaf runs through the `HCF` produced here
(intersect `L` with it), so a dependency in this direction would close a cycle. If you
prove that leaf, you may freely use everything in this file.
-/

@[expose] public section

open scoped nonZeroDivisors

namespace NumberField

section FrobeniusTower

variable (K M L : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
  [Field L] [NumberField L] [Algebra K M] [Algebra M L] [Algebra K L]
  [IsScalarTower K M L] [IsGalois K L] [IsGalois K M]

/-- **FROBENIUS RESTRICTS TO FROBENIUS: in a tower `K ⊆ M ⊆ L` of number fields with
`L/K` and `M/K` Galois, the restriction to `M` of the Frobenius at a maximal ideal `Q`
of `𝓞 L` is the Frobenius at the prime `q = Q ∩ 𝓞 M` below it** (PROVEN 2026-07-30).

Pure ramification theory, and proven exactly like `frobAt_pow_inertiaDeg`: the algebra
map `𝓞 M → 𝓞 L` intertwines `σ|_M` with `σ` (`AlgEquiv.restrictNormal_commutes`), and
the two Frobenius congruences use the SAME residue cardinality because
`(Q ∩ 𝓞 M) ∩ 𝓞 K = Q ∩ 𝓞 K` (`Ideal.under_under`) — so `σ|_M` is an arithmetic
Frobenius at `q`. The Frobenius at an unramified prime is unique
(`AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt`) and the action of `Gal(M/K)` on `𝓞 M` is
faithful (`eq_one_of_smul_eq_self`), which turns that into an equality in `Gal(M/K)`.

**Unramifiedness of `q` over `𝓞 K` is load-bearing**: it is what makes the Frobenius at
`q` unique. At a ramified `q`, `arithFrobAt` makes an arbitrary choice inside the coset
of the inertia group and the two sides differ by an element of it — the same phenomenon
recorded on `frobAt_pow_inertiaDeg`, with the same `K = ℚ`, `L = ℚ(i)`, `Q = (1 + i)`
witness.

Together with `restrictScalars_frobAt` below this is the Frobenius half of the class
field DICTIONARY: this one gives the `≤` inclusion (norm classes fix the intermediate
field), that one gives the `≥` inclusion (the norm classes fill it up).

**Placement.** This belongs upstream beside `frobAt` in
`Fermat/FLT/NumberField/ArtinSymbol.lean`; it is stated here only because that file's
two open leaves are separately owned and a cross-file edit costs a release cycle. Move
it when that file is next touched. -/
theorem restrictNormalHom_frobAt (Q : Ideal (𝓞 L)) [Q.IsMaximal] (q : Ideal (𝓞 M))
    [q.IsMaximal] [Algebra.IsUnramifiedAt (𝓞 K) q] (hq : Q.under (𝓞 M) = q) :
    AlgEquiv.restrictNormalHom M (frobAt K L Q) = frobAt K M q := by
  classical
  set σ : L ≃ₐ[K] L := frobAt K L Q with hσdef
  set τ : M ≃ₐ[K] M := AlgEquiv.restrictNormalHom M σ with hτdef
  have H : IsArithFrobAt (𝓞 K) σ Q := isArithFrobAt_frobAt K L Q
  -- the algebra map `𝓞 M → 𝓞 L` intertwines `τ` and `σ`
  have hint : ∀ x : 𝓞 M, algebraMap (𝓞 M) (𝓞 L) (τ • x) = σ • algebraMap (𝓞 M) (𝓞 L) x := by
    intro x
    have hinj : Function.Injective (algebraMap (𝓞 L) L) :=
      FaithfulSMul.algebraMap_injective (𝓞 L) L
    refine hinj ?_
    show algebraMap M L ((τ • x : 𝓞 M) : M) = σ (algebraMap M L (x : M))
    rw [coe_smul_ringOfIntegers]
    exact AlgEquiv.restrictNormal_commutes σ M (x : M)
  -- so `τ` is an arithmetic Frobenius at `q`
  have Hτ : IsArithFrobAt (𝓞 K) τ q := by
    intro x
    have hcard : Nat.card (𝓞 K ⧸ q.under (𝓞 K)) = Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) := by
      rw [← hq, Ideal.under_under]
    show τ • x - x ^ Nat.card (𝓞 K ⧸ q.under (𝓞 K)) ∈ q
    rw [hcard, ← hq, Ideal.mem_under, map_sub, map_pow, hint x]
    exact H (algebraMap (𝓞 M) (𝓞 L) x)
  -- uniqueness of the Frobenius at the unramified prime `q`, then faithfulness
  have heq := Hτ.eq_of_isUnramifiedAt (isArithFrobAt_frobAt K M q)
    (Ideal.primeCompl_le_nonZeroDivisors q)
  have hsmul : ∀ x : 𝓞 M, τ • x = frobAt K M q • x := fun x => DFunLike.congr_fun heq x
  have hone : τ * (frobAt K M q)⁻¹ = 1 := by
    refine eq_one_of_smul_eq_self _ fun y => ?_
    rw [mul_smul, hsmul ((frobAt K M q)⁻¹ • y), smul_inv_smul]
  rwa [mul_inv_eq_one] at hone

/-- **THE FROBENIUS OF THE UPPER LAYER IS A POWER OF THE FROBENIUS OF THE WHOLE TOWER:
in a tower `K ⊆ M ⊆ L` as above, `Frob_{L/M, Q} = Frob_{L/K, Q} ^ f(q | 𝓞 K)`, where
`q = Q ∩ 𝓞 M`** (PROVEN 2026-07-30).

This is the identity that converts CHEBOTAREV for `L/M` into a statement about the norm
classes of `M` over `K`: the class of `N_{M/K} q` is sent by the Artin map of `L/K` to
`Frob_{L/K, Q} ^ f(q | 𝓞 K)` (because `N_{M/K} q = 𝔭 ^ f`), and by this lemma that
element IS `Frob_{L/M, Q}`. So the image of the norm classes contains every Frobenius of
`L/M`, hence — by Chebotarev — all of `Gal(L/M)`.

**Chain.** `Frob_{L/K, Q} ^ f` fixes `M` pointwise, by `restrictNormalHom_frobAt` above
and `frobAt_pow_inertiaDeg`; so it is an `M`-algebra automorphism of `L`
(`AlgEquiv.ofRingEquiv`). Its Frobenius congruence over `𝓞 M` is the `f`-fold iterate of
its congruence over `𝓞 K`, and the two exponents agree because
`#(𝓞 M / q) = #(𝓞 K / 𝔭) ^ f` (`Ideal.cardQuot_pow_inertiaDeg`). Uniqueness at the
unramified `Q` and faithfulness finish, exactly as above.

**Both unramifiedness hypotheses are load-bearing** — `Q` over `𝓞 M` for the uniqueness
step here, `q` over `𝓞 K` for the appeal to `restrictNormalHom_frobAt`. -/
theorem restrictScalars_frobAt [IsGalois M L] (Q : Ideal (𝓞 L)) [Q.IsMaximal]
    [Algebra.IsUnramifiedAt (𝓞 M) Q] (q : Ideal (𝓞 M)) [q.IsMaximal]
    [Algebra.IsUnramifiedAt (𝓞 K) q] (hq : Q.under (𝓞 M) = q) :
    AlgEquiv.restrictScalars K (frobAt M L Q) = frobAt K L Q ^ q.inertiaDeg (𝓞 K) := by
  classical
  set σ : L ≃ₐ[K] L := frobAt K L Q with hσdef
  set f : ℕ := q.inertiaDeg (𝓞 K) with hfdef
  set c : ℕ := Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) with hcdef
  have H : IsArithFrobAt (𝓞 K) σ Q := isArithFrobAt_frobAt K L Q
  have hmk : ∀ y : 𝓞 L, Ideal.Quotient.mk Q (σ • y) = (Ideal.Quotient.mk Q y) ^ c :=
    fun y ↦ H.mk_apply y
  have key : ∀ (k : ℕ) (x : 𝓞 L),
      Ideal.Quotient.mk Q ((σ ^ k) • x) = (Ideal.Quotient.mk Q x) ^ (c ^ k) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        rw [pow_succ', mul_smul, hmk, ih, ← pow_mul, ← pow_succ]
  -- `σ ^ f` fixes `M` pointwise, so it is an `M`-algebra automorphism of `L`
  have hfix : AlgEquiv.restrictNormalHom M (σ ^ f) = 1 := by
    rw [map_pow, restrictNormalHom_frobAt K M L Q q hq, hfdef]
    exact frobAt_pow_inertiaDeg K M q
  have hcomm : ∀ x : M, (σ ^ f).toRingEquiv (algebraMap M L x) = algebraMap M L x := by
    intro x
    have h := AlgEquiv.restrictNormal_commutes (σ ^ f) M x
    rw [show (σ ^ f).restrictNormal M = AlgEquiv.restrictNormalHom M (σ ^ f) from rfl, hfix,
      AlgEquiv.one_apply] at h
    exact h.symm
  set ρ : L ≃ₐ[M] L := AlgEquiv.ofRingEquiv hcomm with hρdef
  have hρsmul : ∀ x : 𝓞 L, ρ • x = (σ ^ f) • x := fun x ↦ Subtype.ext rfl
  -- `ρ` is an arithmetic Frobenius at `Q` over `𝓞 M`
  have Hρ : IsArithFrobAt (𝓞 M) ρ Q := by
    intro x
    have hunder : Q.under (𝓞 K) = q.under (𝓞 K) := by rw [← hq, Ideal.under_under]
    have hcard : Nat.card (𝓞 M ⧸ Q.under (𝓞 M)) = c ^ f := by
      rw [hq, hcdef, hunder, hfdef, ← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply]
      exact (Ideal.cardQuot_pow_inertiaDeg (q.under (𝓞 K)) q).symm
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
    show Ideal.Quotient.mk Q (ρ • x) = _
    rw [hcard, hρsmul x, key f x, map_pow]
  -- uniqueness of the Frobenius at the unramified prime `Q`, then faithfulness
  have heq := Hρ.eq_of_isUnramifiedAt (isArithFrobAt_frobAt M L Q)
    (Ideal.primeCompl_le_nonZeroDivisors Q)
  have hsmul : ∀ x : 𝓞 L, ρ • x = frobAt M L Q • x := fun x ↦ DFunLike.congr_fun heq x
  have hone : ρ * (frobAt M L Q)⁻¹ = 1 := by
    refine eq_one_of_smul_eq_self _ fun y ↦ ?_
    rw [mul_smul, hsmul ((frobAt M L Q)⁻¹ • y), smul_inv_smul]
  rw [mul_inv_eq_one] at hone
  rw [← hone]
  rfl

end FrobeniusTower

variable (K : Type*) [Field K] [NumberField K]

/-- **THE EXISTENCE THEOREM OF UNRAMIFIED CLASS FIELD THEORY, IN THE ONLY FORM THE ARTIN
ISOMORPHISM NEEDS: `K` has a finite ABELIAN extension inside `AlgebraicClosure K`,
unramified at every finite prime and at every infinite place, of degree AT LEAST `h_K`**
(SORRY LEAF, cut 2026-07-30 out of `exists_hilbertClassField_artinIso` below, which is
now PROVEN from it, from `exists_classGroupHom_eq_frobAt` (RECIPROCITY) and
`closure_frobAt_eq_top` (CHEBOTAREV) of `Fermat/FLT/NumberField/ArtinSymbol.lean`, and
from nothing else).

**THIS IS NOW THE WHOLE REMAINING GAP in the Hilbert-class-field half of this cluster**,
and it is the classical EXISTENCE theorem and nothing else: no Artin map, no dictionary,
no intermediate fields. Everything the old leaf also demanded — that the Artin map is an
isomorphism, and that the norm class group of an intermediate field is the subgroup
fixing it, in BOTH directions — is now derived, over this statement and the two
ArtinSymbol leaves, in `exists_hilbertClassField_artinIso` below.

**The degree is automatically EXACT, so `≥` costs nothing and buys everything.** The
companion file's
`finrank_le_card_classGroup_of_unramified_abelian_of_isUnramifiedAtInfinitePlaces` gives
`[HCF : K] ≤ h_K` for free from the hypotheses already listed here, so any witness has
`[HCF : K] = h_K` — this really is the Hilbert class field. Stating the inequality in the
`≥` direction is deliberate: it is the direction that is hard, and a prover never has to
produce the other one.

**Soundness — the intended inhabitant.** `HCF` is the maximal abelian extension of `K`
inside `AlgebraicClosure K` unramified at every finite prime and at every infinite place;
its degree is `h_K` by unramified class field theory at modulus `1`.

**PINNING.** An adversary cannot take `HCF = K` unless `h_K = 1`: the degree clause
forces `[HCF : K] ≥ h_K`, and with the companion's upper bound the extension produced is
of degree exactly the class number. There is nothing else to pin — the four instance
clauses and the finite-prime clause are the hypotheses of that upper bound, and the
consumer uses only them.

**⚠ `IsUnramifiedAtInfinitePlaces K HCF` IS LOAD-BEARING and must not be dropped.**
Without it the companion's `finrank_le_index_relNormClassSubgroup` is FALSE
(`K = ℚ(√3)` has `h_K = 1` but narrow class number `2`), the degree is no longer pinned
to `h_K`, and the consumer's appeal to reciprocity — which is stated at modulus `1`, i.e.
under exactly this hypothesis — is no longer available. Equivalently, `1` is an
admissible modulus only for extensions unramified at the archimedean places too, and this
is the SMALL (wide) Hilbert class field, not the narrow one.

**Non-vacuity.** For `K = ℚ(√-5)` (`h_K = 2`) the leaf demands a quadratic extension
unramified at every finite prime and at every infinite place — `ℚ(√-5, i)` — which is not
`K`. It is trivial exactly when `h_K = 1`.

**Route.** Neukirch VI (6.9) and (7.3) and the sections preceding them; Childress
ch. 4–5; Lang *ANT* ch. X; Cassels–Fröhlich ch. VII–VIII. The classical proof reduces to
a congruence subgroup of prime exponent, adjoins `ζ_ℓ`, runs Kummer theory over `K(ζ_ℓ)`
and descends by the translation theorem (Verschiebungssatz) — a descent of NORM GROUPS,
which is why the correspondence below is phrased in norm groups. **Do not re-cut the
naive "descend an unramified abelian extension from `K(ζ_ℓ)`" leaf**: it is FALSE, with
the PARI/GP witness recorded on `exists_classField_of_subgroup` below (`K = ℚ(√29)`,
`h = h⁺ = 1`, `h(K(ζ_3)) = 3`).

**The check that would refute this leaf**: a number field `K` admitting no abelian
extension of degree `≥ h_K` unramified at every finite prime and at every infinite place
— equivalently, one whose wide Hilbert class field has degree `< h_K`. -/
theorem exists_unramifiedAbelian_card_classGroup_le_finrank :
    ∃ (HCF : IntermediateField K (AlgebraicClosure K)) (_ : FiniteDimensional K HCF)
      (_ : NumberField HCF) (_ : IsAbelianGalois K HCF)
      (_ : IsUnramifiedAtInfinitePlaces K HCF),
      (∀ (Q : Ideal (𝓞 HCF)) (_ : Q.IsPrime), Q ≠ ⊥ →
        Algebra.IsUnramifiedAt (𝓞 K) Q) ∧
      Nat.card (ClassGroup (𝓞 K)) ≤ Module.finrank K HCF :=
  sorry

/-- **UNRAMIFIED CLASS FIELD THEORY AT MODULUS `1`, IN ONE STATEMENT: the Hilbert
class field `HCF` of `K` exists inside `AlgebraicClosure K`, the Artin map is an
ISOMORPHISM `Cl(𝓞 K) ≃ Gal(HCF/K)`, and under it the norm class group of every
intermediate field is exactly the subgroup fixing that field** (was this file's central
SORRY LEAF; DECOMPOSED AND PROVEN 2026-07-30 from
`exists_unramifiedAbelian_card_classGroup_le_finrank` above — the EXISTENCE theorem — and
from `exists_classGroupHom_eq_frobAt` (RECIPROCITY) and `closure_frobAt_eq_top`
(CHEBOTAREV) in `Fermat/FLT/NumberField/ArtinSymbol.lean`, and from nothing else).

It is the canonical form — Neukirch VI (6.9), the theorem that "the ideal group belonging
to `H` is `P_K · N_{H/K} I_H`" — rather than the "for every subgroup `N` there exists a
field" shape it replaces: the classical proof constructs ONE field `HCF` and one map, and
then the whole correspondence is the Galois correspondence, which is exactly how the
consumer below reads.

**What was deep here, and where each piece went.** (i) `Art` is well defined on ideal
CLASSES — Artin reciprocity: `exists_classGroupHom_eq_frobAt`. (ii) `Art` is SURJECTIVE —
Chebotarev for `HCF/K`: `closure_frobAt_eq_top`, and then INJECTIVE by counting, because
the existence leaf gives `h_K ≤ [HCF : K] = #Gal(HCF/K)` while surjectivity gives the
reverse. (iii) The `≥` half of the dictionary — that the norm classes of `F` already fill
up `Art⁻¹ Gal(HCF/F)` — is Chebotarev applied to `HCF/F`, which is the SAME leaf
`closure_frobAt_eq_top` with `F` as the base field; the bridge from its Frobenius
elements to the norm classes of `F` is `restrictScalars_frobAt` above. (iv) The `≤` half
is the Frobenius computation `Frob_𝔭 ^ f(𝔓/𝔭) = 1`, i.e. `restrictNormalHom_frobAt` and
`frobAt_pow_inertiaDeg`. (v) The existence of `HCF` itself is the leaf above.

**No circularity with `exists_surjective_aut_classGroupQuotient` below, and keep it that
way.** An earlier version of this proof got the `≥` half by counting, out of that leaf;
the Chebotarev-over-`F` route replaces it, so this theorem does NOT depend on it. That
matters, because the natural way to prove that leaf is to intersect `L` with the `HCF`
produced HERE — which would be a cycle if this file's proof went the other way. Do not
reintroduce the counting shortcut.

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
              (Art : ClassGroup (𝓞 K) →* (HCF ≃ₐ[K] HCF)) := by
  classical
  obtain ⟨HCF, hfd, hnf, habgal, hinf, hunrHCF, hcard⟩ :=
    exists_unramifiedAbelian_card_classGroup_le_finrank K
  haveI := hfd; haveI := hnf; haveI := habgal; haveI := hinf
  refine ⟨HCF, hfd, hnf, habgal, hinf, hunrHCF, ?_⟩
  have habel : ∀ a b : HCF ≃ₐ[K] HCF, a * b = b * a := fun a b => mul_comm' a b
  -- ## The Artin map, and why it is an isomorphism
  obtain ⟨φ, hfrob⟩ := exists_classGroupHom_eq_frobAt K HCF habel hunrHCF
  have hunder : ∀ (Q : Ideal (𝓞 HCF)), Q.IsMaximal → Q.under (𝓞 K) ≠ ⊥ := by
    intro Q hQ
    exact Ideal.under_ne_bot (𝓞 K)
      (Ideal.bot_lt_of_maximal Q (NumberField.RingOfIntegers.not_isField HCF)).ne'
  have hsurj : Function.Surjective φ := by
    refine MonoidHom.range_eq_top.1 (top_le_iff.1 ?_)
    rw [← closure_frobAt_eq_top K HCF]
    refine (Subgroup.closure_le _).2 ?_
    rintro σ ⟨Q, hQ, -, rfl⟩
    exact ⟨ClassGroup.mk0 ⟨Q.under (𝓞 K), mem_nonZeroDivisors_of_ne_zero (hunder Q hQ)⟩,
      hfrob Q hQ _ rfl⟩
  have hcardeq : Nat.card (ClassGroup (𝓞 K)) = Nat.card (HCF ≃ₐ[K] HCF) := by
    have h1 : Nat.card (HCF ≃ₐ[K] HCF) = Module.finrank K HCF :=
      IsGalois.card_aut_eq_finrank K HCF
    have h2 : Nat.card (HCF ≃ₐ[K] HCF) ≤ Nat.card (ClassGroup (𝓞 K)) :=
      Nat.card_le_card_of_surjective _ hsurj
    omega
  have hbij : Function.Bijective φ := (Nat.bijective_iff_surjective_and_card φ).2 ⟨hsurj, hcardeq⟩
  refine ⟨MulEquiv.ofBijective φ hbij, ?_⟩
  have hcoe : ((MulEquiv.ofBijective φ hbij : ClassGroup (𝓞 K) ≃* (HCF ≃ₐ[K] HCF)) :
      ClassGroup (𝓞 K) →* (HCF ≃ₐ[K] HCF)) = φ := rfl
  rw [hcoe]
  intro F hNF
  haveI := hNF
  -- ## The intermediate field `lift F`, with the instances the dictionary needs
  have hle : IntermediateField.lift F ≤ HCF := IntermediateField.lift_le F
  letI : Algebra (IntermediateField.lift F) HCF :=
    (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower K (IntermediateField.lift F) HCF :=
    IsScalarTower.of_algebraMap_eq' (IntermediateField.inclusion hle).comp_algebraMap.symm
  haveI : FiniteDimensional K (IntermediateField.lift F) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).injective
  haveI : IsAbelianGalois K (IntermediateField.lift F) :=
    IsAbelianGalois.of_algHom (IntermediateField.inclusion hle)
  haveI : Module.Finite (IntermediateField.lift F) HCF :=
    Module.Finite.of_restrictScalars_finite K _ _
  haveI : Algebra.IsAlgebraic (IntermediateField.lift F) HCF := Algebra.IsAlgebraic.of_finite _ _
  haveI : IsUnramifiedAtInfinitePlaces K (IntermediateField.lift F) :=
    IsUnramifiedAtInfinitePlaces.bot K (IntermediateField.lift F) HCF
  have hunrM : ∀ (q : Ideal (𝓞 (IntermediateField.lift F))) (_ : q.IsPrime), q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) q := by
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
  -- ## The bridge: `fixingSubgroup F` is the kernel of restriction to `lift F`
  have hbridge : IntermediateField.fixingSubgroup F =
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := HCF)
        (IntermediateField.lift F)).ker := by
    have hinj : Function.Injective (algebraMap (IntermediateField.lift F) HCF) :=
      (algebraMap (IntermediateField.lift F) HCF).injective
    ext σ
    have hRN : AlgEquiv.restrictNormalHom (F := K) (K₁ := HCF) (IntermediateField.lift F) σ =
        σ.restrictNormal (IntermediateField.lift F) := rfl
    rw [MonoidHom.mem_ker, hRN, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro hfix
      refine AlgEquiv.ext fun y => ?_
      refine hinj ?_
      rw [AlgEquiv.restrictNormal_commutes σ (IntermediateField.lift F) y, AlgEquiv.one_apply]
      exact hfix _ ((IntermediateField.mem_lift
        (algebraMap (IntermediateField.lift F) HCF y)).1 y.2)
    · intro hker x hx
      have hx' : (x : AlgebraicClosure K) ∈ IntermediateField.lift F :=
        (IntermediateField.mem_lift x).2 hx
      have hxe : algebraMap (IntermediateField.lift F) HCF
          ⟨(x : AlgebraicClosure K), hx'⟩ = x := rfl
      have h := AlgEquiv.restrictNormal_commutes σ (IntermediateField.lift F)
        ⟨(x : AlgebraicClosure K), hx'⟩
      rw [hxe, hker, AlgEquiv.one_apply, hxe] at h
      exact h.symm
  haveI : IsGalois (IntermediateField.lift F) HCF :=
    IsGalois.tower_top_of_isGalois K (IntermediateField.lift F) HCF
  -- ## The value of the Artin map at a norm class: a power of the Frobenius
  have hkey : ∀ (q : Ideal (𝓞 (IntermediateField.lift F))) [q.IsMaximal]
      (Q : Ideal (𝓞 HCF)) [Q.IsMaximal] (J : (Ideal (𝓞 K))⁰),
      Q.under (𝓞 (IntermediateField.lift F)) = q →
      (J : Ideal (𝓞 K)) = Ideal.relNorm (𝓞 K) q →
      φ (ClassGroup.mk0 J) = (frobAt K HCF Q) ^ q.inertiaDeg (𝓞 K) := by
    intro q hqmax Q hQmax J hQq hJ
    haveI := hqmax
    haveI := hQmax
    have hq0 : q ≠ ⊥ :=
      (Ideal.bot_lt_of_maximal q (NumberField.RingOfIntegers.not_isField _)).ne'
    have hpne : q.under (𝓞 K) ≠ ⊥ := Ideal.under_ne_bot (𝓞 K) hq0
    have hunderQ : Q.under (𝓞 K) = q.under (𝓞 K) := by rw [← hQq, Ideal.under_under]
    set Jp : (Ideal (𝓞 K))⁰ :=
      ⟨q.under (𝓞 K), mem_nonZeroDivisors_of_ne_zero hpne⟩ with hJpdef
    have hJpow : J = Jp ^ q.inertiaDeg (𝓞 K) := by
      refine Subtype.ext ?_
      rw [hJ, Ideal.relNorm_eq_pow_of_isMaximal q (q.under (𝓞 K)), SubmonoidClass.coe_pow]
    rw [hJpow, map_pow, map_pow, hfrob Q hQmax Jp hunderQ.symm]
  -- ## The `≤` half: the norm classes of `lift F` fix `F`
  have hsub : relNormClassSubgroup K (IntermediateField.lift F) ≤
      Subgroup.comap φ (IntermediateField.fixingSubgroup F) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro c ⟨I, hI, rfl⟩
    refine mem_of_relNorm_of_forall_isMaximal K (IntermediateField.lift F)
      (H := Subgroup.comap φ (IntermediateField.fixingSubgroup F)) ?_ I _ rfl
    intro q J hqmax hJ
    haveI := hqmax
    have hq0 : q ≠ ⊥ :=
      (Ideal.bot_lt_of_maximal q (NumberField.RingOfIntegers.not_isField _)).ne'
    haveI : Algebra.IsUnramifiedAt (𝓞 K) q := hunrM q hqmax.isPrime hq0
    -- a prime `Q` of `𝓞 HCF` over `q`
    obtain ⟨Q, hQ, hQover⟩ :=
      q.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 HCF)
        (by
          have hinj : Function.Injective
              (algebraMap (𝓞 (IntermediateField.lift F)) (𝓞 HCF)) :=
            FaithfulSMul.algebraMap_injective _ _
          simp [(RingHom.injective_iff_ker_eq_bot _).mp hinj])
    haveI := hQ
    haveI : Q.LiesOver q := ⟨hQover.symm⟩
    have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hq0 Q
    haveI hQmax : Q.IsMaximal := hQ.isMaximal hQ0
    -- the Artin map sends that class to `Frob_Q ^ f`, which restricts to `Frob_q ^ f = 1`
    rw [Subgroup.mem_comap, hbridge, MonoidHom.mem_ker,
      hkey q Q J hQover hJ, map_pow,
      restrictNormalHom_frobAt K (IntermediateField.lift F) HCF Q q hQover]
    exact frobAt_pow_inertiaDeg K (IntermediateField.lift F) q
  -- ## The `≥` half: Chebotarev for `HCF/(lift F)` fills up the fixing subgroup
  refine le_antisymm hsub ?_
  have hge : IntermediateField.fixingSubgroup F ≤
      Subgroup.map φ (relNormClassSubgroup K (IntermediateField.lift F)) := by
    have hpush : Subgroup.map
        (AlgEquiv.restrictScalarsHom (R := K) (S := IntermediateField.lift F) (A := HCF))
        (⊤ : Subgroup (HCF ≃ₐ[IntermediateField.lift F] HCF)) ≤
        Subgroup.map φ (relNormClassSubgroup K (IntermediateField.lift F)) := by
      rw [← closure_frobAt_eq_top (IntermediateField.lift F) HCF, MonoidHom.map_closure]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨τ, ⟨Q, hQmax, hQunr, rfl⟩, rfl⟩
      haveI := hQmax
      haveI := hQunr
      have hQ0 : Q ≠ ⊥ :=
        (Ideal.bot_lt_of_maximal Q (NumberField.RingOfIntegers.not_isField _)).ne'
      have hq0 : Q.under (𝓞 (IntermediateField.lift F)) ≠ ⊥ :=
        Ideal.under_ne_bot (𝓞 (IntermediateField.lift F)) hQ0
      haveI hqmax : (Q.under (𝓞 (IntermediateField.lift F))).IsMaximal :=
        (Ideal.IsPrime.under (𝓞 (IntermediateField.lift F)) (P := Q)).isMaximal hq0
      haveI : Algebra.IsUnramifiedAt (𝓞 K) (Q.under (𝓞 (IntermediateField.lift F))) :=
        hunrM _ hqmax.isPrime hq0
      have hJne : Ideal.relNorm (𝓞 K) (Q.under (𝓞 (IntermediateField.lift F))) ≠ ⊥ := by
        simpa using (Ideal.relNorm_eq_bot_iff (R := 𝓞 K)
          (I := Q.under (𝓞 (IntermediateField.lift F)))).not.mpr hq0
      refine ⟨ClassGroup.mk0 ⟨Ideal.relNorm (𝓞 K) (Q.under (𝓞 (IntermediateField.lift F))),
        mem_nonZeroDivisors_of_ne_zero hJne⟩,
        Subgroup.subset_closure ⟨Q.under (𝓞 (IntermediateField.lift F)), hq0, rfl⟩, ?_⟩
      rw [hkey (Q.under (𝓞 (IntermediateField.lift F))) Q _ rfl rfl,
        ← restrictScalars_frobAt K (IntermediateField.lift F) HCF Q
          (Q.under (𝓞 (IntermediateField.lift F))) rfl]
      rfl
    rw [hbridge]
    intro σ hσ
    have hcomm : ∀ x : IntermediateField.lift F,
        σ.toRingEquiv (algebraMap (IntermediateField.lift F) HCF x) =
          algebraMap (IntermediateField.lift F) HCF x := by
      intro x
      have h := AlgEquiv.restrictNormal_commutes σ (IntermediateField.lift F) x
      rw [show σ.restrictNormal (IntermediateField.lift F) =
        AlgEquiv.restrictNormalHom (IntermediateField.lift F) σ from rfl,
        MonoidHom.mem_ker.1 hσ, AlgEquiv.one_apply] at h
      exact h.symm
    exact hpush ⟨AlgEquiv.ofRingEquiv hcomm, trivial, rfl⟩
  intro c hc
  obtain ⟨n, hn, hnc⟩ := hge (Subgroup.mem_comap.1 hc)
  rwa [← hbij.1 hnc]

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

**What is now available for it, and what is still missing (2026-07-30).**
`exists_hilbertClassField_artinIso` above is PROVEN modulo the existence leaf, and it may
be used here without any risk of circularity — the implication is checked to run only in
this direction (see the module docstring). So the soundness sketch above is now half
formalisable: `Art` and the dictionary exist. Three things are still missing, in
increasing order of depth.

* *Transfer along an embedding.* `L` here is an abstract `Algebra K L`, while `HCF` lives
  inside `AlgebraicClosure K`. `IsAlgClosed.lift` embeds `L`, and `Ideal.relNorm_map_`
  `algEquiv` transports the norm, but `relNormClassSubgroup` and `Algebra.IsUnramifiedAt`
  have to be carried along the resulting `K`-algebra isomorphism by hand — the pin has no
  API for transporting rings of integers and their primes. Pure plumbing, but real.
* *The intersection.* With `L` inside `AlgebraicClosure K`, put `M := L ⊓ HCF`; then
  `Gal(L/K) ↠ Gal(M/K)` by restriction and `Gal(M/K) ≃ Cl(𝓞 K) ⧸ N_M` by the dictionary,
  so everything reduces to `N_L = N_M`. The inclusion `N_L ≤ N_M` is transitivity of the
  norm; it is the OTHER one that is the theorem.
* *`N_M ≤ N_L`, i.e. Chebotarev for `HCF·L / L`.* This is the genuine content and it is
  NOT the Chebotarev leaf of `ArtinSymbol.lean` applied to anything in this file: the
  composite `HCF·L` is a new field, and the argument needs its primes. Note `L/K` may be
  ramified at a real place, which is exactly why this cannot be routed through the
  modulus-`1` reciprocity leaf — that one is false without
  `IsUnramifiedAtInfinitePlaces`. `HCF·L / L` IS unramified everywhere (including at the
  archimedean places, where `L`'s real places are already real in `HCF·L` because `HCF/K`
  is unramified there), so a prover who builds the composite gets a modulus-`1` situation
  over the base `L`.

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
