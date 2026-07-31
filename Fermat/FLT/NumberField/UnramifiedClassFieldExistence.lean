/-
NumberField/UnramifiedClassFieldExistence.lean — own work for the Fermat
project (not vendored from the FLT project).
-/
module

public import Fermat.FLT.NumberField.UnramifiedClassFieldBound
public import Mathlib.FieldTheory.Galois.Abelian
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

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
* `NumberField.relNormClassSubgroup_eq_of_algEquiv` and
  `NumberField.isUnramifiedAt_ringOfIntegers_of_algEquiv` (over
  `NumberField.ringOfIntegersAlgEquiv`, and over `NumberField.isUnramifiedAt_of_algEquiv`
  hoisted here from `CyclotomicModelTransport.lean`) — PROVEN 2026-07-30, the `Transport`
  section. The norm class group and unramifiedness at a finite prime are carried along a
  `K`-algebra equivalence of number fields. Pure plumbing, absent from the pin, and what
  lets an abstract `Algebra K L` be moved into `AlgebraicClosure K` beside the Hilbert
  class field.
* `NumberField.exists_unramifiedAbelian_card_classGroup_le_finrank` — **OPEN LEAF, and
  as of 2026-07-30 the ONLY `sorry` left in this file.** The
  EXISTENCE theorem, alone: `K` has an abelian extension inside `AlgebraicClosure K`,
  unramified at every finite prime and at every infinite place, of degree at least `h_K`
  (hence, by the companion file's upper bound, exactly `h_K`). Cut 2026-07-30 out of the
  Artin-isomorphism node below.
* `NumberField.exists_hilbertClassField_artinIso` — **PROVEN 2026-07-30** from the
  existence leaf above and from `ArtinSymbol.lean`'s two leaves (RECIPROCITY and
  CHEBOTAREV), and from nothing else. Unramified class field theory at modulus `1` in one
  statement: the Hilbert class field exists inside `AlgebraicClosure K`, the Artin map is
  an isomorphism `Cl(𝓞 K) ≃ Gal(HCF/K)` sending `[𝔭]` to `Frob_𝔭`, and the norm class
  group of an intermediate field is the subgroup fixing it. The Frobenius clause and the
  dictionary clause are independent exports and have different consumers: only the first
  is used by `exists_surjective_aut_classGroupQuotient`, only the second by
  `exists_classField_of_subgroup`. The isomorphism is surjectivity (Chebotarev) plus
  counting against the existence leaf; the dictionary is the two Frobenius tower lemmas,
  with Chebotarev applied a second time — to `HCF/F` rather than to `HCF/K` — for the
  inclusion that says the norm classes FILL UP the fixing subgroup.
* `NumberField.exists_classField_of_subgroup` — PROVEN from the leaf above by the
  Galois correspondence. The existence theorem at modulus `1`: every subgroup of
  `Cl(𝓞 K)` is the norm class group of a finite abelian extension unramified at
  every finite prime and at every infinite place.
* `NumberField.exists_surjective_aut_classGroupQuotient_intermediateField` and
  `NumberField.exists_surjective_aut_classGroupQuotient` — **PROVEN 2026-07-30** from
  `exists_hilbertClassField_artinIso`'s Frobenius clause, `closure_frobAt_eq_top`
  (CHEBOTAREV) and the two Frobenius tower lemmas, and from nothing else. The Artin map
  in the direction `Gal(L/K) ↠ Cl(𝓞 K) ⧸ relNormClassSubgroup K L`, cut out of the first
  inequality on 2026-07-30. The mirror image of the companion file's
  `exists_surjective_classGroupHom_aut_of_unramified_abelian`, and NOT implied by it:
  this one survives ramification at the infinite places. The content is one inclusion —
  the class field of `N_{L/K}` is contained in `L` — obtained by CHEBOTAREV over `L`
  applied to the compositum `HCF ⬝ L`; the first of the two statements is that argument
  for an `L` already inside `AlgebraicClosure K`, the second adds the transport. Neither
  needs `L/K` abelian.
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

**Read that file before attacking the remaining leaf below.** Its two leaves, plus the
EXISTENCE leaf here, are now exactly the input of `exists_hilbertClassField_artinIso` —
and, since 2026-07-30, of everything else in this file as well.

A caution that used to read the other way. Those three are all stated at modulus `1`,
i.e. under `IsUnramifiedAtInfinitePlaces`, while
`index_relNormClassSubgroup_le_finrank` deliberately does NOT assume it, so this file
long recorded that they could not suffice for it. They do, and the reason is worth
keeping: RECIPROCITY is used only over the base `K`, where the hypothesis does hold
(it is `HCF` that must be unramified at the infinite places, not `L`), and CHEBOTAREV
— which assumes neither abelianness nor anything archimedean — is what is applied over
the possibly-badly-ramified `L`. The asymmetry between the two ArtinSymbol leaves is
exactly what makes the modulus-`1` machinery reach a statement that is false at
modulus `1` for the companion file's opposite surjection.

## Dependency direction inside this file — do not reverse it (2026-07-30)

`exists_hilbertClassField_artinIso` does NOT use
`exists_surjective_aut_classGroupQuotient`. That is deliberate and was paid for: an
earlier version of its proof got the `≥` half of the dictionary by counting, out of that
leaf, and the Chebotarev-over-`F` route was written precisely to remove the dependence.
The reason is that the route to that leaf runs through the `HCF` produced here, so a
dependency in this direction would close a cycle.

**It paid off the same day.** That leaf is now PROVEN, and its proof does exactly what
was anticipated — it forms the compositum of `L` with the `HCF` produced here. Had the
counting shortcut survived, the file would not compile. The rule therefore still binds:
`exists_hilbertClassField_artinIso` and everything it depends on must never be made to
depend on anything below it.
-/

@[expose] public section

open scoped nonZeroDivisors

namespace NumberField

section FrobeniusTower

variable (K M L : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
  [Field L] [NumberField L] [Algebra K M] [Algebra M L] [Algebra K L]
  [IsScalarTower K M L] [IsGalois K L] [IsGalois K M]

/-- **FROBENIUS RESTRICTS TO FROBENIUS: in a tower `K ⊆ M ⊆ L` of number fields with
**RENAMED 2026-07-31 (release 29).**  `ArtinSymbol.lean` -- which this
module imports -- declares a DIFFERENT theorem under the name
`restrictNormalHom_frobAt`: it computes the target ideal as `Q.under (𝓞 M)`
rather than taking it as a parameter with a defining equation.  Both are
wanted and the qualified names collided, so this one -- the parametrised
form, which is what this file's three call sites use -- carries a suffix.
Collapsing the pair is queued.

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
theorem restrictNormalHom_frobAt_of_under (Q : Ideal (𝓞 L)) [Q.IsMaximal] (q : Ideal (𝓞 M))
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
    rw [map_pow, restrictNormalHom_frobAt_of_under K M L Q q hq, hfdef]
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

section Transport

/-!
### Transport along a `K`-algebra equivalence

An abstract extension `L/K` and its image inside `AlgebraicClosure K` are `K`-isomorphic
but not equal, and nothing in the pin carries the arithmetic of `L` across such an
isomorphism: `relNormClassSubgroup` is defined from `Ideal.relNorm` on `𝓞 L`, and
`Algebra.IsUnramifiedAt (𝓞 K) q` is `FormallyUnramified` of a LOCALIZATION of `𝓞 L`.
Both must be moved by hand. This is the plumbing that
`exists_surjective_aut_classGroupQuotient`'s docstring listed as its first missing
ingredient; it is pure bookkeeping, but it is what lets that proof put the abstract `L`
into the same field as the Hilbert class field.
-/

variable {K : Type*} [Field K] [NumberField K]
variable {L₁ L₂ : Type*} [Field L₁] [NumberField L₁] [Field L₂] [NumberField L₂]
  [Algebra K L₁] [Algebra K L₂]

/-- **The `𝓞 K`-algebra equivalence of rings of integers induced by a `K`-algebra
equivalence of number fields** (PROVEN 2026-07-30).

`RingOfIntegers.mapRingEquiv` supplies the ring equivalence; all that is added here is
that it is `𝓞 K`-linear, which is `AlgEquiv.commutes` for `e` pushed through the two
scalar towers `𝓞 K ⊆ 𝓞 Lᵢ ⊆ Lᵢ` and `𝓞 K ⊆ K ⊆ Lᵢ`. -/
noncomputable def ringOfIntegersAlgEquiv (e : L₁ ≃ₐ[K] L₂) : (𝓞 L₁) ≃ₐ[𝓞 K] (𝓞 L₂) :=
  { RingOfIntegers.mapRingEquiv e.toRingEquiv with
    commutes' := fun r => by
      apply RingOfIntegers.ext
      show e ((algebraMap (𝓞 K) (𝓞 L₁) r : 𝓞 L₁) : L₁) =
        ((algebraMap (𝓞 K) (𝓞 L₂) r : 𝓞 L₂) : L₂)
      rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap,
        ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L₁) L₁,
        ← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 L₂) L₂,
        IsScalarTower.algebraMap_apply (𝓞 K) K L₁,
        IsScalarTower.algebraMap_apply (𝓞 K) K L₂, AlgEquiv.commutes] }

private theorem relNormClassSubgroup_le_of_algEquiv (e : L₁ ≃ₐ[K] L₂) :
    relNormClassSubgroup K L₁ ≤ relNormClassSubgroup K L₂ := by
  refine (Subgroup.closure_le _).2 ?_
  rintro c ⟨I, hI, rfl⟩
  set σ := ringOfIntegersAlgEquiv e with hσ
  have hI' : Ideal.map σ I ≠ ⊥ :=
    fun h => hI ((Ideal.map_eq_bot_iff_of_injective σ.injective).1 h)
  have hrel : Ideal.relNorm (𝓞 K) (Ideal.map σ I) = Ideal.relNorm (𝓞 K) I :=
    Ideal.relNorm_map_algEquiv σ I
  refine Subgroup.subset_closure ⟨Ideal.map σ I, hI', ?_⟩
  congr 1
  exact Subtype.ext hrel.symm

/-- **THE NORM CLASS GROUP IS AN INVARIANT OF THE `K`-ISOMORPHISM CLASS OF `L`**
(PROVEN 2026-07-30).

Each generator `[N_{L₁/K} I]` of the left-hand side is the generator
`[N_{L₂/K} (σ I)]` of the right-hand side, because `Ideal.relNorm_map_algEquiv` says the
relative norm is unchanged by an `𝓞 K`-algebra automorphism of the top ring. Both
inclusions are the same argument applied to `e` and to `e.symm`. -/
theorem relNormClassSubgroup_eq_of_algEquiv (e : L₁ ≃ₐ[K] L₂) :
    relNormClassSubgroup K L₁ = relNormClassSubgroup K L₂ :=
  le_antisymm (relNormClassSubgroup_le_of_algEquiv e)
    (relNormClassSubgroup_le_of_algEquiv e.symm)

/-- **`Algebra.IsUnramifiedAt` IS CARRIED BY AN ISOMORPHISM OVER THE BASE**
(PROVEN 2026-07-30).

If `h : R ≃ₐ[A] P` and the prime `Q` of `P` pulls back to the prime `q` of
`R`, then `A`-unramifiedness at `q` gives `A`-unramifiedness at `Q`. The proof
is the only thing it can be: `h` carries `q.primeCompl` onto `Q.primeCompl`,
so `IsLocalization.algEquivOfAlgEquiv` gives an `A`-algebra isomorphism of the
two localisations, and `Algebra.FormallyUnramified.of_equiv` transports the
definition (`IsUnramifiedAt A q` is by definition
`FormallyUnramified A (Localization.AtPrime q)`).

**Provenance.** This was written for
`Fermat/FLT/NumberField/CyclotomicModelTransport.lean`, which imports this file, and was
HOISTED here on 2026-07-30 when `exists_surjective_aut_classGroupQuotient` below needed
the same statement — two copies of one declaration in one namespace do not compile
together, so the choice was hoist or rename, and hoisting is what removes the
duplication. Nothing about it is specific to either consumer; it belongs in mathlib
beside `Algebra.IsUnramifiedAt`. -/
theorem isUnramifiedAt_of_algEquiv {A R P : Type*} [CommRing A] [CommRing R] [CommRing P]
    [Algebra A R] [Algebra A P] (h : R ≃ₐ[A] P) (q : Ideal R) [q.IsPrime]
    (Q : Ideal P) [Q.IsPrime] (hQ : Ideal.comap (h : R →+* P) Q = q)
    (hu : Algebra.IsUnramifiedAt A q) : Algebra.IsUnramifiedAt A Q := by
  have hiff : ∀ x : R, x ∈ q ↔ h x ∈ Q := by
    intro x; rw [← hQ]; rfl
  have hmap : Submonoid.map (h : R →* P) q.primeCompl = Q.primeCompl := by
    ext y
    simp only [Submonoid.mem_map, Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk,
      Set.mem_compl_iff, SetLike.mem_coe]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact fun hmem => hx ((hiff x).mpr hmem)
    · intro hy
      exact ⟨h.symm y, fun hmem => hy (by simpa using (hiff _).mp hmem), by simp⟩
  exact Algebra.FormallyUnramified.of_equiv
    (IsLocalization.algEquivOfAlgEquiv (Localization.AtPrime q) (Localization.AtPrime Q) h hmap)

omit [NumberField K] [NumberField L₁] [NumberField L₂] in
/-- **UNRAMIFIEDNESS AT EVERY FINITE PRIME TRANSPORTS ALONG A `K`-ALGEBRA EQUIVALENCE OF
NUMBER FIELDS** (PROVEN 2026-07-30).

The specialisation of `isUnramifiedAt_of_algEquiv` above to
`ringOfIntegersAlgEquiv e : 𝓞 L₁ ≃ₐ[𝓞 K] 𝓞 L₂`. The hypothesis is stated over ALL
nonzero primes rather than at the single prime `σ⁻¹ q`, purely because the caller holds
it in exactly that form; nothing in the proof uses more than the one prime.

Nonzero-ness has to be carried too, and it is the one step that is not formal: `⊥` is a
prime of `𝓞 L₁` and the hypothesis deliberately excludes it, so the pullback `σ⁻¹ q` must
be shown nonzero, which is `Ideal.map_comap_of_surjective` against `Ideal.map_bot`. -/
theorem isUnramifiedAt_ringOfIntegers_of_algEquiv (e : L₁ ≃ₐ[K] L₂)
    (h : ∀ (Q : Ideal (𝓞 L₁)) (_ : Q.IsPrime), Q ≠ ⊥ → Algebra.IsUnramifiedAt (𝓞 K) Q)
    (q : Ideal (𝓞 L₂)) (hq : q.IsPrime) (hq0 : q ≠ ⊥) :
    Algebra.IsUnramifiedAt (𝓞 K) q := by
  haveI := hq
  set σ : 𝓞 L₁ ≃ₐ[𝓞 K] 𝓞 L₂ := ringOfIntegersAlgEquiv e with hσ
  set ρ : 𝓞 L₁ →+* 𝓞 L₂ := (σ : 𝓞 L₁ →+* 𝓞 L₂) with hρ
  set Q : Ideal (𝓞 L₁) := q.comap ρ with hQ
  haveI hQp : Q.IsPrime := Ideal.comap_isPrime _ _
  have hqQ : Q.map ρ = q := by
    rw [hQ, Ideal.map_comap_of_surjective ρ σ.surjective]
  have hQ0 : Q ≠ ⊥ := by
    intro hcon
    exact hq0 (by rw [← hqQ, hcon, Ideal.map_bot])
  exact isUnramifiedAt_of_algEquiv σ Q q rfl (h Q hQp hQ0)

end Transport

variable (K : Type*) [Field K] [NumberField K]

/-- **THE NORM CLASS GROUP IS ANTITONE IN THE FIELD: `L ≤ M` gives
`relNormClassSubgroup K M ≤ relNormClassSubgroup K L`** (PROVEN 2026-07-31).

`N_{M/K} = N_{L/K} ∘ N_{M/L}` (`Ideal.relNorm_relNorm`), so the class of `N_{M/K} I` is
already the class of `N_{L/K} J` for `J = N_{M/L} I`; and `J ≠ ⊥` because `relNorm` of a
nonzero ideal is nonzero (`Ideal.relNorm_eq_bot_iff`). The generating sets are therefore
nested and `Subgroup.closure_le` finishes.

**THIS IS THE REASON THE EXISTENCE LEAVES BELOW ARE PHRASED IN NORM GROUPS AND NOT IN
DEGREES.** It is the ONE monotonicity in this cluster that points the useful way: enlarging
the field SHRINKS the norm class group, so the everywhere-unramified abelian extensions of
`K` can be combined by composita and their norm groups intersected. Nothing analogous holds
on the Galois side — a compositum `M ⊇ L₁, L₂` only gives
`Gal(M/K) ↪ Gal(L₁/K) × Gal(L₂/K)`, which bounds `[M : K]` from ABOVE — so a statement
carrying a degree, or an injection `Cl(𝓞 K) ↪ Gal(L/K)`, does not combine under composita at
all. See `exists_unramifiedAbelian_card_classGroup_le_finrank` below for what that costs.

The tower instances are the ones the file builds elsewhere by hand (`IntermediateField.
inclusion`, `IsScalarTower.of_algebraMap_eq'`); `Module.Finite ↥L ↥M` comes from
`Module.Finite.of_restrictScalars_finite`, and the `Module.Finite`/`IsTorsionFree`
hypotheses of `Ideal.relNorm_relNorm` on the rings of integers are then synthesised. -/
theorem relNormClassSubgroup_le_of_le (L M : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K M] [NumberField L] [NumberField M] (hLM : L ≤ M) :
    relNormClassSubgroup K M ≤ relNormClassSubgroup K L := by
  letI : Algebra L M := (IntermediateField.inclusion hLM).toRingHom.toAlgebra
  haveI : IsScalarTower K L M :=
    IsScalarTower.of_algebraMap_eq' (IntermediateField.inclusion hLM).comp_algebraMap.symm
  haveI : Module.Finite L M := Module.Finite.of_restrictScalars_finite K _ _
  refine (Subgroup.closure_le _).2 ?_
  rintro c ⟨I, hI, rfl⟩
  have hJ : Ideal.relNorm (𝓞 L) I ≠ ⊥ := by
    simpa using (Ideal.relNorm_eq_bot_iff (R := 𝓞 L) (I := I)).not.mpr hI
  have hrel : Ideal.relNorm (𝓞 K) (Ideal.relNorm (𝓞 L) I) = Ideal.relNorm (𝓞 K) I :=
    Ideal.relNorm_relNorm (𝓞 K) (𝓞 L) I
  exact Subgroup.subset_closure
    ⟨Ideal.relNorm (𝓞 L) I, hJ, by congr 1; exact Subtype.ext hrel.symm⟩

/-- **THE SUBGROUPS OF `Cl(𝓞 K)` WITH CYCLIC QUOTIENT INTERSECT IN `⊥`: every ideal class
`c ≠ 1` is missed by some `N` with `Cl(𝓞 K) ⧸ N` cyclic** (PROVEN 2026-07-31).

Pure finite abelian group theory, and the reason the cyclic case of the existence theorem
suffices for the general one. `Cl(𝓞 K)` is finite and commutative, so
`CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity` supplies a character
`φ : Cl(𝓞 K) →* (AlgebraicClosure K)ˣ` with `φ c ≠ 1`; take `N = φ.ker`. The quotient is
`φ.range` (`QuotientGroup.quotientKerEquivRange`), a finite subgroup of the units of a
field, hence cyclic (`isCyclic_subgroup_units`).

**`AlgebraicClosure K` rather than `ℂ`, deliberately.** The duality lemma needs a monoid
with enough roots of unity, and `ℂ` would drag the whole complex-analysis cone into a file
whose mathematics is entirely algebraic. `AlgebraicClosure K` is already the ambient field
of every statement here, and `IsSepClosed.hasEnoughRootsOfUnity` applies to it once
`NeZero ((Monoid.exponent (Cl 𝓞 K) : ℕ) : K)` is supplied — which is
`Monoid.exponent_ne_zero_of_finite` plus characteristic zero.

**PRIME index is NOT enough, and this is the trap the statement avoids.** For
`Cl(𝓞 K) ≃ ℤ/4` the only subgroup of prime index is `2ℤ/4`, and the subgroups of prime
index therefore intersect in `2ℤ/4 ≠ ⊥`. A reduction of the existence theorem to congruence
subgroups of PRIME index (which is how several textbook accounts phrase it) has to iterate
up a tower to recover the rest; reducing to CYCLIC quotient instead is what makes the
compositum argument below a single step. -/
theorem exists_isCyclic_quotient_notMem (c : ClassGroup (𝓞 K)) (hc : c ≠ 1) :
    ∃ N : Subgroup (ClassGroup (𝓞 K)), IsCyclic (ClassGroup (𝓞 K) ⧸ N) ∧ c ∉ N := by
  haveI : NeZero ((Monoid.exponent (ClassGroup (𝓞 K)) : ℕ) : K) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
    (ClassGroup (𝓞 K)) (AlgebraicClosure K) hc
  refine ⟨φ.ker, ?_, fun h => hφ h⟩
  haveI : Finite φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
  exact isCyclic_of_surjective (QuotientGroup.quotientKerEquivRange φ).symm.toMonoidHom
    (QuotientGroup.quotientKerEquivRange φ).symm.surjective

/-- **THE EXISTENCE THEOREM FOR A CONGRUENCE SUBGROUP WITH CYCLIC QUOTIENT: for every
`N ≤ Cl(𝓞 K)` with `Cl(𝓞 K) ⧸ N` CYCLIC there is a finite abelian extension of `K` inside
`AlgebraicClosure K`, unramified at every finite prime and at every infinite place, whose
norm class group is contained in `N`** (SORRY LEAF, cut 2026-07-31 out of
`exists_unramifiedAbelian_relNormClassSubgroup_eq_bot` below).

**THIS IS WHERE KUMMER THEORY LIVES, and it is the whole classical content of the existence
theorem.** Takagi's argument: `Cl(𝓞 K) ⧸ N` cyclic of order `n`; adjoin `ζ_n` to get
`K' = K(ζ_n)`; build the extension of `K'` by Kummer theory from a group of `n`-virtual
units of `K'` chosen so that the extension is unramified; descend the NORM GROUP to `K` by
the translation theorem (Verschiebungssatz). References: Neukirch VI (7.3) and the sections
before it; Childress ch. 4–5; Lang *ANT* ch. X; Cassels–Fröhlich ch. VII–VIII.

**⚠ Do not re-cut the naive "descend an unramified abelian extension from `K(ζ_ℓ)`" leaf**:
it is FALSE, with the PARI/GP witness recorded on `exists_classField_of_subgroup` below
(`K = ℚ(√29)`, `h = h⁺ = 1`, `h(K(ζ_3)) = 3`). The descent in the classical proof is of the
norm group, not of the field, which is exactly why this statement's conclusion is
`relNormClassSubgroup K L ≤ N` and not a statement about `L` itself.

**`≤ N` and not `= N`, deliberately.** The consumer only ever intersects, and the reverse
inclusion is free anyway once the correspondence is known (it is
`exists_classField_of_subgroup` below, which is PROVEN over the full existence theorem).
Asking for `≤` keeps the leaf as weak as it can be while still doing its job.

**No degree clause, deliberately.** Adding `Module.finrank K L = N.index` would make the
leaf strictly stronger and would NOT remove the need for the second fundamental inequality
further down: degrees do not survive the compositum step (see
`relNormClassSubgroup_le_of_le` above). Keeping degrees out of this leaf is what lets the
compositum argument be a single well-founded descent.

**Non-vacuity and the trivial case.** At `N = ⊤` the conclusion is vacuous and `L = K`
works; the consumer uses exactly that instance to start its descent. At `N = ⊥` the
statement is the full Hilbert class field, so the leaf is not uniformly easy — the cyclic
hypothesis is what bounds the difficulty, and `Cl(𝓞 K) ⧸ ⊥` is cyclic precisely when
`Cl(𝓞 K)` is.

**The check that would refute it**: a number field `K` and `N ≤ Cl(𝓞 K)` with cyclic
quotient such that every finite abelian extension of `K` unramified at every finite prime
and at every infinite place has some ideal class outside `N` in its norm class group. -/
theorem exists_unramifiedAbelian_relNormClassSubgroup_le_of_isCyclic_quotient
    (N : Subgroup (ClassGroup (𝓞 K))) (hN : IsCyclic (ClassGroup (𝓞 K) ⧸ N)) :
    ∃ (L : IntermediateField K (AlgebraicClosure K)) (_ : FiniteDimensional K L)
      (_ : NumberField L) (_ : IsAbelianGalois K L)
      (_ : IsUnramifiedAtInfinitePlaces K L),
      (∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime), Q ≠ ⊥ →
        Algebra.IsUnramifiedAt (𝓞 K) Q) ∧
      relNormClassSubgroup K L ≤ N :=
  sorry

omit [NumberField K] in
/-- **AN AUTOMORPHISM OF `AlgebraicClosure K` THAT FIXES `L₁` AND `L₂` POINTWISE FIXES THE
COMPOSITUM POINTWISE** (PROVEN 2026-07-31).

The engine of every compositum argument in this file, and the reason the three obligations
on `L₁ ⊔ L₂` are all the same argument. The fixed points of `ρ` are an intermediate field —
concretely `IntermediateField.fixedField (Subgroup.closure {ρ})` — so `sup_le` applies once
each `Lᵢ` is inside it, and membership there is `Subgroup.closure_le` into
`MulAction.stabilizer _ y`, which is exactly the statement that `ρ` fixes `y`.

Using the stabiliser is what avoids an induction over the powers of `ρ`: `closure {ρ}`
contains `ρ^n` for every `n : ℤ`, and checking each of those fixes `y` by hand would need
a `zpow` induction, while `Subgroup.closure_le` discharges all of them from the single
fact `ρ • y = y` because the stabiliser is already a subgroup. -/
theorem forall_mem_sup_of_fixed (L₁ L₂ : IntermediateField K (AlgebraicClosure K))
    (ρ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (h₁ : ∀ x ∈ L₁, ρ x = x) (h₂ : ∀ x ∈ L₂, ρ x = x) :
    ∀ x ∈ L₁ ⊔ L₂, ρ x = x := by
  have key : L₁ ⊔ L₂ ≤ IntermediateField.fixedField (Subgroup.closure {ρ}) := by
    refine sup_le ?_ ?_ <;> intro y hy <;>
      refine (IntermediateField.mem_fixedField_iff _ _).2 fun g hg => ?_
    · exact (Subgroup.closure_le
        (MulAction.stabilizer (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) y)).2
        (by rintro _ rfl; exact h₁ y hy) hg
    · exact (Subgroup.closure_le
        (MulAction.stabilizer (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) y)).2
        (by rintro _ rfl; exact h₂ y hy) hg
  intro x hx
  exact (IntermediateField.mem_fixedField_iff _ _).1 (key hx) ρ (Subgroup.subset_closure rfl)

omit [NumberField K] in
/-- **RESTRICTING TO A NORMAL INTERMEDIATE FIELD IS TRIVIAL EXACTLY WHEN THE AUTOMORPHISM
FIXES IT POINTWISE — the `→` direction** (PROVEN 2026-07-31). One application of
`AlgEquiv.restrictNormal_commutes` and injectivity of the inclusion. -/
theorem restrictNormalHom_eq_one_of_fixed (E : IntermediateField K (AlgebraicClosure K))
    [Normal K E] (ρ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (h : ∀ x ∈ E, ρ x = x) :
    AlgEquiv.restrictNormalHom (F := K) (K₁ := AlgebraicClosure K) E ρ = 1 := by
  refine AlgEquiv.ext fun y => ?_
  have hc := AlgEquiv.restrictNormal_commutes ρ (E : IntermediateField K (AlgebraicClosure K)) y
  rw [show ρ.restrictNormal (E : IntermediateField K (AlgebraicClosure K)) =
    AlgEquiv.restrictNormalHom E ρ from rfl] at hc
  exact Subtype.ext (by simpa [h (y : AlgebraicClosure K) y.2] using hc)

omit [NumberField K] in
/-- **… and the `←` direction** (PROVEN 2026-07-31). -/
theorem fixed_of_restrictNormalHom_eq_one (E : IntermediateField K (AlgebraicClosure K))
    [Normal K E] (ρ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (h : AlgEquiv.restrictNormalHom (F := K) (K₁ := AlgebraicClosure K) E ρ = 1) :
    ∀ x ∈ E, ρ x = x := by
  intro x hx
  have hc := AlgEquiv.restrictNormal_commutes ρ
    (E : IntermediateField K (AlgebraicClosure K)) (⟨x, hx⟩ : E)
  rw [show ρ.restrictNormal (E : IntermediateField K (AlgebraicClosure K)) =
    AlgEquiv.restrictNormalHom E ρ from rfl, h] at hc
  simpa using hc.symm

open scoped IsMulCommutative in
/-- **THE COMPOSITUM OF TWO FINITE ABELIAN EXTENSIONS OF `K` INSIDE `AlgebraicClosure K` IS
ABELIAN OVER `K`** (PROVEN 2026-07-31).

The Galois-theoretic third of the compositum leaf below, closed so that its owner faces only
ramification. Lift `σ, τ ∈ Gal(L₁ ⬝ L₂ / K)` to `Gal(K̄/K)`
(`AlgEquiv.restrictNormalHom_surjective`) and look at the commutator `ρ`. Restriction to
`Lᵢ` is a group homomorphism into a COMMUTATIVE group, so it kills `ρ`; hence `ρ` fixes each
`Lᵢ` pointwise, hence the compositum pointwise, hence restricts to `1` there — which is the
commutativity wanted. `IsGalois K ↥(L₁ ⊔ L₂)` is synthesised (`Normal` and separability of a
sup are instances at this pin), so only the commutativity is work.

**Note what is NOT used: no linear disjointness, no `Gal(M/K) ↪ Gal(L₁/K) × Gal(L₂/K)` as an
explicit map, and no degree.** Injectivity of that pair map is exactly
`forall_mem_sup_of_fixed`, and stating it as "fixes both ⟹ fixes the sup" is what makes the
same lemma serve the ramification clauses too. -/
theorem isAbelianGalois_sup (L₁ L₂ : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    [IsAbelianGalois K L₁] [IsAbelianGalois K L₂] :
    IsAbelianGalois K ↥(L₁ ⊔ L₂) := by
  haveI : IsGalois K ↥(L₁ ⊔ L₂) := ⟨⟩
  refine { is_comm.comm := fun σ τ => ?_ }
  obtain ⟨σ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure K) σ
  obtain ⟨τ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure K) τ
  set ρ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := (σ' * τ') * (τ' * σ')⁻¹ with hρ
  have hfix : ∀ (E : IntermediateField K (AlgebraicClosure K)) [Normal K E]
      [IsMulCommutative (E ≃ₐ[K] E)], ∀ x ∈ E, ρ x = x := by
    intro E _ _
    refine fixed_of_restrictNormalHom_eq_one K E ρ ?_
    rw [hρ, map_mul, map_inv, map_mul, map_mul,
      mul_comm (AlgEquiv.restrictNormalHom E τ') (AlgEquiv.restrictNormalHom E σ')]
    exact mul_inv_cancel _
  have hone : AlgEquiv.restrictNormalHom (F := K) (K₁ := AlgebraicClosure K)
      ↥(L₁ ⊔ L₂) ρ = 1 :=
    restrictNormalHom_eq_one_of_fixed K (L₁ ⊔ L₂) ρ
      (forall_mem_sup_of_fixed K L₁ L₂ ρ (hfix L₁) (hfix L₂))
  rw [hρ, map_mul, map_inv] at hone
  rw [← map_mul, ← map_mul, ← mul_inv_eq_one]
  exact hone

/-- **THE COMPOSITUM OF TWO EXTENSIONS UNRAMIFIED AT THE INFINITE PLACES IS UNRAMIFIED AT
THE INFINITE PLACES** (SORRY LEAF, cut 2026-07-31 out of `exists_unramifiedAbelian_sup`
below).

Pure archimedean ramification theory, no class field theory. `IsUnramifiedAtInfinitePlaces
K L` says every infinite place of `L` is unramified over `K`, i.e. no real place of `K`
becomes complex. The argument is the ARCHIMEDEAN instance of `forall_mem_sup_of_fixed`
above: if a real place `v` of `K` were to become complex in `M = L₁ ⬝ L₂`, complex
conjugation at a place above `v` is a nontrivial element of `Gal(M/K)` (the extension is
Galois, so the decomposition group at an archimedean place is generated by it), and its
restriction to each `Lᵢ` is the corresponding conjugation there — trivial, since `v` is
unramified in `Lᵢ`. An element trivial on `L₁` and on `L₂` is trivial, contradiction.

**Cheap sufficient cases worth knowing before doing the general one**: mathlib's
`IsUnramifiedAtInfinitePlaces_of_odd_finrank` settles it whenever `[M : K]` is odd, and
`IsUnramifiedAtInfinitePlaces.bot` handles the tower direction; neither reaches the
compositum. `NumberField.InfinitePlace.IsUnramified` and `InfinitePlace.comap` are the
API to work in.

**The check that would refute it**: two extensions of a number field `K`, each unramified
at every infinite place, whose compositum has a real place of `K` becoming complex. -/
theorem isUnramifiedAtInfinitePlaces_sup (L₁ L₂ : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L₁] [FiniteDimensional K L₂]
    [IsUnramifiedAtInfinitePlaces K L₁] [IsUnramifiedAtInfinitePlaces K L₂] :
    IsUnramifiedAtInfinitePlaces K ↥(L₁ ⊔ L₂) :=
  sorry

/-- **THE COMPOSITUM OF TWO EXTENSIONS UNRAMIFIED AT EVERY FINITE PRIME IS UNRAMIFIED AT
EVERY FINITE PRIME** (SORRY LEAF, cut 2026-07-31 out of `exists_unramifiedAbelian_sup`
below).

Pure nonarchimedean ramification theory, no class field theory, and the last genuinely
mathematical obligation of the compositum. The argument is the NONARCHIMEDEAN instance of
`forall_mem_sup_of_fixed` above: an element of the inertia group at a prime `Q` of
`𝓞 (L₁ ⬝ L₂)` acts trivially on `𝓞 M / Q`, hence trivially on the subring
`𝓞 Lᵢ / (Q ∩ 𝓞 Lᵢ)`, hence lies in the inertia group of `Q ∩ 𝓞 Lᵢ` over `𝓞 K` — which is
trivial by hypothesis. So it is trivial on `L₁` and on `L₂`, hence trivial, hence the
inertia group at `Q` is trivial and `Q` is unramified.

**⚠ THE ROUTE NOT TO TRY: `Algebra.FormallyUnramified.baseChange` on
`𝓞 L₁ ⊗_{𝓞 K} 𝓞 L₂`.** It gives unramifiedness of the TENSOR PRODUCT, and transporting
that to `𝓞 (L₁L₂)` needs the latter to be locally generated by the former — i.e. that the
conductor of `𝓞 L₁ ⊗ 𝓞 L₂` in `𝓞 (L₁L₂)` is the unit ideal, which is false in general even
for `L₁`, `L₂` unramified. The inertia route never forms the tensor product.

**What the pin supplies.** `Algebra.IsUnramifiedAt`, `Algebra.IsUnramifiedAt.of_liesOver`
(descent to an intermediate ring, used elsewhere in this file),
`Ideal.ramificationIdx'_eq_one_iff`, `Ideal.under_under`, and mathlib's Frobenius/inertia
material in `Mathlib/RingTheory/Frobenius.lean` and `Mathlib/RingTheory/Invariant/Basic.lean`.
`ArtinSymbol.lean`'s `eq_one_of_smul_eq_self` (an automorphism acting trivially on `𝓞 L` is
the identity) is the bridge from "acts trivially on the ring" to "is `1` in `Gal`", and it
is already proven.

**The check that would refute it**: a prime of a number field `K` unramified in `L₁` and in
`L₂` but ramified in `L₁L₂`. -/
theorem isUnramifiedAt_ringOfIntegers_sup (L₁ L₂ : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L₁] [FiniteDimensional K L₂] [NumberField L₁] [NumberField L₂]
    (h₁ : ∀ (Q : Ideal (𝓞 L₁)) (_ : Q.IsPrime), Q ≠ ⊥ → Algebra.IsUnramifiedAt (𝓞 K) Q)
    (h₂ : ∀ (Q : Ideal (𝓞 L₂)) (_ : Q.IsPrime), Q ≠ ⊥ → Algebra.IsUnramifiedAt (𝓞 K) Q) :
    ∀ (Q : Ideal (𝓞 ↥(L₁ ⊔ L₂))) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) Q :=
  sorry

/-- **THE COMPOSITUM OF TWO EVERYWHERE-UNRAMIFIED ABELIAN EXTENSIONS IS ONE: given two
finite abelian extensions of `K` inside `AlgebraicClosure K`, each unramified at every
finite prime and at every infinite place, some such extension contains them both** (cut
2026-07-31 out of `exists_unramifiedAbelian_relNormClassSubgroup_eq_bot` below, and
DECOMPOSED AND PROVEN the same day from `isAbelianGalois_sup` above — the Galois third,
CLOSED — together with the two remaining leaves `isUnramifiedAtInfinitePlaces_sup` and
`isUnramifiedAt_ringOfIntegers_sup`, and from nothing else).

**THERE IS NO CLASS FIELD THEORY IN THIS STATEMENT.** It is pure Galois and ramification
theory, it is the kind of thing that belongs in mathlib, and it is separately ownable from
the Kummer-theoretic leaf above. That separation is the point of the cut.

**Stated existentially (`∃ M`, `L₁ ≤ M`, `L₂ ≤ M`) rather than at `M = L₁ ⊔ L₂`.** The
intended witness IS the compositum, but phrasing it existentially costs the consumer nothing
and spares both sides the `IntermediateField.sup` instance derivations at the interface. A
prover should take `M = L₁ ⊔ L₂` and will find `FiniteDimensional K M`
(`IntermediateField.finiteDimensional_sup`), `NumberField M`
(`NumberField.of_module_finite`) and `Normal K M` already available as instances — the file
does exactly this at `exists_surjective_aut_classGroupQuotient_intermediateField` below,
where `E := HCF ⊔ M` needs no hand-built instance beyond the tower algebras.

**The three real obligations were ALL THE SAME ARGUMENT, and that is why one of them is
already closed.** An element of `Gal(M/K)` trivial on `L₁` and on `L₂` is trivial, because
the set it fixes is an intermediate field containing both, hence containing `L₁ ⊔ L₂`. That
step is `forall_mem_sup_of_fixed` above, PROVEN, and it serves all three:

* *abelian* — `isAbelianGalois_sup` above, **PROVEN 2026-07-31**: the commutator of two
  lifts to `Gal(K̄/K)` restricts to `1` on each `Lᵢ` because `Gal(Lᵢ/K)` is commutative;
* *unramified at the finite primes* — `isUnramifiedAt_ringOfIntegers_sup` above, OPEN: the
  same, with the inertia group at a prime `Q` of `𝓞 M` in place of the commutator;
* *unramified at the infinite places* — `isUnramifiedAtInfinitePlaces_sup` above, OPEN: the
  same, with complex conjugation at an archimedean place.

The two open ones are separately ownable and use disjoint mathlib API
(`Algebra.IsUnramifiedAt` and localisation, against `InfinitePlace.IsUnramified` and
`InfinitePlace.comap`); each docstring carries its own argument and its own refutation
check, including the `FormallyUnramified.baseChange` route that does NOT work.

**Both unramifiedness hypotheses on both fields are load-bearing.** Dropping unramifiedness
at the infinite places makes the conclusion false for the same reason it makes the
companion file's `finrank_le_index_relNormClassSubgroup` false: `K = ℚ(√3)` has a narrow
class field ramified at a real place, and composita of such extensions stay ramified there,
so the conclusion could not carry `IsUnramifiedAtInfinitePlaces K M`.

**The check that would refute it**: two finite abelian extensions of a number field `K`,
each unramified at every finite prime and at every infinite place, whose compositum is
ramified somewhere — equivalently, a prime of `K` unramified in `L₁` and in `L₂` but
ramified in `L₁L₂`. -/
theorem exists_unramifiedAbelian_sup (L₁ L₂ : IntermediateField K (AlgebraicClosure K))
    (h₁fd : FiniteDimensional K L₁) (h₁nf : NumberField L₁) (h₁ab : IsAbelianGalois K L₁)
    (h₁inf : IsUnramifiedAtInfinitePlaces K L₁)
    (h₁unr : ∀ (Q : Ideal (𝓞 L₁)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) Q)
    (h₂fd : FiniteDimensional K L₂) (h₂nf : NumberField L₂) (h₂ab : IsAbelianGalois K L₂)
    (h₂inf : IsUnramifiedAtInfinitePlaces K L₂)
    (h₂unr : ∀ (Q : Ideal (𝓞 L₂)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) Q) :
    ∃ (M : IntermediateField K (AlgebraicClosure K)) (_ : FiniteDimensional K M)
      (_ : NumberField M) (_ : IsAbelianGalois K M)
      (_ : IsUnramifiedAtInfinitePlaces K M),
      (∀ (Q : Ideal (𝓞 M)) (_ : Q.IsPrime), Q ≠ ⊥ →
        Algebra.IsUnramifiedAt (𝓞 K) Q) ∧
      L₁ ≤ M ∧ L₂ ≤ M := by
  haveI := h₁fd; haveI := h₁nf; haveI := h₁ab; haveI := h₁inf
  haveI := h₂fd; haveI := h₂nf; haveI := h₂ab; haveI := h₂inf
  haveI : FiniteDimensional K ↥(L₁ ⊔ L₂) := IntermediateField.finiteDimensional_sup L₁ L₂
  haveI : NumberField ↥(L₁ ⊔ L₂) := NumberField.of_module_finite K _
  exact ⟨L₁ ⊔ L₂, inferInstance, inferInstance, isAbelianGalois_sup K L₁ L₂,
    isUnramifiedAtInfinitePlaces_sup K L₁ L₂,
    isUnramifiedAt_ringOfIntegers_sup K L₁ L₂ h₁unr h₂unr, le_sup_left, le_sup_right⟩

/-- **THE SECOND FUNDAMENTAL INEQUALITY AT MODULUS `1`: for `L/K` finite abelian,
unramified at every finite prime AND at every infinite place, the norm index
`[I_K : P_K · N_{L/K} I_L]` is AT MOST the degree `[L : K]`** (SORRY LEAF, cut 2026-07-31
out of `exists_unramifiedAbelian_card_classGroup_le_finrank` below).

**This is the input that turns norm-group information into a DEGREE, and the existence
theorem below cannot be proven without it or an equivalent.** Everything else this cluster
has — the companion file's `finrank_le_index_relNormClassSubgroup`, its
`exists_surjective_classGroupHom_aut_of_unramified_abelian`, and the whole Artin map — runs
in the direction `Cl(𝓞 K) ↠ Gal(L/K)` and therefore bounds `[L : K]` from ABOVE. Nothing
available upstream of this line bounds a degree from below, and a degree lower bound is
exactly what the leaf below asserts.

**⚠ IT IS NOT A DUPLICATE OF `index_relNormClassSubgroup_le_finrank` BELOW, AND THE
APPARENT DUPLICATION IS FORCED BY THE DEPENDENCY ORDER.** That theorem is the SAME
inequality with the archimedean hypothesis DROPPED, and it is PROVEN — but its proof runs
`exists_surjective_aut_classGroupQuotient` → `exists_hilbertClassField_artinIso` →
`exists_unramifiedAbelian_card_classGroup_le_finrank`, i.e. through the existence leaf
below. Citing it here would close a cycle, and Lean's declaration order rejects it outright.
The honest reading of the two is:

* THIS one is an INPUT of the theory — classically the algebraic half of the class field
  axiom, `#Ĥ⁰(Gal(L/K), C_L) = [L : K]` for `L/K` cyclic, extended to abelian `L` by
  induction along a cyclic subextension using multiplicativity of the norm index in towers;
* the one below is an OUTPUT — the same inequality *extended* to extensions ramified at
  the archimedean places, obtained (as its own docstring already records) by enlarging the
  modulus once the correspondence at modulus `1` is in hand.

So a prover who closes this leaf does NOT make the theorem below redundant, and a prover
who is tempted to "simplify" by deleting this leaf in favour of that theorem will get a
`declaration ... not found` and should stop rather than reorder the file.

**Route.** Neukirch VI (7.1) and V (7.1) (the cyclic case, via the Herbrand quotient of
the idele class group); Lang *ANT* ch. IX–X; Cassels–Fröhlich ch. VII. Artin–Tate's
*Class Field Theory* ch. VI–VII gives the class-formation version, which is the one that
states exactly this inequality with no analysis in it.

**Sanity checks.** `L = K`: `relNormClassSubgroup K K = ⊤`, index `1 ≤ 1`. `K = ℚ(√-5)`
(`h = 2`), `L = K(i)` the Hilbert class field: norm index `2 ≤ 2`. `K = ℚ`, `L = ℚ(i)`
(ramified at `2`, so not an instance of this statement, but the inequality still holds):
`h_ℚ = 1`, index `1 ≤ 2`.

**⚠ Do not drop `[IsUnramifiedAtInfinitePlaces K L]` "because the statement stays true".**
It does stay true — that is precisely what `index_relNormClassSubgroup_le_finrank` below
says — but the general form is not reachable from here, and a leaf stated more widely than
it can be proven at this point in the file is a leaf nobody can close.

**The check that would refute it**: a finite abelian extension `L/K` of number fields,
unramified at every finite prime and at every infinite place, with
`(relNormClassSubgroup K L).index > [L : K]`. -/
theorem index_relNormClassSubgroup_le_finrank_of_isUnramifiedAtInfinitePlaces
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [IsUnramifiedAtInfinitePlaces K L]
    (habel : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (hunr : ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) Q) :
    (relNormClassSubgroup K L).index ≤ Module.finrank K L :=
  sorry

/-- **THE EXISTENCE THEOREM OF UNRAMIFIED CLASS FIELD THEORY, IN ITS NORM-GROUP FORM: `K`
has a finite ABELIAN extension inside `AlgebraicClosure K`, unramified at every finite
prime and at every infinite place, EVERY ideal class of which is a norm class** (cut
2026-07-31 out of `exists_unramifiedAbelian_card_classGroup_le_finrank` below, and
DECOMPOSED AND PROVEN the same day from
`exists_unramifiedAbelian_relNormClassSubgroup_le_of_isCyclic_quotient` and
`exists_unramifiedAbelian_sup` above, and from nothing else).

**The descent, in full.** Minimise `Nat.card (relNormClassSubgroup K L)` over the
everywhere-unramified abelian `L ⊆ AlgebraicClosure K`; the set of achievable values is a
nonempty set of naturals (the cyclic leaf at `N = ⊤` supplies a member), so `Nat.sInf_mem`
gives a minimiser `L₀`. If `relNormClassSubgroup K L₀ ≠ ⊥`, pick `c ≠ 1` inside it, take an
`N` with cyclic quotient missing `c` (`exists_isCyclic_quotient_notMem`), take `L₁` with
`relNormClassSubgroup K L₁ ≤ N`, and let `M` contain both. Then
`relNormClassSubgroup K M ≤ relNormClassSubgroup K L₀` and `≤ N`, so it misses `c` and is
STRICTLY smaller — contradicting minimality. No enumeration of subgroups and no finite
induction over a family is needed, which is why the compositum leaf is only ever used on
TWO fields at a time.

`relNormClassSubgroup K L = ⊥` says `P_K · N_{L/K} I_L = P_K`, i.e. the ideal group
belonging to `L` is the trivial subgroup of `Cl(𝓞 K)` — classically, that `L` is the
Hilbert class field. The DEGREE is deliberately not mentioned: it is supplied by the
second fundamental inequality above, and separating the two is the whole point of this
cut. See that leaf's docstring for why the separation is forced.

**This is the half that is CONSTRUCTIVE, and it is where Kummer theory lives.** The
classical proof (Takagi) is: reduce to a congruence subgroup with CYCLIC quotient; adjoin
`ζ_ℓ`; run Kummer theory over `K(ζ_ℓ)` with a group of `ℓ`-virtual units; descend the NORM
GROUP by the translation theorem (Verschiebungssatz). Norm groups behave well under
composita — `Ideal.relNorm_relNorm` gives `relNormClassSubgroup K M ≤ relNormClassSubgroup
K L` whenever `L ≤ M` — so the cyclic cases can be combined, and the intersection of the
subgroups with cyclic quotient is `⊥` because characters separate a finite abelian group.
**Do not re-cut the naive "descend an unramified abelian extension from `K(ζ_ℓ)`" leaf**:
it is FALSE, with the PARI/GP witness recorded on `exists_classField_of_subgroup` below
(`K = ℚ(√29)`, `h = h⁺ = 1`, `h(K(ζ_3)) = 3`).

**Non-vacuity.** For `K = ℚ(√-5)` (`h_K = 2`) the witness is `ℚ(√-5, i)`, and
`relNormClassSubgroup K K = ⊤ ≠ ⊥`, so `L = K` is NOT admissible. It is trivial exactly
when `h_K = 1`.

**PINNING.** `relNormClassSubgroup K L = ⊥` is the whole content: it cannot be satisfied
by `L = K` unless `h_K = 1`, because `relNormClassSubgroup K K = ⊤`
(`N_{K/K} I = I`). The four instance clauses and the finite-prime clause are exactly the
hypotheses of the inequality above, which is the only consumer.

**The check that would refute this leaf**: a number field `K` for which no finite abelian
extension, unramified at every finite prime and at every infinite place, has every ideal
class of `K` in the group generated by its relative norms. -/
theorem exists_unramifiedAbelian_relNormClassSubgroup_eq_bot :
    ∃ (L : IntermediateField K (AlgebraicClosure K)) (_ : FiniteDimensional K L)
      (_ : NumberField L) (_ : IsAbelianGalois K L)
      (_ : IsUnramifiedAtInfinitePlaces K L),
      (∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime), Q ≠ ⊥ →
        Algebra.IsUnramifiedAt (𝓞 K) Q) ∧
      relNormClassSubgroup K L = ⊥ := by
  classical
  -- The set of norm-group cardinalities realised by an everywhere-unramified abelian
  -- extension of `K` inside `AlgebraicClosure K`.
  set S : Set ℕ := {n | ∃ (L : IntermediateField K (AlgebraicClosure K))
      (_ : FiniteDimensional K L) (_ : NumberField L) (_ : IsAbelianGalois K L)
      (_ : IsUnramifiedAtInfinitePlaces K L),
      (∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime), Q ≠ ⊥ →
        Algebra.IsUnramifiedAt (𝓞 K) Q) ∧
      n = Nat.card (relNormClassSubgroup K L)} with hSdef
  -- `S` is nonempty: the cyclic leaf at `N = ⊤`, whose quotient is trivial.
  have hSne : S.Nonempty := by
    haveI : Subsingleton (ClassGroup (𝓞 K) ⧸ (⊤ : Subgroup (ClassGroup (𝓞 K)))) :=
      QuotientGroup.subsingleton_quotient_top
    obtain ⟨L, hfd, hnf, hab, hinf, hunr, -⟩ :=
      exists_unramifiedAbelian_relNormClassSubgroup_le_of_isCyclic_quotient K ⊤
        isCyclic_of_subsingleton
    exact ⟨_, L, hfd, hnf, hab, hinf, hunr, rfl⟩
  -- Take an `L₀` realising the MINIMUM. Its norm class group is `⊥`.
  obtain ⟨L₀, hfd, hnf, hab, hinf, hunr, hcard⟩ := Nat.sInf_mem hSne
  haveI := hfd; haveI := hnf; haveI := hab; haveI := hinf
  refine ⟨L₀, hfd, hnf, hab, hinf, hunr, ?_⟩
  by_contra hbot
  -- Otherwise some class `c ≠ 1` survives, and a character kills it.
  obtain ⟨c, hcmem, hc1⟩ :=
    ((relNormClassSubgroup K L₀).bot_or_exists_ne_one).resolve_left hbot
  obtain ⟨N, hNcyc, hcN⟩ := exists_isCyclic_quotient_notMem K c hc1
  obtain ⟨L₁, h1fd, h1nf, h1ab, h1inf, h1unr, h1le⟩ :=
    exists_unramifiedAbelian_relNormClassSubgroup_le_of_isCyclic_quotient K N hNcyc
  obtain ⟨M, hMfd, hMnf, hMab, hMinf, hMunr, hL₀M, hL₁M⟩ :=
    exists_unramifiedAbelian_sup K L₀ L₁ hfd hnf hab hinf hunr h1fd h1nf h1ab h1inf h1unr
  haveI := hMfd; haveI := hMnf
  -- The compositum's norm class group lies below both, hence strictly below `L₀`'s.
  have hle₀ : relNormClassSubgroup K M ≤ relNormClassSubgroup K L₀ :=
    relNormClassSubgroup_le_of_le K L₀ M hL₀M
  have hleN : relNormClassSubgroup K M ≤ N :=
    le_trans (relNormClassSubgroup_le_of_le K L₁ M hL₁M) h1le
  have hlt : relNormClassSubgroup K M < relNormClassSubgroup K L₀ := by
    refine lt_of_le_of_ne hle₀ fun h => hcN (hleN ?_)
    rw [h]; exact hcmem
  have hcardlt :
      Nat.card (relNormClassSubgroup K M) < Nat.card (relNormClassSubgroup K L₀) := by
    have hss : (relNormClassSubgroup K M : Set (ClassGroup (𝓞 K))) ⊂
        (relNormClassSubgroup K L₀ : Set (ClassGroup (𝓞 K))) :=
      SetLike.coe_ssubset_coe.mpr hlt
    have := Set.Finite.card_lt_card (Set.toFinite _) hss
    simpa using this
  have hmem : Nat.card (relNormClassSubgroup K M) ∈ S :=
    ⟨M, hMfd, hMnf, hMab, hMinf, hMunr, rfl⟩
  exact absurd (Nat.sInf_le hmem) (by omega)

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
      Nat.card (ClassGroup (𝓞 K)) ≤ Module.finrank K HCF := by
  obtain ⟨L, hfd, hnf, habgal, hinf, hunr, hbot⟩ :=
    exists_unramifiedAbelian_relNormClassSubgroup_eq_bot K
  haveI := hfd; haveI := hnf; haveI := habgal; haveI := hinf
  refine ⟨L, hfd, hnf, habgal, hinf, hunr, ?_⟩
  have h := index_relNormClassSubgroup_le_finrank_of_isUnramifiedAtInfinitePlaces K L
    (fun a b => mul_comm' a b) hunr
  rwa [hbot, Subgroup.index_bot] at h

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

**The FROBENIUS clause (added 2026-07-30, and it is what makes the map an ARTIN map).**
The second conjunct says `Art [𝔭] = Frob_𝔭`; without it `Art` is merely *an* isomorphism
`Cl(𝓞 K) ≃ Gal(HCF/K)` and the dictionary clause pins it only up to an automorphism of
the quotient. It costs the proof below nothing — `hfrob`, the defining property of the
`φ` that `Art` is built from, is already in hand — and it is exactly the input that
`exists_surjective_aut_classGroupQuotient` below needs. Note the dictionary clause is
NOT needed by that consumer; the two clauses are independent exports.

**No circularity with `exists_surjective_aut_classGroupQuotient` below, and keep it that
way.** An earlier version of this proof got the `≥` half by counting, out of that leaf;
the Chebotarev-over-`F` route replaces it, so this theorem does NOT depend on it. That
was paid for and it paid off: the leaf below is now PROVEN, and its proof intersects
`L` with the `HCF` produced HERE — which would have been a cycle if this file's proof
had gone the other way. Do not reintroduce the counting shortcut.

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
        (∀ (Q : Ideal (𝓞 HCF)) (_ : Q.IsMaximal) (J : (Ideal (𝓞 K))⁰),
            (J : Ideal (𝓞 K)) = Q.under (𝓞 K) →
              Art (ClassGroup.mk0 J) = frobAt K HCF Q) ∧
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
  refine ⟨MulEquiv.ofBijective φ hbij, hfrob, ?_⟩
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
      restrictNormalHom_frobAt_of_under K (IntermediateField.lift F) HCF Q q hQover]
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
  obtain ⟨HCF, hfd, hnf, habgal, hinf, hunrHCF, Art, -, hdict⟩ :=
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

/-- **THE ARTIN MAP IN THE DIRECTION `Gal(M/K) ↠ Cl(𝓞 K)/N`, FOR `M` ALREADY INSIDE
`AlgebraicClosure K`** (PROVEN 2026-07-30 from `exists_hilbertClassField_artinIso` above
— its Artin isomorphism and its FROBENIUS clause, NOT its dictionary clause — together
with `closure_frobAt_eq_top` (CHEBOTAREV) of `Fermat/FLT/NumberField/ArtinSymbol.lean`
and the two Frobenius tower lemmas at the top of this file, and from nothing else).

This is the whole mathematical content of `exists_surjective_aut_classGroupQuotient`
below; that theorem is this one plus transport along an embedding. It is stated
separately because the argument needs `M` and the Hilbert class field to live in ONE
field, so that their compositum can be formed, and an abstract `Algebra K M` does not.

**NEITHER `IsAbelianGalois` NOR `IsUnramifiedAtInfinitePlaces` APPEARS, and that is the
point of the node.** `Gal(M/K)` may be nonabelian — the target is abelian, so `ψ` simply
factors through the abelianization — and `M/K` may be ramified at a real place, which is
exactly the case the companion file's `exists_surjective_classGroupHom_aut_of_unramified_`
`abelian` cannot reach (`K = ℚ(√3)`, `h = 1`, narrow `h⁺ = 2`). Unramifiedness at the
FINITE primes is load-bearing: it is what makes `restrictScalars_frobAt` applicable at
the prime of `M` below each prime of the compositum.

**The argument.** Write `N = relNormClassSubgroup K M`, let `HCF` and
`Art : Cl(𝓞 K) ≃ Gal(HCF/K)` be the Hilbert class field and its Artin isomorphism, and
let `F` be the fixed field, inside `HCF`, of the subgroup `Art N`. The theorem is the
single geometric fact

  **`F ⊆ M`** — the class field of the norm group of `M` is contained in `M`,

after which everything is the Galois correspondence: restriction `Gal(M/K) ↠ Gal(F/K)`
is surjective because `F/K` is normal (a subextension of the abelian `HCF/K`), and
`Gal(F/K) ≃ Gal(HCF/K) ⧸ Art N ≃ Cl(𝓞 K) ⧸ N` by `IsGalois.normalAutEquivQuotient`
(using `fixingSubgroup_fixedField`) and `QuotientGroup.congr` along `Art`.

`F ⊆ M` is CHEBOTAREV over `M`, applied to the compositum `E = HCF ⬝ M`. Every
`σ ∈ Gal(E/M)` restricts, on `HCF`, into `Art N`: by Chebotarev it is enough to check
this on the Frobenius elements `Frob_{E/M, 𝔔}`, and for those the two tower lemmas give

  `Frob_{E/M,𝔔}|_{HCF} = (Frob_{E/K,𝔔} ^ f(𝔮|𝔭))|_{HCF} = Frob_{HCF/K,𝔓} ^ f(𝔮|𝔭)
                        = Art([𝔭]) ^ f(𝔮|𝔭) = Art([N_{M/K} 𝔮])`,

where `𝔮 = 𝔔 ∩ 𝓞 M` and `𝔭 = 𝔔 ∩ 𝓞 K`, the third equality being the Frobenius clause of
`exists_hilbertClassField_artinIso` and the fourth `N_{M/K} 𝔮 = 𝔭 ^ f`. That last class
is a generator of `N`, so the restriction lies in `Art N`. Hence every element of `F`,
which `Art N` fixes pointwise, is fixed by all of `Gal(E/M)` — and `E/M` is Galois, so
it lies in `M`.

**Why the DICTIONARY clause of `exists_hilbertClassField_artinIso` is not used, though
its docstring's sketch suggested it would be.** That sketch intersected `M` with `HCF`
and identified the norm class group of the intersection. The route taken here never
forms the intersection: it goes straight for the fixed field `F` of `Art N`, for which
`fixingSubgroup F = Art N` is `IsGalois.fixingSubgroup_fixedField` rather than a
class-field statement. Only the Frobenius clause is needed, and the inclusion
`N_{M∩HCF} ≤ N_M` that the sketch called "the theorem" is subsumed by `F ⊆ M`. -/
theorem exists_surjective_aut_classGroupQuotient_intermediateField
    (M : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K M] [NumberField M]
    [IsGalois K M]
    (hunr : ∀ (Q : Ideal (𝓞 M)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) Q) :
    ∃ ψ : (M ≃ₐ[K] M) →* ClassGroup (𝓞 K) ⧸ relNormClassSubgroup K M,
      Function.Surjective ψ := by
  classical
  obtain ⟨HCF, hfd, hnf, habgal, hinf, hunrHCF, Art, hArtFrob, -⟩ :=
    exists_hilbertClassField_artinIso K
  haveI := hfd; haveI := hnf; haveI := habgal
  set N : Subgroup (ClassGroup (𝓞 K)) := relNormClassSubgroup K M with hNdef
  set A : ClassGroup (𝓞 K) →* (HCF ≃ₐ[K] HCF) :=
    (Art : ClassGroup (𝓞 K) →* (HCF ≃ₐ[K] HCF)) with hAdef
  set H : Subgroup (HCF ≃ₐ[K] HCF) := N.map A with hHdef
  haveI hHnormal : H.Normal := inferInstance
  set F : IntermediateField K HCF := IntermediateField.fixedField H with hFdef
  set F' : IntermediateField K (AlgebraicClosure K) := IntermediateField.lift F with hF'def
  have hF'HCF : F' ≤ HCF := IntermediateField.lift_le F
  -- ## The compositum `E = HCF ⬝ M`, and the tower instances it carries
  set E : IntermediateField K (AlgebraicClosure K) := HCF ⊔ M with hEdef
  have hHCFE : HCF ≤ E := le_sup_left
  have hME : M ≤ E := le_sup_right
  haveI : NumberField E := NumberField.of_module_finite K E
  haveI : IsGalois K E := ⟨⟩
  letI : Algebra HCF E := (IntermediateField.inclusion hHCFE).toRingHom.toAlgebra
  haveI : IsScalarTower K HCF E :=
    IsScalarTower.of_algebraMap_eq' (IntermediateField.inclusion hHCFE).comp_algebraMap.symm
  letI : Algebra M E := (IntermediateField.inclusion hME).toRingHom.toAlgebra
  haveI : IsScalarTower K M E :=
    IsScalarTower.of_algebraMap_eq' (IntermediateField.inclusion hME).comp_algebraMap.symm
  haveI : IsGalois M E := IsGalois.tower_top_of_isGalois K M E
  -- ## CHEBOTAREV over `M`: the image of `Gal(E/M)` in `Gal(HCF/K)` lies in `Art N`
  set Φ : (E ≃ₐ[M] E) →* (HCF ≃ₐ[K] HCF) :=
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := E) HCF).comp
      (AlgEquiv.restrictScalarsHom (R := K) (S := M) (A := E)) with hΦdef
  have hΦmem : ∀ σ : E ≃ₐ[M] E, Φ σ ∈ H := by
    intro σ
    have hgen : (⊤ : Subgroup (E ≃ₐ[M] E)) ≤ Subgroup.comap Φ H := by
      rw [← closure_frobAt_eq_top M E]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨Q, hQmax, hQunr, rfl⟩
      haveI := hQmax
      haveI := hQunr
      have hQ0 : Q ≠ ⊥ :=
        (Ideal.bot_lt_of_maximal Q (NumberField.RingOfIntegers.not_isField _)).ne'
      have hq0 : Q.under (𝓞 M) ≠ ⊥ := Ideal.under_ne_bot (𝓞 M) hQ0
      haveI hqmax : (Q.under (𝓞 M)).IsMaximal :=
        (Ideal.IsPrime.under (𝓞 M) (P := Q)).isMaximal hq0
      haveI : Algebra.IsUnramifiedAt (𝓞 K) (Q.under (𝓞 M)) := hunr _ hqmax.isPrime hq0
      have hP0 : Q.under (𝓞 HCF) ≠ ⊥ := Ideal.under_ne_bot (𝓞 HCF) hQ0
      haveI hPmax : (Q.under (𝓞 HCF)).IsMaximal :=
        (Ideal.IsPrime.under (𝓞 HCF) (P := Q)).isMaximal hP0
      haveI : Algebra.IsUnramifiedAt (𝓞 K) (Q.under (𝓞 HCF)) := hunrHCF _ hPmax.isPrime hP0
      have hpne : (Q.under (𝓞 M)).under (𝓞 K) ≠ ⊥ := Ideal.under_ne_bot (𝓞 K) hq0
      have hJne : Ideal.relNorm (𝓞 K) (Q.under (𝓞 M)) ≠ ⊥ := by
        simpa using (Ideal.relNorm_eq_bot_iff (R := 𝓞 K)
          (I := Q.under (𝓞 M))).not.mpr hq0
      set J : (Ideal (𝓞 K))⁰ := ⟨Ideal.relNorm (𝓞 K) (Q.under (𝓞 M)),
        mem_nonZeroDivisors_of_ne_zero hJne⟩ with hJdef
      set Jp : (Ideal (𝓞 K))⁰ := ⟨(Q.under (𝓞 M)).under (𝓞 K),
        mem_nonZeroDivisors_of_ne_zero hpne⟩ with hJpdef
      have hmemN : ClassGroup.mk0 J ∈ N :=
        Subgroup.subset_closure ⟨Q.under (𝓞 M), hq0, rfl⟩
      have hJpow : J = Jp ^ (Q.under (𝓞 M)).inertiaDeg (𝓞 K) := by
        refine Subtype.ext ?_
        rw [SubmonoidClass.coe_pow]
        exact Ideal.relNorm_eq_pow_of_isMaximal (Q.under (𝓞 M)) ((Q.under (𝓞 M)).under (𝓞 K))
      have hval : Φ (frobAt M E Q) = A (ClassGroup.mk0 J) := by
        show AlgEquiv.restrictNormalHom HCF
          (AlgEquiv.restrictScalars K (frobAt M E Q)) = _
        rw [restrictScalars_frobAt K M E Q (Q.under (𝓞 M)) rfl, map_pow,
          restrictNormalHom_frobAt_of_under K HCF E Q (Q.under (𝓞 HCF)) rfl, hJpow, map_pow, map_pow]
        congr 1
        refine (hArtFrob (Q.under (𝓞 HCF)) hPmax Jp ?_).symm
        show (Q.under (𝓞 M)).under (𝓞 K) = (Q.under (𝓞 HCF)).under (𝓞 K)
        rw [Ideal.under_under, Ideal.under_under]
      show Φ (frobAt M E Q) ∈ H
      rw [hval, hHdef]
      exact Subgroup.mem_map_of_mem A hmemN
    exact Subgroup.mem_comap.1 (hgen trivial)
  -- ## The class field of `N` sits inside `M`
  have hFM : F' ≤ M := by
    intro x hx
    have hxHCF : x ∈ HCF := hF'HCF hx
    have hxE : x ∈ E := hHCFE hxHCF
    have hxF : (⟨x, hxHCF⟩ : HCF) ∈ F := (IntermediateField.mem_lift (⟨x, hxHCF⟩ : HCF)).1 hx
    have hfix : ∀ σ : E ≃ₐ[M] E, σ ⟨x, hxE⟩ = ⟨x, hxE⟩ := by
      intro σ
      have h1 : Φ σ ⟨x, hxHCF⟩ = ⟨x, hxHCF⟩ :=
        (IntermediateField.mem_fixedField_iff H _).1 hxF _ (hΦmem σ)
      have h2 := AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars K σ) HCF
        (⟨x, hxHCF⟩ : HCF)
      rw [show (AlgEquiv.restrictScalars K σ).restrictNormal HCF = Φ σ from rfl, h1] at h2
      exact h2.symm
    obtain ⟨y, hy⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (⟨x, hxE⟩ : E)).2 hfix
    have hxy : (y : AlgebraicClosure K) = x := congrArg Subtype.val hy
    rw [← hxy]
    exact y.2
  -- ## `Gal(M/K) ↠ Gal(F/K) ≃ Gal(HCF/K)/Art N ≃ Cl(𝓞 K)/N`
  set F'' : IntermediateField K M := IntermediateField.restrict hFM with hF''def
  set eFF'' : (F : IntermediateField K HCF) ≃ₐ[K] F'' :=
    (IntermediateField.liftAlgEquiv F).trans (IntermediateField.restrict_algEquiv hFM) with heF
  haveI : Normal K F'' := Normal.of_algEquiv eFF''
  have hsurj0 : Function.Surjective
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) F'') :=
    AlgEquiv.restrictNormalHom_surjective M
  set ψ₁ : (F'' ≃ₐ[K] F'') ≃* (F ≃ₐ[K] F) := AlgEquiv.autCongr eFF''.symm with hψ₁
  set ψ₂ : (F ≃ₐ[K] F) ≃* ((HCF ≃ₐ[K] HCF) ⧸ H) :=
    (IsGalois.normalAutEquivQuotient H).symm with hψ₂
  set ψ₃ : ((HCF ≃ₐ[K] HCF) ⧸ H) ≃* (ClassGroup (𝓞 K) ⧸ N) :=
    (QuotientGroup.congr N H Art hHdef.symm).symm with hψ₃
  refine ⟨((ψ₃.toMonoidHom.comp ψ₂.toMonoidHom).comp ψ₁.toMonoidHom).comp
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) F''), ?_⟩
  simp only [MonoidHom.coe_comp]
  exact ψ₃.surjective.comp (ψ₂.surjective.comp (ψ₁.surjective.comp hsurj0))

/-- **THE ARTIN MAP AT MODULUS `1`, IN THE DIRECTION `Gal(L/K) ↠ Cl(𝓞 K)/N`: for
`L/K` finite abelian and unramified at every finite prime there is a SURJECTIVE
homomorphism `Gal(L/K) →* Cl(𝓞 K) ⧸ relNormClassSubgroup K L`** (was a SORRY LEAF, cut
2026-07-30 out of `index_relNormClassSubgroup_le_finrank` below; PROVEN 2026-07-30 from
`exists_surjective_aut_classGroupQuotient_intermediateField` above by transport along an
embedding, and from nothing else).

This is the mirror image of the cut the companion file made on 2026-07-28, where
`finrank_le_index_relNormClassSubgroup` was reduced to
`exists_surjective_classGroupHom_aut_of_unramified_abelian` — the surjection
`Cl(𝓞 K) ↠ Gal(L/K)`. **The two nodes are genuinely different theorems and
neither implies the other**: that one is FALSE for extensions ramified at an
infinite place (its docstring records `K = ℚ(√3)`, `h = 1`, narrow `h⁺ = 2`), and
this one is true for all of them — which is exactly why
`IsUnramifiedAtInfinitePlaces` must NOT be added here (see the ⚠ note on the
consumer below).

**What this theorem adds to the node above: TRANSPORT.** `L` is an abstract
`Algebra K L`, while the Hilbert class field lives inside `AlgebraicClosure K`, and the
argument needs the two in one field. `IsAlgClosed.lift` embeds `L` as the intermediate
field `L' = ι.fieldRange`, and the three things that must be carried across
`e : L ≃ₐ[K] L'` are `relNormClassSubgroup` (`relNormClassSubgroup_eq_of_algEquiv`),
unramifiedness at the finite primes (`isUnramifiedAt_ringOfIntegers_of_algEquiv`) and `Gal`
(`AlgEquiv.autCongr`); the quotient types are then identified by
`QuotientGroup.quotientMulEquivOfEq`. The first two are the plumbing built in the
`Transport` section at the top of this file, and they are the reusable part: the pin has
no API for moving rings of integers and their primes along a `K`-algebra isomorphism.

**⚠ `habel` IS NOT USED — and this is now a fact about the proof, not a claim about the
mathematics.** The binder is retained (renamed `_habel`) because every consumer holds it
and because removing it would change the signature; the argument never touches it, since
`Cl(𝓞 K) ⧸ N` is abelian and `ψ` may simply factor through the abelianization of
`Gal(L/K)`. `hunr` **is** load-bearing, at the finite primes only. Note in particular
that the general (possibly nonabelian) statement is available directly from
`exists_surjective_aut_classGroupQuotient_intermediateField` above.

**PINNING.** Only surjectivity is used, and the inequality below follows from ANY
surjective hom, so an adversary who post-composes an automorphism of the quotient still
yields a true consumer. The `ψ` produced here is the canonical one — restriction to the
class field of `N`, followed by the inverse Artin map.

**Sanity checks against the classical statement.** `L = K`: `N = ⊤`, the target is
trivial and `ψ` is the trivial map. `K = ℚ(√-5)` (`h = 2`), `L = K(i)` the Hilbert class
field: `N = ⊥` and `ψ` is an isomorphism of groups of order `2`. `K = ℚ(√3)` (`h = 1`,
`h⁺ = 2`), `L` the NARROW Hilbert class field, ramified at a real place: `Cl(𝓞 K)` is
trivial, so the target is trivial and `ψ` is again the trivial map — the case that makes
the companion file's opposite surjection false and this one true.

**The check that would refute it**: a finite abelian extension `L/K` of number
fields, unramified at every finite prime, for which no group homomorphism
`Gal(L/K) → Cl(𝓞 K) ⧸ relNormClassSubgroup K L` is surjective — equivalently
(by the counting below) one with `(relNormClassSubgroup K L).index > [L : K]`. -/
theorem exists_surjective_aut_classGroupQuotient [IsGalois K L]
    (_habel : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (hunr : ∀ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) Q) :
    ∃ ψ : (L ≃ₐ[K] L) →* ClassGroup (𝓞 K) ⧸ relNormClassSubgroup K L,
      Function.Surjective ψ := by
  classical
  set ι : L →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift with hι
  set L' : IntermediateField K (AlgebraicClosure K) := ι.fieldRange with hL'
  set e : L ≃ₐ[K] L' := AlgEquiv.ofInjectiveField ι with he
  haveI : FiniteDimensional K L' := e.toLinearEquiv.finiteDimensional
  haveI : NumberField L' := NumberField.of_module_finite K L'
  haveI : IsGalois K L' := IsGalois.of_algEquiv e
  have hunr' : ∀ (Q : Ideal (𝓞 L')) (_ : Q.IsPrime), Q ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 K) Q :=
    fun Q hQ hQ0 => isUnramifiedAt_ringOfIntegers_of_algEquiv e hunr Q hQ hQ0
  obtain ⟨ψ', hψ'⟩ := exists_surjective_aut_classGroupQuotient_intermediateField K L' hunr'
  have hN : relNormClassSubgroup K L = relNormClassSubgroup K L' :=
    relNormClassSubgroup_eq_of_algEquiv e
  refine ⟨((QuotientGroup.quotientMulEquivOfEq hN.symm).toMonoidHom.comp ψ').comp
    (AlgEquiv.autCongr e).toMonoidHom, ?_⟩
  simp only [MonoidHom.coe_comp]
  exact ((QuotientGroup.quotientMulEquivOfEq hN.symm).surjective.comp hψ').comp
    (AlgEquiv.autCongr e).surjective

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
