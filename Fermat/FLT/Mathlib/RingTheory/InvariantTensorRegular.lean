/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Fermat.FLT.Mathlib.RingTheory.InvariantBaseChange
public import Fermat.FLT.Mathlib.RingTheory.InvariantCoarseRing
public import Fermat.FLT.Mathlib.RingTheory.RegularLocalNormal
public import Fermat.FLT.Mathlib.AlgebraicGeometry.SmoothConnectedCriteria
public import Fermat.FLT.Mathlib.AlgebraicGeometry.Morphisms.SmoothReduced
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# The invariants of a smooth curve algebra are geometrically regular

Let `k` be a field, `S` a smooth `k`-algebra of Krull dimension one, `G` a finite group
acting on `S` by `k`-algebra automorphisms and `R = S^G` its ring of invariants, embedded
in `S`.  This module proves

  `isRegularRing_tensorProduct_of_isInvariant : IsRegularRing (K ⊗[k] R)`

for every ALGEBRAIC field extension `K/k` — in the application `K = k̄`, and the point of
the base change is that `IsRegularRing R` alone is strictly weaker over an imperfect `k`
and does not give smoothness (the standing witness is the quasi-elliptic
`y² = x³ + t` over `𝔽₃(t)`, recorded on
`smoothOfRelativeDimension_specMap_algebraMap_of_isRegularRing`).

## What is proven here and what is left

Everything about the BASE CHANGE is proven:

* `R ⊗[k] K` is the ring of invariants of `S ⊗[k] K` — this is
  `Fermat.InvariantBaseChange.isInvariant_tensor`, since a field extension is flat;
* `S ⊗[k] K` is smooth over `K` — `Algebra.Smooth.baseChange`, transported across
  `Algebra.TensorProduct.commRight` because mathlib states the instance for `K ⊗[k] S`
  and the invariant machinery is written for `S ⊗[k] K`;
* `ringKrullDim (S ⊗[k] K) = ringKrullDim S`.  **No dimension theory of finite-type
  algebras is needed for this, and that is worth knowing**: because `K/k` is ALGEBRAIC,
  `S ⊗[k] K` is INTEGRAL over `S` (`Algebra.IsIntegral.tensorProduct`) and `S` injects
  into it (`Algebra.TensorProduct.includeLeft_injective`, `S` being flat over the field
  `k`), so `ringKrullDim_eq_of_isIntegral_of_injective` applies verbatim.  A route through
  "Krull dimension is invariant under base field extension" — which the leaf's docstring in
  `ModularCurve/X1.lean` named as one of the three missing general theorems — would have
  been a genuine piece of missing theory; it is not needed at an algebraic extension.

## What is left (2026-08-02)

`isRegularRing_of_isInvariant_of_smooth` — the theorem the base change consumes, and which
used to be the leaf — is now **PROVEN**, and so is
`isIntegrallyClosed_localizationAtPrime_of_isInvariant_of_smooth`.  **What is left is ONE
leaf, `isIntegrallyClosed_of_forall_localizationAtPrime`, and it is pure commutative
algebra**: no group, no smoothness, no invariants, no tensor product, no dimension —

  *a noetherian ring all of whose localizations at primes are integrally closed DOMAINS is
  integrally closed in its total quotient ring.*

It is the non-domain case of `Mathlib/RingTheory/LocalProperties/IntegrallyClosed.lean`, every
result of which carries `[IsDomain R]`, and its docstring carries the conductor proof, the
faithfulness audit for both hypotheses, and where in the tree it belongs.

The old leaf bundled three things, and they have separated:

* **`IsDomain`** — which the old docstring called *"the whole difficulty"* and proposed to
  settle by a `G`-equivariant product decomposition of `S` — is PROVEN here as
  `isDomain_localizationAtPrime_of_isInvariant`, with no decomposition: `IsRegularRing` is a
  LOCAL condition, and `ker (R → R_p) = ker (S → S_P) ∩ R` for any prime `P` of `S` over `p`,
  by prime avoidance over one `G`-orbit plus a norm.  Every localization of `S` at a prime is
  a domain because it is regular local
  (`Algebra.Smooth.isRegularLocalRing_of_isLocalizationAtPrime`, `RegularLocalNormal.lean`).
* **The localization of the invariant setup**, which the classical route needs and which
  costs NOTHING: `InvariantBaseChange.isInvariant_tensor` at `k = B = R`, `K = R_p` gives
  `Algebra.IsInvariant (R ⊗[R] R_p) (S ⊗[R] R_p) G`, and `S ⊗[R] R_p` is recognised by
  `inferInstance` as the localization of `S` at the image of `R ∖ p`.
* **NORMALITY**, which is the residue, and which is now a statement about a ring and nothing
  else.
-/

@[expose] public section

open scoped TensorProduct Pointwise

namespace Fermat.InvariantTensorRegular

/-! ### Kernels of localization maps

Two elementary facts about `A → M⁻¹A`, isolated because the argument below reads the
localization only through its kernel.  For a localization the kernel is
`{a | ∃ m ∈ M, m * a = 0}`, and it is PRIME exactly when the localization is a domain — which
is what makes "is a domain" checkable by an ideal-theoretic computation upstairs. -/

/-- Membership in the kernel of a localization map. -/
theorem mem_ker_algebraMap_iff {A : Type} [CommRing A] (M : Submonoid A)
    (L : Type) [CommRing L] [Algebra A L] [IsLocalization M L] (a : A) :
    a ∈ RingHom.ker (algebraMap A L) ↔ ∃ m : M, (m : A) * a = 0 := by
  rw [RingHom.mem_ker, IsLocalization.map_eq_zero_iff M]

/-- **A localization whose structure map has PRIME kernel has no zero divisors.**  (The
converse is `Ideal.comap_isPrime` of `⊥`, used below.) -/
theorem noZeroDivisors_of_isPrime_ker {A : Type} [CommRing A] (M : Submonoid A)
    (L : Type) [CommRing L] [Algebra A L] [IsLocalization M L]
    (h : (RingHom.ker (algebraMap A L)).IsPrime) : NoZeroDivisors L := by
  refine ⟨fun {x y} hxy => ?_⟩
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M x
  obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective M y
  dsimp only at hxy ⊢
  rw [← IsLocalization.mk'_mul, IsLocalization.mk'_eq_zero_iff] at hxy
  have hab : a * b ∈ RingHom.ker (algebraMap A L) := (mem_ker_algebraMap_iff M L _).mpr hxy
  rcases h.mem_or_mem hab with hh | hh
  · exact Or.inl ((IsLocalization.mk'_eq_zero_iff _ _).mpr ((mem_ker_algebraMap_iff M L a).mp hh))
  · exact Or.inr ((IsLocalization.mk'_eq_zero_iff _ _).mpr ((mem_ker_algebraMap_iff M L b).mp hh))

/-! ### The invariant ring's localizations at primes are DOMAINS

This is the half of the leaf that its docstring called "the whole difficulty", and it is
closed here.  See `isDomain_localizationAtPrime_of_isInvariant` for the argument. -/

section IsDomain

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]

/-- The annihilator of an element, as an ideal.  (Only used to feed prime avoidance.) -/
def annihilatorIdeal (x : S) : Ideal S where
  carrier := {t : S | t * x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv
    simp only [Set.mem_setOf_eq] at *
    rw [add_mul, hu, hv, add_zero]
  smul_mem' := by
    intro c u hu
    simp only [Set.mem_setOf_eq] at *
    rw [smul_eq_mul, mul_assoc, hu, mul_zero]

theorem mem_annihilatorIdeal {x t : S} : t ∈ annihilatorIdeal x ↔ t * x = 0 := Iff.rfl

variable (G : Type) [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]

omit [Finite G] in
/-- The image of `R` is fixed by `G` — `SMulCommClass G R S` in the form the arguments below
use it. -/
theorem smul_algebraMap_of_smulCommClass (g : G) (a : R) :
    g • (algebraMap R S a) = algebraMap R S a := by
  rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]

/-- **AN ANNIHILATOR UPSTAIRS DESCENDS TO ONE DOWNSTAIRS** (PROVEN).  If some element of `S`
outside a prime `P` kills `algebraMap R S a`, then some element of `R` outside `p = P ∩ R`
kills `a`.

Equivalently: `ker (R → S_P) = ker (R → R_p)`, one inclusion being trivial.  This is the only
place the GROUP does any work in the domain half, and it does it twice:

* the annihilator `J` of `algebraMap R S a` is `G`-STABLE, because `a` is `G`-invariant; so
  the single witness `t ∉ P` gives `g • t ∈ J ∖ (g • P)` for every `g`, i.e. `J` avoids the
  whole `G`-orbit of `P`.  **Prime avoidance** over that finite orbit then produces ONE
  `u ∈ J` outside every `g • P` — and that uniformity is exactly what a single `t` does not
  give;
* the norm `N = ∏_{g} g • u` is `G`-invariant, hence comes from `R` by
  `Algebra.IsInvariant`; it still kills `algebraMap R S a` (one of its factors does), and it
  is outside `P` because `P.primeCompl` is a submonoid containing every `g • u`.

`hinj` is used only at the last line, to turn `algebraMap R S (v * a) = 0` into `v * a = 0`. -/
theorem exists_notMem_mul_eq_zero_of_isInvariant [Algebra.IsInvariant R S G]
    (hinj : Function.Injective (algebraMap R S))
    (p : Ideal R) (P : Ideal S) [hP : P.IsPrime] (hPp : P.comap (algebraMap R S) = p)
    (a : R) (t : S) (ht : t ∉ P) (hta : t * algebraMap R S a = 0) :
    ∃ v ∉ p, v * a = 0 := by
  classical
  cases nonempty_fintype G
  set x := algebraMap R S a with hxdef
  have hgx : ∀ g : G, g • x = x := fun g => smul_algebraMap_of_smulCommClass G g a
  -- the annihilator of `x` avoids every `G`-conjugate of `P`
  have hJ : ∀ g : G, ¬ (annihilatorIdeal x ≤ g • P) := by
    intro g hle
    apply ht
    have hmem : g • t ∈ annihilatorIdeal x := by
      rw [mem_annihilatorIdeal]
      calc (g • t) * x = (g • t) * (g • x) := by rw [hgx g]
        _ = g • (t * x) := (smul_mul' g t x).symm
        _ = 0 := by rw [hta, smul_zero]
    have h2 := hle hmem
    rwa [Ideal.smul_mem_pointwise_smul_iff] at h2
  -- prime avoidance over the finite family `{g • P}`
  obtain ⟨u, huJ, huP⟩ : ∃ u ∈ annihilatorIdeal x, ∀ g : G, u ∉ g • P := by
    by_contra hcon
    push Not at hcon
    have hsub : ((annihilatorIdeal x : Ideal S) : Set S) ⊆
        ⋃ g ∈ (↑(Finset.univ : Finset G) : Set G),
          (((fun g : G => g • P) g : Ideal S) : Set S) := by
      intro u hu
      obtain ⟨g, hg⟩ := hcon u hu
      exact Set.mem_biUnion (by simp) hg
    obtain ⟨g, -, hg⟩ :=
      (Ideal.subset_union_prime (1 : G) (1 : G) (fun i _ _ _ => inferInstance)).mp hsub
    exact hJ g hg
  -- the norm of `u` is `G`-invariant, kills `x`, and stays outside `P`
  set N : S := ∏ g : G, g • u with hNdef
  have hNa : N * x = 0 := by
    have hsplit : N = u * ∏ g ∈ Finset.univ.erase (1 : G), g • u := by
      rw [hNdef, ← Finset.mul_prod_erase Finset.univ (fun g : G => g • u)
        (Finset.mem_univ (1 : G)), one_smul]
    rw [hsplit, mul_comm u _, mul_assoc, (mem_annihilatorIdeal.mp huJ), mul_zero]
  have hNinv : ∀ h : G, h • N = N := by
    intro h
    rw [hNdef, Finset.smul_prod']
    exact Fintype.prod_equiv (Equiv.mulLeft h) _ _ (fun g => by rw [smul_smul]; rfl)
  have hNP : N ∉ P := by
    have hfac : ∀ g : G, g • u ∈ P.primeCompl := by
      intro g hg
      refine huP g⁻¹ ?_
      have h3 : g⁻¹ • (g • u) ∈ g⁻¹ • P := Ideal.smul_mem_pointwise_smul _ _ _ hg
      rwa [inv_smul_smul] at h3
    exact Submonoid.prod_mem _ (fun g _ => hfac g)
  obtain ⟨v, hv⟩ := Algebra.IsInvariant.isInvariant (A := R) (G := G) N hNinv
  refine ⟨v, ?_, ?_⟩
  · intro hvp
    rw [← hPp] at hvp
    exact hNP (hv ▸ hvp)
  · apply hinj
    rw [map_mul, hv, map_zero, ← hxdef]
    exact hNa

/-- **THE LOCALIZATION OF AN INVARIANT RING AT A PRIME IS A DOMAIN**, as soon as every
localization of `S` at a prime is (PROVEN 2026-08-02).

This is what the leaf's own docstring identified as the obstruction — *"`IsDomain` is the
whole difficulty, and it is not available"* — and it does not need the product decomposition
that docstring prescribed.  What replaces it:

* `ker (R → R_p)` is the ONLY thing that has to be shown prime: a localization whose
  structure map has prime kernel has no zero divisors
  (`noZeroDivisors_of_isPrime_ker`), and `R_p` is nontrivial because `p ≠ ⊤`;
* upstairs, `ker (S → S_P)` IS prime, because `S_P` is a domain — it is the comap of `⊥`;
* and `exists_notMem_mul_eq_zero_of_isInvariant` says the two kernels CORRESPOND:
  `ker (R → R_p) = ker (S → S_P) ∩ R` for any prime `P` of `S` over `p`.  So primeness
  descends.

Geometrically: `p` contains a UNIQUE minimal prime of `R`, because a prime of `S` over `p`
contains a unique minimal prime of `S` (that is `S_P` being a domain) and `G` moves the
primes over `p` transitively — the transitivity being what makes the choice of `P` immaterial.

**No hypothesis on `S` beyond `hSdom` is used**: not reducedness, not noetherianity, not
finite type, not the dimension.  `hinj` is used only inside
`exists_notMem_mul_eq_zero_of_isInvariant`, and `[Finite G]` twice (integrality, and the
norm). -/
theorem isDomain_localizationAtPrime_of_isInvariant [Algebra.IsInvariant R S G]
    (hinj : Function.Injective (algebraMap R S))
    (hSdom : ∀ (P : Ideal S) [P.IsPrime], IsDomain (Localization.AtPrime P))
    (p : Ideal R) [hp : p.IsPrime] :
    IsDomain (Localization.AtPrime p) := by
  haveI : Algebra.IsIntegral R S := Algebra.IsInvariant.isIntegral R S G
  have hker : RingHom.ker (algebraMap R S) = ⊥ := (RingHom.injective_iff_ker_eq_bot _).mp hinj
  obtain ⟨P, -, hPprime, hPc⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (R := R) (S := S) p (⊥ : Ideal S)
      (by simp [← RingHom.ker_eq_comap_bot, hker])
  haveI := hPprime
  haveI : (RingHom.ker (algebraMap S (Localization.AtPrime P))).IsPrime := by
    haveI := hSdom P
    rw [RingHom.ker_eq_comap_bot]
    exact Ideal.comap_isPrime _ _
  have hkerprime : (RingHom.ker (algebraMap R (Localization.AtPrime p))).IsPrime := by
    constructor
    · intro htop
      have h1 : (1 : R) ∈ RingHom.ker (algebraMap R (Localization.AtPrime p)) := htop ▸ trivial
      rw [RingHom.mem_ker, map_one] at h1
      exact one_ne_zero h1
    · intro a b hab
      rw [mem_ker_algebraMap_iff p.primeCompl] at hab
      obtain ⟨⟨v, hv⟩, hvab⟩ := hab
      -- replace `a` by `v * a`, so that `(v * a) * b = 0` on the nose
      have hva : (v * a) * b = 0 := by rw [mul_assoc]; exact hvab
      have hmapzero : algebraMap R S (v * a) * algebraMap R S b = 0 := by
        rw [← map_mul, hva, map_zero]
      have hmem : algebraMap R S (v * a) * algebraMap R S b
          ∈ RingHom.ker (algebraMap S (Localization.AtPrime P)) := by
        rw [RingHom.mem_ker, hmapzero, map_zero]
      rcases Ideal.IsPrime.mem_or_mem ‹_› hmem with hh | hh
      · left
        rw [mem_ker_algebraMap_iff P.primeCompl] at hh
        rw [mem_ker_algebraMap_iff p.primeCompl]
        obtain ⟨⟨t, ht⟩, hta⟩ := hh
        obtain ⟨w, hw, hwa⟩ :=
          exists_notMem_mul_eq_zero_of_isInvariant G hinj p P hPc (v * a) t ht hta
        exact ⟨⟨w * v, Submonoid.mul_mem _ hw hv⟩, by rw [mul_assoc]; exact hwa⟩
      · right
        rw [mem_ker_algebraMap_iff P.primeCompl] at hh
        rw [mem_ker_algebraMap_iff p.primeCompl]
        obtain ⟨⟨t, ht⟩, htb⟩ := hh
        obtain ⟨w, hw, hwb⟩ :=
          exists_notMem_mul_eq_zero_of_isInvariant G hinj p P hPc b t ht htb
        exact ⟨⟨w, hw⟩, hwb⟩
  haveI := noZeroDivisors_of_isPrime_ker p.primeCompl (Localization.AtPrime p) hkerprime
  exact NoZeroDivisors.to_isDomain _

end IsDomain

/-! ### The residual leaf: normality is a local property for a ring with local domains

This is the whole of what is left, and it is general commutative algebra — no group, no
smoothness, no invariants, no tensor product. -/

/-- **A NOETHERIAN RING ALL OF WHOSE LOCALIZATIONS AT PRIMES ARE INTEGRALLY CLOSED DOMAINS
IS INTEGRALLY CLOSED IN ITS TOTAL QUOTIENT RING** (sorry leaf).

`IsIntegrallyClosed A` is mathlib's `IsIntegralClosure A A (FractionRing A)` with
`FractionRing A = Localization (nonZeroDivisors A)`, i.e. the TOTAL quotient ring, so the
statement is meaningful for a ring that is not a domain — and that is the point.  `A` here is
a product of Dedekind domains in disguise; `hdom` is exactly the hypothesis that says its
`Spec` is a disjoint union rather than a gluing.

## WHY IT IS A LEAF: every local–global lemma for `IsIntegrallyClosed` at this pin carries `[IsDomain]`

Checked 2026-08-02 against `Mathlib/RingTheory/LocalProperties/IntegrallyClosed.lean`: of its
five results, `IsIntegrallyClosed.of_localization_submonoid`, `.of_localization`,
`.of_localization_maximal`, `.of_isLocalization_maximal` and
`isIntegrallyClosed_ofLocalizationMaximal`, **every one is stated under `[IsDomain R]`** — the
last one literally as `OfLocalizationMaximal fun R _ => ([IsDomain R] → IsIntegrallyClosed R)`.
There is no `IsNormalRing` in mathlib at this pin (`grep`: zero hits), and no structure theory
of reduced normal noetherian rings, so the "finite product of normal domains" route is not
available either.

## THE PROOF, WHICH IS THE CONDUCTOR ARGUMENT AND NEEDS NO PRODUCT DECOMPOSITION

Let `z ∈ Q(A)` be integral over `A` and let `I = {a : A | a • z ∈ range (algebraMap A (Q A))}`
be its conductor — an ideal, containing the denominator of `z`, and `z ∈ A` exactly when
`1 ∈ I`.  Suppose `I ≤ m` for a maximal `m`.  Then:

* **`nonZeroDivisors A` maps into `nonZeroDivisors A_m`.**  `A_m` is a domain by `hdom`, so
  `ker (A → A_m)` is prime (the comap of `⊥`), and it is contained in every prime `≤ m`
  — if `t ∉ m` and `t a = 0` then `a` lies in every prime below `m`, `t` lying in none.  A
  non-zero-divisor `u` avoids every minimal prime, hence avoids `ker (A → A_m)`, hence is
  nonzero in the domain `A_m`.
* So there is a ring map `Q(A) → Frac(A_m)` over `A`, and the image of `z` is integral over
  `A_m`, hence lies in `A_m` by `hic`.
* Writing `z = x / u` with `u ∈ nonZeroDivisors A`, that says `s * x - a * u ↦ 0` in `A_m` for
  some `a` and `s ∉ m`, i.e. `t * (s * x - a * u) = 0` in `A` for some `t ∉ m`; and then
  `t * s ∈ I` with `t * s ∉ m`.  Contradiction, so `I = ⊤` and `z ∈ A`.

`[IsNoetherianRing A]` is used only to know a non-zero-divisor avoids every minimal prime; a
prover may find it removable, and if so should say so rather than keep it.

## FAITHFULNESS

`hdom` may NOT be dropped, and is not implied by `hic`: over `A = k[x,y]/(xy)` — reduced,
noetherian, one-dimensional — the localization at the origin is not a domain, and `A` is not
integrally closed in its total quotient ring (`(1,0)`, the idempotent of the normalization
`k[x] × k[y]`, is integral over `A` and not in it).  So a version with `hic` alone is FALSE.

`hic` may not be dropped either, for the ordinary reason: `A = k[x²,x³]` is a noetherian
domain, every localization is a domain, and `A` is not integrally closed.

**WHERE THIS BELONGS.**  `Fermat/FLT/Mathlib/RingTheory/LocalProperties/`, beside mathlib's
`IntegrallyClosed.lean` which it is the missing non-domain case of.  It is stated here because
this module is its only consumer and because moving it would rebuild a cone for one theorem;
a second consumer is the reason to hoist it. -/
theorem isIntegrallyClosed_of_forall_localizationAtPrime (A : Type) [CommRing A]
    [IsNoetherianRing A]
    (_hdom : ∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P))
    (_hic : ∀ (P : Ideal A) [P.IsPrime], IsIntegrallyClosed (Localization.AtPrime P)) :
    IsIntegrallyClosed A :=
  sorry

/-! ### The localizations of the invariant ring are integrally closed -/

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **THE LOCALIZATIONS OF THE INVARIANT RING AT PRIMES ARE INTEGRALLY CLOSED**
(PROVEN 2026-08-02 over `isIntegrallyClosed_of_forall_localizationAtPrime` alone) —
Deligne–Rapoport III.1, Katz–Mazur 8.2.1, in the ring-theoretic form: *the quotient of a
smooth affine curve by a finite group is normal.*

The route runs over `S ⊗[R] R_p`, which mathlib recognises OUTRIGHT (by `inferInstance`) as
the localization of `S` at the image of `R ∖ p`, so its localizations at primes are
localizations of `S` at primes and are therefore regular local — normal domains — by
`RegularLocalNormal.lean`.

**The localization of the invariant setup costs NOTHING**, and that is the finding that made
this cheap: `Fermat.InvariantBaseChange.isInvariant_tensor` is stated for a base `k`, a
sub-`k`-algebra `B ⊆ A` and any FLAT `k`-algebra `K`, so instantiating it at `k = B = R` and
`K = R_p` — a flat `R`-algebra — gives `Algebra.IsInvariant (R ⊗[R] R_p) (S ⊗[R] R_p) G`
together with the action and the `SMulCommClass`, and `injective_bcInclusion` gives the
injectivity.  No group action on a localization has to be constructed by hand.  The
identification `R ⊗[R] R_p ≅ R_p` is `Algebra.TensorProduct.lid`, and `IsIntegrallyClosed`
transports along it by `IsIntegrallyClosed.of_equiv`.

`IsDomain (R ⊗[R] R_p)` — the hypothesis of `isIntegrallyClosed_of_isInvariant` that used to
be the obstruction — is `isDomain_localizationAtPrime_of_isInvariant` above, transported.

**`hdim` IS NOT NEEDED HERE and has been dropped**: normality of invariants holds in every
dimension.  It is REGULARITY that fails in dimension `≥ 2` (`k[x,y]^{±1}`, the quadric cone),
and that is why the parent below still takes it.

`set_option backward.isDefEq.respectTransparency false` is required: without it the `IsDomain`
produced for `Localization.AtPrime P` sits at `OreLocalization.instSemiring` while the goal
sits at `CommRing.toCommSemiring.toSemiring`, and the two cannot be identified because
`OreLocalization.instAdd` is not `@[expose]`d by the module system. -/
theorem isIntegrallyClosed_localizationAtPrime_of_isInvariant_of_smooth (K R S : Type)
    [Field K] [CommRing R] [CommRing S] [Algebra K R] [Algebra R S] [Algebra K S]
    [IsScalarTower K R S] (G : Type) [Group G] [Finite G] [MulSemiringAction G S]
    [SMulCommClass G R S] [Algebra.IsInvariant R S G] [Algebra.Smooth K S]
    (hinj : Function.Injective (algebraMap R S))
    (p : Ideal R) [p.IsPrime] :
    IsIntegrallyClosed (Localization.AtPrime p) := by
  classical
  haveI : Algebra.IsIntegral R S := Algebra.IsInvariant.isIntegral R S G
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing K S
  haveI hSred : IsReduced S := Algebra.Smooth.isReduced_of_isField (Field.toIsField K)
  -- localizations of `S` at primes are normal domains
  have hSdom : ∀ (Q : Ideal S) [Q.IsPrime], IsDomain (Localization.AtPrime Q) := by
    intro Q _
    haveI : IsRegularLocalRing (Localization.AtPrime Q) :=
      Algebra.Smooth.isRegularLocalRing_of_isLocalizationAtPrime K Q _
    exact GaloisRepresentation.Modularity.isDomain_of_isRegularLocalRing _
  -- `R_p` is a domain
  haveI hRpdom : IsDomain (Localization.AtPrime p) :=
    isDomain_localizationAtPrime_of_isInvariant G hinj hSdom p
  -- the base-changed invariant setup, along the FLAT extension `R → R_p`
  letI := Fermat.InvariantBaseChange.bcAction (k := R) (A := S) (Localization.AtPrime p) G
  letI := Fermat.InvariantBaseChange.bcAlgebra (k := R) (B := R) (A := S) (Localization.AtPrime p)
  haveI := Fermat.InvariantBaseChange.isInvariant_tensor (B := R) (A := S) R
    (Localization.AtPrime p) G
  haveI := Fermat.InvariantBaseChange.smulCommClass_tensor (B := R) (A := S) R
    (Localization.AtPrime p) G
  have hinj' : Function.Injective (algebraMap (R ⊗[R] Localization.AtPrime p)
      (S ⊗[R] Localization.AtPrime p)) :=
    Fermat.InvariantBaseChange.injective_bcInclusion R (Localization.AtPrime p) hinj
  -- `S ⊗[R] R_p` is the localization of `S` at the image of `R ∖ p`
  haveI hloc : IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl)
      (S ⊗[R] Localization.AtPrime p) := inferInstance
  haveI : IsNoetherianRing (S ⊗[R] Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing (Algebra.algebraMapSubmonoid S p.primeCompl) _ inferInstance
  haveI : IsReduced (S ⊗[R] Localization.AtPrime p) :=
    isReduced_localizationPreserves (Algebra.algebraMapSubmonoid S p.primeCompl) _ inferInstance
  -- its localizations at primes are localizations of `S` at primes, hence normal domains
  have hBdom : ∀ (P : Ideal (S ⊗[R] Localization.AtPrime p)) [P.IsPrime],
      IsDomain (Localization.AtPrime P) := by
    intro P hP
    haveI : (P.comap (algebraMap S (S ⊗[R] Localization.AtPrime p))).IsPrime := hP.comap _
    haveI := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid S p.primeCompl) (Localization.AtPrime P) P
    haveI : IsRegularLocalRing (Localization.AtPrime P) :=
      Algebra.Smooth.isRegularLocalRing_of_isLocalizationAtPrime K
        (P.comap (algebraMap S (S ⊗[R] Localization.AtPrime p))) _
    exact GaloisRepresentation.Modularity.isDomain_of_isRegularLocalRing
      (Localization.AtPrime P)
  have hBic : ∀ (P : Ideal (S ⊗[R] Localization.AtPrime p)) [P.IsPrime],
      IsIntegrallyClosed (Localization.AtPrime P) := by
    intro P hP
    haveI : (P.comap (algebraMap S (S ⊗[R] Localization.AtPrime p))).IsPrime := hP.comap _
    haveI := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid S p.primeCompl) (Localization.AtPrime P) P
    exact Algebra.Smooth.isIntegrallyClosed_of_isLocalizationAtPrime K
      (P.comap (algebraMap S (S ⊗[R] Localization.AtPrime p))) _
  haveI : IsIntegrallyClosed (S ⊗[R] Localization.AtPrime p) :=
    isIntegrallyClosed_of_forall_localizationAtPrime _ hBdom hBic
  -- `R ⊗[R] R_p ≅ R_p`, so it is a domain, and normality transports back
  have hlid : Function.Injective
      (Algebra.TensorProduct.lid R (Localization.AtPrime p)).toRingEquiv.toRingHom :=
    (Algebra.TensorProduct.lid R (Localization.AtPrime p)).toRingEquiv.injective
  haveI : IsDomain (R ⊗[R] Localization.AtPrime p) := Function.Injective.isDomain _ hlid
  haveI := Algebra.IsInvariant.isIntegrallyClosed_of_isInvariant
    (R ⊗[R] Localization.AtPrime p) (S ⊗[R] Localization.AtPrime p) G hinj'
    (Algebra.IsInvariant.nonZeroDivisors_le_comap_of_isInvariant _ _ G hinj')
  exact IsIntegrallyClosed.of_equiv
    (Algebra.TensorProduct.lid R (Localization.AtPrime p)).toRingEquiv

/-! ### The theorem the base change consumes -/

/-- **The invariants of a finite group acting on a SMOOTH algebra of Krull dimension one
over a field form a REGULAR ring** (PROVEN 2026-08-02 over the single leaf
`isIntegrallyClosed_localizationAtPrime_of_isInvariant_of_smooth` above) —
Deligne–Rapoport III.1, Katz–Mazur 8.2.1, in the ring-theoretic form; classically, "the
quotient of a smooth affine curve by a finite group is again a smooth affine curve" in the
normal-and-one-dimensional formulation.

This is what is left of `X1.lean`'s `isRegularRing_tensorAlgebraicClosure_of_isInvariant` once
the base change is paid for; see that file for the modular consumer and this module's header
for what the base change costs (nothing).

## THE PROOF, AND WHAT THE OLD DOCSTRING GOT WRONG

The old route was *normal + noetherian + dimension one ⇒ Dedekind ⇒ regular*, blocked because
`IsDomain R` is FALSE in the intended application (`S` splits into `φ(n)` components over a
field containing `ζ_n`), and every relevant mathlib and in-tree lemma carried `[IsDomain R]`.
Its prescribed repair was the `G`-equivariant PRODUCT DECOMPOSITION of `S`, priced at a
structure theory of reduced normal noetherian rings that the pin does not have.

**No product decomposition is needed, because `IsRegularRing` is a LOCAL condition and
`R_p` IS a domain for every prime `p`** — see `isDomain_localizationAtPrime_of_isInvariant`,
whose proof is prime avoidance over one `G`-orbit plus a norm.  Given that, each `R_p` is a
noetherian local domain of Krull dimension `≤ 1` (from
`ringKrullDim_eq_of_isIntegral_of_injective`, no domain hypothesis anywhere), so it is a
DEDEKIND DOMAIN as soon as it is integrally closed, and mathlib's
`[IsDedekindDomain R] : IsRegularRing R` finishes.

So `IsDomain` — which the previous docstring called "the whole difficulty" — is gone, and the
one surviving obligation is NORMALITY of the `R_p`.

`IsNoetherianRing R` is not an extra input: Noether's theorem on invariants
(`Algebra.IsInvariant.finiteType_of_isInvariant`) plus the Hilbert basis theorem.

## FAITHFULNESS (inherited, and re-checked against the new proof)

`hdim` is load-bearing and is where NONDEGENERACY enters: it is consumed as
`Ring.KrullDimLE 1 (Localization.AtPrime p)` and is what makes the Dedekind step available.
Regularity is FALSE for invariants in dimension `≥ 2` — `k[x,y]^{±1}`, the quadric cone
`k[u,v,w]/(uv − w²)`, is normal and not regular — so no proof can avoid using it.

`hinj` is what makes `R` a subring of `S` rather than merely an algebra over it; without it
take `R := k[x]/(x²) → S := k` with `G` trivial, where `R` is `S^G` in the sense of
`Algebra.IsInvariant` and `R` is not reduced, let alone regular.

`[Finite G]` is consumed by `Algebra.IsInvariant.isIntegral`, by Noether's theorem, and by the
norm inside the domain half.

The statement is NOT vacuous: `S := k[x]`, `G := ℤ/2` acting by `x ↦ -x`, `R = k[x²]` is an
inhabitant with `R` regular, and so is any `S` split into several components with `G`
permuting them. -/
theorem isRegularRing_of_isInvariant_of_smooth (K R S : Type)
    [Field K] [CommRing R] [CommRing S] [Algebra K R] [Algebra R S] [Algebra K S]
    [IsScalarTower K R S] (G : Type) [Group G] [Finite G] [MulSemiringAction G S]
    [SMulCommClass G R S] [Algebra.IsInvariant R S G] [Algebra.Smooth K S]
    (hinj : Function.Injective (algebraMap R S))
    (hdim : ringKrullDim S = (1 : ℕ)) :
    IsRegularRing R := by
  haveI : Algebra.IsIntegral R S := Algebra.IsInvariant.isIntegral R S G
  haveI : Algebra.FiniteType K R := Algebra.IsInvariant.finiteType_of_isInvariant K R S G hinj
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing K R
  have hSdom : ∀ (P : Ideal S) [P.IsPrime], IsDomain (Localization.AtPrime P) := by
    intro P hP
    haveI : IsRegularLocalRing (Localization.AtPrime P) :=
      Algebra.Smooth.isRegularLocalRing_of_isLocalizationAtPrime K P _
    exact GaloisRepresentation.Modularity.isDomain_of_isRegularLocalRing _
  have hdimR : ringKrullDim R = (1 : ℕ) :=
    (ringKrullDim_eq_of_isIntegral_of_injective R S hinj).symm.trans hdim
  rw [isRegularRing_iff]
  intro p hp
  haveI := hp
  haveI : IsDomain (Localization.AtPrime p) :=
    isDomain_localizationAtPrime_of_isInvariant G hinj hSdom p
  haveI hnoethp : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
  haveI hicp : IsIntegrallyClosed (Localization.AtPrime p) :=
    isIntegrallyClosed_localizationAtPrime_of_isInvariant_of_smooth K R S G hinj p
  haveI : Ring.KrullDimLE 1 (Localization.AtPrime p) := by
    refine Ring.krullDimLE_iff.mpr ?_
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)]
    refine le_trans (Ideal.height_le_ringKrullDim_of_ne_top hp.ne_top) ?_
    rw [hdimR]
  haveI hd1 : Ring.DimensionLEOne (Localization.AtPrime p) :=
    ⟨fun h1 h2 => Ring.krullDimLE_one_iff_of_noZeroDivisors.mp inferInstance _ h1 h2⟩
  haveI : IsDedekindRing (Localization.AtPrime p) := { hnoethp, hd1, hicp with }
  haveI : IsDedekindDomain (Localization.AtPrime p) := { }
  exact IsRegularLocalRing.of_isRegularRing_of_isLocalRing _

/-! ### The base change, which is free -/

section BaseChange

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (k K R S : Type) [Field k] [Field K] [Algebra k K] [Algebra.IsIntegral k K]
  [CommRing R] [CommRing S] [Algebra k R] [Algebra R S] [Algebra k S] [IsScalarTower k R S]
  (G : Type) [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]

omit [Algebra.IsIntegral k K] in
/-- `S` embeds in `S ⊗[k] K`, because `S` is flat over the field `k`. -/
theorem injective_algebraMap_tensorRight :
    Function.Injective (algebraMap S (S ⊗[k] K)) :=
  Algebra.TensorProduct.includeLeft_injective (S := k) (algebraMap k K).injective

/-- **The Krull dimension is unchanged by an ALGEBRAIC base field extension** — because the
extension is then integral, so no dimension theory of finite-type algebras is needed. -/
theorem ringKrullDim_tensorRight :
    ringKrullDim (S ⊗[k] K) = ringKrullDim S :=
  ringKrullDim_eq_of_isIntegral_of_injective S (S ⊗[k] K)
    (injective_algebraMap_tensorRight k K S)

omit [Algebra.IsIntegral k K] in
/-- The scalar tower `K → R ⊗[k] K → S ⊗[k] K`, for the right-hand algebra structures and
the base-changed inclusion. -/
theorem isScalarTower_tensorRight :
    letI := Fermat.InvariantBaseChange.bcAlgebra (B := R) (A := S) k K
    IsScalarTower K (R ⊗[k] K) (S ⊗[k] K) := by
  letI := Fermat.InvariantBaseChange.bcAlgebra (B := R) (A := S) k K
  refine IsScalarTower.of_algebraMap_eq fun κ => ?_
  show (1 : S) ⊗ₜ[k] κ = Fermat.InvariantBaseChange.bcInclusion k K ((1 : R) ⊗ₜ[k] κ)
  rw [Fermat.InvariantBaseChange.bcInclusion_tmul, map_one]

omit [Algebra.IsIntegral k K] in
/-- `S ⊗[k] K` is smooth over `K` — mathlib's `Algebra.Smooth.baseChange` states this for
`K ⊗[k] S`, and `Algebra.TensorProduct.commRight` is the `K`-algebra equivalence between
the two orientations. -/
theorem smooth_tensorRight [Algebra.Smooth k S] : Algebra.Smooth K (S ⊗[k] K) :=
  Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k K S)

/-- **THE BASE-CHANGED INVARIANT RING OF A SMOOTH CURVE ALGEBRA IS REGULAR**, for any
ALGEBRAIC extension `K/k` — proven over the single leaf
`isRegularRing_of_isInvariant_of_smooth`, which mentions no tensor product.

The `K`-algebra structure on `K ⊗[k] R` in the conclusion is mathlib's standard one, so a
consumer never has to know that the proof runs on the other orientation. -/
theorem isRegularRing_tensorProduct_of_isInvariant
    [Algebra.IsInvariant R S G] [Algebra.Smooth k S]
    (hinj : Function.Injective (algebraMap R S))
    (hdim : ringKrullDim S = (1 : ℕ)) :
    IsRegularRing (K ⊗[k] R) := by
  classical
  haveI : SMulCommClass G k S :=
    Fermat.InvariantBaseChange.smulCommClass_of_isScalarTower k R S G
  letI := Fermat.InvariantBaseChange.bcAction (A := S) k K G
  letI := Fermat.InvariantBaseChange.bcAlgebra (B := R) (A := S) k K
  haveI := Fermat.InvariantBaseChange.isInvariant_tensor (B := R) (A := S) k K G
  haveI := Fermat.InvariantBaseChange.smulCommClass_tensor (B := R) (A := S) k K G
  haveI := isScalarTower_tensorRight k K R S
  haveI := smooth_tensorRight k K S
  have hinj' : Function.Injective (algebraMap (R ⊗[k] K) (S ⊗[k] K)) :=
    Fermat.InvariantBaseChange.injective_bcInclusion k K hinj
  have hdim' : ringKrullDim (S ⊗[k] K) = (1 : ℕ) := by
    rw [ringKrullDim_tensorRight k K S, hdim]
  haveI := isRegularRing_of_isInvariant_of_smooth K (R ⊗[k] K) (S ⊗[k] K) G hinj' hdim'
  exact IsRegularRing.of_ringEquiv (Algebra.TensorProduct.comm k R K).toRingEquiv

end BaseChange

end Fermat.InvariantTensorRegular

end
