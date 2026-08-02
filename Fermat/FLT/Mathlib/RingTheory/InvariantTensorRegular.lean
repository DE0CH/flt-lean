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
used to be the leaf — is now **PROVEN**.  What is left is ONE leaf,
`isIntegrallyClosed_localizationAtPrime_of_isInvariant_of_smooth`, which contains no tensor
product, no base change and no regularity: *every localization of `S^G` at a prime is
integrally closed in its total quotient ring.*  See its docstring for the route and for what
was stale in the previous audit.

The two halves the old leaf bundled have separated:

* **`IsDomain`** — which that leaf's docstring called *"the whole difficulty"* and proposed
  to settle by a `G`-equivariant product decomposition of `S` — is PROVEN here as
  `isDomain_localizationAtPrime_of_isInvariant`, with no decomposition: `IsRegularRing` is a
  LOCAL condition, and `ker (R → R_p) = ker (S → S_P) ∩ R` for any prime `P` of `S` over `p`,
  by prime avoidance over one `G`-orbit plus a norm.  Every localization of `S` at a prime is
  a domain because it is regular local
  (`Algebra.Smooth.isRegularLocalRing_of_isLocalizationAtPrime`, `RegularLocalNormal.lean`).
* **NORMALITY** is the residue.
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

/-! ### The residual leaf -/

/-- **THE LOCALIZATIONS OF THE INVARIANT RING AT PRIMES ARE INTEGRALLY CLOSED** (sorry leaf)
— Deligne–Rapoport III.1, Katz–Mazur 8.2.1, in the ring-theoretic form: *the quotient of a
smooth affine curve by a finite group is normal.*

This is ALL that is left of `isRegularRing_of_isInvariant_of_smooth`, which is now PROVEN
over it (see below), and it is a NORMALITY statement — the `IsDomain` obstruction that
theorem's docstring called "the whole difficulty" is discharged by
`isDomain_localizationAtPrime_of_isInvariant` above.

## WHAT WAS STALE IN THE OLD AUDIT, AND WHY THE PRICE HAS MOVED

The 2026-07-31 "WHAT IS MISSING FROM THE PIN" list on the parent had three bullets.  Its
FIRST bullet — *"smooth over a field ⇒ regular, or ⇒ integrally closed … is EMPTY"* — was
measured against `Mathlib/RingTheory/Smooth/` and `Mathlib/RingTheory/Etale/` only, and it is
false about THIS TREE.  `Fermat/FLT/Mathlib/RingTheory/RegularLocalNormal.lean` carries, all
PROVEN as of 2026-07-31:

* `Algebra.Smooth.isRegularLocalRing_of_isLocalizationAtPrime` — a localization at a prime of
  a smooth algebra over a field is regular local;
* `Algebra.Smooth.isIntegrallyClosed_of_isLocalizationAtPrime` — and is integrally closed;
* `GaloisRepresentation.Modularity.isDomain_of_isRegularLocalRing` (in `RegularStalks.lean`)
  — a regular local ring is a domain.

So `S` is regular, and every `S_P` is a normal DOMAIN.  That is what makes the domain half
above go through, and it is why the residue is normality and nothing else.

The THIRD bullet — no structure theory of reduced normal noetherian rings — stands, and it is
what this leaf still owes.  The SECOND bullet — normality does not localise without a domain
— stands as a statement about mathlib and is now only needed in the ASCENT direction (see the
route).

## THE ROUTE, AND THE TWO NAMED PIECES IT NEEDS

Both are stated over `S_p := (R ∖ p)⁻¹ S`, the localization of `S` at the image of `R ∖ p` —
a `G`-STABLE submonoid, because `G` fixes the image of `R` pointwise
(`smul_algebraMap_of_smulCommClass`).

1. **LOCALIZATION OF THE INVARIANT SETUP** (formal, not a citation).  `G` acts on `S_p` by
   `g • (s/w) = (g • s)/w` — well defined because `w ∈ R` is `G`-fixed — and
   `Algebra.IsInvariant R_p S_p G` holds: given `s/w` fixed by `G`, each `g` supplies
   `w_g ∈ R ∖ p` with `w_g • (g • s − s) = 0`; the product `w'` of the `w_g` is again in
   `R ∖ p`, is `G`-fixed, and `w' * s` is then `G`-fixed, hence lies in the image of `R` by
   `Algebra.IsInvariant R S G`; and `s/w = (w' s)/(w' w)`.  `R_p → S_p` is injective by the
   same computation as `hinj`.
2. **`IsIntegrallyClosed S_p`** — i.e. *a noetherian ring all of whose localizations at primes
   are integrally closed domains is integrally closed in its total quotient ring.*  Its
   localizations at primes are the `S_Q` for `Q ⊆ some prime over p`, and those ARE normal
   domains by `Algebra.Smooth.isIntegrallyClosed_of_isLocalizationAtPrime`.  This is the one
   genuinely missing piece of general commutative algebra; mathlib's
   `IsIntegrallyClosed.of_localization_maximal` and every neighbour in
   `Mathlib/RingTheory/LocalProperties/IntegrallyClosed.lean` carries `[IsDomain R]`.

   Its proof is the conductor argument and does NOT need the product decomposition: for
   `z ∈ Q(A)` integral over `A`, the ideal `I = {a | a z ∈ A}` is not contained in any maximal
   `m`, because `nonZeroDivisors A` maps into `nonZeroDivisors A_m` (`A_m` being a domain
   whose zero ideal pulls back into every prime below `m`), so `z` maps into `Frac(A_m) = A_m`
   and clears a denominator outside `m`.

   With those two, the leaf is `isIntegrallyClosed_of_isInvariant` (`InvariantCoarseRing.lean`)
   applied to `(R_p, S_p, G)`: its `[IsDomain R]` hypothesis is `isDomain_localizationAtPrime_of_isInvariant`
   above, and its `hnzd` is `nonZeroDivisors_le_comap_of_isInvariant` (`S_p` is reduced).

## FAITHFULNESS

`hdim` is retained although the descent above never reads it: regularity of invariants is
FALSE in dimension `≥ 2` (`k[x,y]^{±1}`, the quadric cone `k[u,v,w]/(uv − w²)`, is normal and
not regular), so the PARENT needs it, and normality at the primes of a two-dimensional
invariant ring is still true — this leaf alone would survive without it.  It is kept because
the caller has it for free and because a hypothesis cannot make the leaf false.

`hinj` is genuinely load-bearing for the ROUTE (`isIntegrallyClosed_of_isInvariant` takes it)
and for the parent.

`[Finite G]` is consumed by `Algebra.IsInvariant.isIntegral` and by the norm.

The statement is NOT vacuous and NOT automatic: `Localization.AtPrime p` is a genuine
normality assertion — `k[x²,x³]` localized at `(x², x³)` is a noetherian local domain of
dimension one that is NOT integrally closed — so the content is that no such ring occurs as a
localization of `S^G`. -/
theorem isIntegrallyClosed_localizationAtPrime_of_isInvariant_of_smooth (K R S : Type)
    [Field K] [CommRing R] [CommRing S] [Algebra K R] [Algebra R S] [Algebra K S]
    [IsScalarTower K R S] (G : Type) [Group G] [Finite G] [MulSemiringAction G S]
    [SMulCommClass G R S] [Algebra.IsInvariant R S G] [Algebra.Smooth K S]
    (_hinj : Function.Injective (algebraMap R S))
    (_hdim : ringKrullDim S = (1 : ℕ))
    (p : Ideal R) [p.IsPrime] :
    IsIntegrallyClosed (Localization.AtPrime p) :=
  sorry

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
    isIntegrallyClosed_localizationAtPrime_of_isInvariant_of_smooth K R S G hinj hdim p
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
