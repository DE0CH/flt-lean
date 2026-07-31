/-
Fermat/FLT/Mathlib/RingTheory/RegularLocalNormal.lean — own work for the
Fermat project (not vendored from the FLT project).

# Regular local rings are integrally closed, and so are the stalks of a smooth scheme

This module supplies the NORMALITY half of the regular-local-ring theory, on top of
`Fermat/FLT/Modularity/RegularStalks.lean`, which already carries the regularity half:

* `isRegularLocalRing_stalk_of_smooth_over_field` — a stalk of a smooth `K`-scheme is
  regular local (PROVEN there, 2026-07-26);
* `isDomain_of_isRegularLocalRing` — a regular local ring is a domain (PROVEN there,
  2026-07-26, closing mathlib's own recorded TODO).

What was still missing, and is supplied here, is `IsIntegrallyClosed`.

## Main results

* `IsIntegrallyClosed.of_isPrincipal_maximalIdeal` — a Noetherian local domain whose maximal
  ideal is principal is integrally closed (it is a field or a DVR).
* `IsIntegrallyClosed.of_span_singleton_isPrime` — **the conductor argument**, and the
  mathematical core of this file.  If `x ≠ 0` generates a PRIME ideal of a domain `R`, and
  `R` localised at `(x)` and at every prime NOT containing `x` is integrally closed, then so
  is `R`.  No noetherian hypothesis, no locality, no dimension theory.
* `IsIntegrallyClosed.of_isRegularRing_of_isLocalRing` — **a local ring all of whose
  localizations at primes are regular local is integrally closed.**  This is the file's
  general commutative-algebra statement; see the WALL section below for why it is stated
  over `IsRegularRing` rather than over `IsRegularLocalRing` alone.
* `Algebra.Smooth.isIntegrallyClosed_of_isLocalizationAtPrime` — a localization at a prime
  of a smooth algebra over a field is integrally closed.
* `AlgebraicGeometry.isIntegrallyClosed_stalk_of_smooth_over_field` — **the stalks of a
  scheme smooth over a field are integrally closed.**
* `Fermat.AbelianSchemeStruct.isIntegrallyClosed_stalk` — the same for an abelian scheme
  over a field, which is the shape `Fermat/FLT/Modularity/TateModule.lean` holds.

## Why this file exists

`exists_pow_eq_stalkMap_mulByNat_prime` (the Verschiebung leaf, `TateModule.lean`) reduces —
along its cheapest audited route — to a statement about the FUNCTION FIELD, and the reduction
needs exactly this: `A'` is integral, so every stalk `𝒪_{A',x}` injects into `k(A')`; a
`p`-th root in `k(A')` of `b ∈ 𝒪_{A',x}` is a root of `T ^ p - b`, hence INTEGRAL over
`𝒪_{A',x}`, hence lies in `𝒪_{A',x}` as soon as that ring is integrally closed.  With
`isIntegrallyClosed_stalk_of_smooth_over_field` the leaf's `∀ x : A'` collapses to a single
statement about a single field.  **That leaf is NOT touched here** — its other half, the
field-level criterion `{x ∈ K : d x = 0} = K ^ p`, is separate missing library.

## THE WALL, stated precisely: `IsRegularLocalRing R → IsIntegrallyClosed R` alone is NOT
## reachable at this pin, and the reason is one named mathlib TODO

The theorem below is stated for a ring that is local AND all of whose localizations at primes
are regular local (`IsRegularRing` + `IsLocalRing`), not for a bare `IsRegularLocalRing`.
That is not a stylistic choice; it is where the pin stops.

The proof is an induction on the embedding dimension, and its inductive step localizes: it
needs `R_p` to be regular local for `p` a prime strictly below `𝔪`.  For a bare
`IsRegularLocalRing R` that is the statement

    `IsRegularLocalRing R → IsRegularRing R`,

which is **mathlib's own recorded TODO**, verbatim in
`Mathlib/RingTheory/RegularLocalRing/Defs.lean`:

    ## TODO
    Show that regular local rings are regular under this definition.
    This follows from localizations of regular local rings being regular (@Thmoas-Guan).

It is not a bookkeeping gap.  Localizations of a regular local ring are regular because
regularity is equivalent to FINITE GLOBAL DIMENSION (Serre), and that equivalence is the
same homological input Auslander–Buchsbaum needs; mathlib has neither.  A sweep of the pin on
2026-07-31 confirms the surrounding absences are all still real:

* `Mathlib/RingTheory/RegularLocalRing/` is still exactly `Defs.lean` and `Polynomial.lean`,
  and neither connects `IsRegularLocalRing` to `IsIntegrallyClosed`, to
  `UniqueFactorizationMonoid`, or to `IsRegularRing`;
* `grep -rl 'KrullDomain' Mathlib/` is EMPTY — no Krull domains;
* `grep -rl 'CohenMacaulay' Mathlib/` is EMPTY — no depth theory, hence **no Serre's
  criterion `R1 + S2`**;
* there is no Auslander–Buchsbaum and no Cohen structure theorem.

So the three classical routes to normality of a regular local ring — Auslander–Buchsbaum
(regular ⟹ UFD ⟹ normal), Serre's criterion, and Krull domains — are ALL blocked at the
same pin, each by a different missing theory.

**No consumer is blocked by this.**  What a consumer here actually holds is a stalk of a
SMOOTH scheme, and smoothness supplies the full `IsRegularRing` hypothesis directly: every
localization at a prime of a smooth algebra over a field is again a localization at a prime
of that same algebra, hence regular local by `isRegularLocalRing_stalk_of_smooth_over_field`
applied at another point of the same `Spec`.  That is
`Algebra.Smooth.isRegularRing_localizationAtPrime` below, and it is why the geometric
corollaries in this file are unconditional.

Anyone closing the residual gap should close `IsRegularLocalRing R → IsRegularRing R` in
mathlib's own terms — it is one theorem that makes `IsIntegrallyClosed.of_isRegularRing`
below immediately give `IsRegularLocalRing.isIntegrallyClosed` with no further work here.

## THE PROOF, and why it is cheap

The core is `IsIntegrallyClosed.of_span_singleton_isPrime`, which is the classical
identity `R = R[1/x] ∩ R_{(x)}` rewritten so that no localization ever has to be built.
Let `z` lie in the fraction field and be integral over `R`, and let

    `J = {r ∈ R | r z ∈ R}`

be its CONDUCTOR (`denomIdeal` below), a nonzero ideal.  Then:

1. for every prime `p` with `x ∉ p`, integral closedness of `R_p` puts `z` in `R_p`, i.e.
   gives an `s ∈ J ∖ p` — so `J ⊄ p`.  Hence **every** prime containing `J` contains `x`,
   i.e. `x ∈ √J`, i.e. `x ^ k ∈ J` for some `k`;
2. take `k` LEAST with `a := x ^ k z ∈ R`.  If `k ≥ 1` then `a ∉ (x)`, by minimality;
3. integral closedness of `R_{(x)}` gives `s ∉ (x)` with `c := s z ∈ R`, whence
   `s a = x ^ k c`, so `x ∣ s a`; as `(x)` is prime and `s ∉ (x)`, `x ∣ a` — contradiction.
   So `k = 0` and `z ∈ R`.

Step 1 is the only place localizations appear, and it is used only to produce ONE
denominator; that is why the statement needs neither noetherianity nor a dimension.

In the induction, `x` is a regular parameter (`x ∈ 𝔪 ∖ 𝔪²`), `(x)` is prime because
`R ⧸ (x)` is again regular local (`isRegularLocalRing_quotient_span_singleton`) hence a
domain (`isDomain_of_isRegularLocalRing`), `R_{(x)}` has a PRINCIPAL maximal ideal so it is a
field or a DVR outright, and the remaining `R_p` are handled by the inductive hypothesis
because `p < 𝔪` forces `height p < height 𝔪` (`Ideal.height_add_one_le_of_lt_of_isPrime`),
which regularity identifies with the embedding dimension.

Note the induction never needs `ringKrullDim` to be finite as a separate hypothesis:
regularity gives `(maximalIdeal R).spanFinrank = ringKrullDim R` with a NATURAL number on the
left, so finiteness comes for free.
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Fermat.FLT.Modularity.AbelianScheme
public import Fermat.FLT.Modularity.RegularStalks

@[expose] public section

universe u

open IsLocalRing

/-! ### A Noetherian local domain with principal maximal ideal -/

/-- **A NOETHERIAN LOCAL DOMAIN WHOSE MAXIMAL IDEAL IS PRINCIPAL IS INTEGRALLY CLOSED**
(PROVEN 2026-07-31).

It is a field if `𝔪 = ⊥` and a DVR otherwise, and mathlib knows both cases: the DVR half is
`(IsDiscreteValuationRing.TFAE R hf).out 4 0`, whose item 4 is exactly "`𝔪` is principal",
and a DVR is a PID, hence a UFD, hence integrally closed by `instIsIntegrallyClosed`.

This is the base of the induction in `IsIntegrallyClosed.of_isRegularRing_of_isLocalRing`
below, and — more importantly — it is what discharges the localization at the regular
parameter there WITHOUT any appeal to regularity: `R_{(x)}` has maximal ideal generated by
the image of `x`, and that is all the argument uses. -/
theorem IsIntegrallyClosed.of_isPrincipal_maximalIdeal (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsLocalRing R] (h : (maximalIdeal R).IsPrincipal) :
    IsIntegrallyClosed R := by
  by_cases hf : IsField R
  · exact hf.toField.instIsIntegrallyClosed
  · haveI : IsDiscreteValuationRing R := ((IsDiscreteValuationRing.TFAE R hf).out 4 0).mp h
    infer_instance

/-! ### The conductor of an element of the fraction field -/

namespace RegularNormal

/-- **THE CONDUCTOR (denominator ideal) `{r ∈ R | r z ∈ R}`** of an element `z` of the
fraction field of a domain `R`.  It is nonzero for every `z`, and `z ∈ R` exactly when it is
all of `R`; the whole of `IsIntegrallyClosed.of_span_singleton_isPrime` is an argument about
this one ideal. -/
def denomIdeal (R : Type u) [CommRing R] [IsDomain R] (z : FractionRing R) : Ideal R where
  carrier := {r : R |
    ∃ a : R, algebraMap R (FractionRing R) r * z = algebraMap R (FractionRing R) a}
  add_mem' := by
    rintro r r' ⟨a, ha⟩ ⟨a', ha'⟩
    exact ⟨a + a', by rw [map_add, add_mul, ha, ha', map_add]⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c r ⟨a, ha⟩
    exact ⟨c * a, by rw [smul_eq_mul, map_mul, mul_assoc, ha, map_mul]⟩

@[simp]
theorem mem_denomIdeal {R : Type u} [CommRing R] [IsDomain R] {z : FractionRing R} {r : R} :
    r ∈ denomIdeal R z ↔
      ∃ a : R, algebraMap R (FractionRing R) r * z = algebraMap R (FractionRing R) a :=
  Iff.rfl

/-- **AN INTEGRALLY CLOSED LOCALIZATION PRODUCES A DENOMINATOR OUTSIDE ITS PRIME**
(PROVEN 2026-07-31).

If `R_p` is integrally closed and `z` is integral over `R`, then `z` is integral over `R_p`
(`IsIntegral.tower_top`), hence lies in `R_p` — and an element of `R_p ⊆ Frac R` is `a / s`
with `s ∉ p`, so `s` is a denominator for `z` lying outside `p`.

This is the ONLY point at which the conductor argument touches a localization, and it is
used twice: at the prime `(x)` and at an arbitrary prime avoiding `x`. -/
theorem exists_notMem_mem_denomIdeal (R : Type u) [CommRing R] [IsDomain R]
    (p : Ideal R) (hp : p.IsPrime)
    (hcl : IsIntegrallyClosed (Localization.AtPrime p))
    (z : FractionRing R) (hz : IsIntegral R z) :
    ∃ s : R, s ∉ p ∧ s ∈ denomIdeal R z := by
  haveI := hp
  haveI := hcl
  have hzA : IsIntegral (Localization.AtPrime p) z := hz.tower_top
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff (FractionRing R)).mp hcl hzA
  obtain ⟨⟨a, s⟩, hy'⟩ := IsLocalization.surj p.primeCompl y
  refine ⟨s, s.2, a, ?_⟩
  have := congrArg (algebraMap (Localization.AtPrime p) (FractionRing R)) hy'
  rw [map_mul, hy, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
  rw [mul_comm]
  exact this

end RegularNormal

/-- **THE CONDUCTOR ARGUMENT** (PROVEN 2026-07-31), and the mathematical core of this file:
`R = R[1/x] ∩ R_{(x)}` in a form that builds neither ring.

Let `R` be a domain and `x ≠ 0` an element generating a PRIME ideal.  If `R` localised at
`(x)` is integrally closed, and so is `R` localised at every prime NOT containing `x`, then
`R` is integrally closed.

**No noetherian hypothesis, no local hypothesis, no dimension theory.**  That is what makes
this reusable: the induction below supplies the two families of localizations from
regularity, but nothing in the statement mentions regularity.

THE PROOF is the four-step argument in this module's header docstring.  The one step worth
repeating is why `x ∈ √J` for the conductor `J`: a prime `p ⊇ J` with `x ∉ p` would, by
hypothesis, give a denominator of `z` outside `p` — i.e. an element of `J ∖ p`, contradicting
`J ⊆ p`.  So every prime over `J` contains `x`, which is `Ideal.radical_eq_sInf`.

The `k = 0` branch IS the conclusion (`z = x ^ 0 z ∈ R`); only `k ≥ 1` needs refuting, and
there minimality of `k` says `a = x ^ k z` is not divisible by `x`, while primeness of `(x)`
applied to `s a = x ^ k c` says it is. -/
theorem IsIntegrallyClosed.of_span_singleton_isPrime
    (R : Type u) [CommRing R] [IsDomain R] {x : R} (hx0 : x ≠ 0)
    (hxp : (Ideal.span {x}).IsPrime)
    (h1 : IsIntegrallyClosed (Localization.AtPrime (Ideal.span {x})))
    (h2 : ∀ (p : Ideal R) (_ : p.IsPrime), x ∉ p → IsIntegrallyClosed (Localization.AtPrime p)) :
    IsIntegrallyClosed R := by
  classical
  refine (isIntegrallyClosed_iff (FractionRing R)).mpr ?_
  intro z hz
  have hinj := IsFractionRing.injective R (FractionRing R)
  -- every prime containing the conductor contains `x`
  have hrad : x ∈ (RegularNormal.denomIdeal R z).radical := by
    rw [Ideal.radical_eq_sInf]
    refine Submodule.mem_sInf.mpr ?_
    rintro p ⟨hJp, hpp⟩
    by_contra hxp'
    obtain ⟨s, hs, hsJ⟩ :=
      RegularNormal.exists_notMem_mem_denomIdeal R p hpp (h2 p hpp hxp') z hz
    exact hs (hJp hsJ)
  have hex : ∃ n : ℕ, x ^ n ∈ RegularNormal.denomIdeal R z := hrad
  obtain ⟨a, ha⟩ := RegularNormal.mem_denomIdeal.mp (Nat.find_spec hex)
  rcases Nat.eq_zero_or_pos (Nat.find hex) with hk0 | hkpos
  · refine ⟨a, ?_⟩
    rw [hk0, pow_zero, map_one, one_mul] at ha
    exact ha.symm
  exfalso
  -- `a ∉ (x)`, by minimality of the exponent
  have hax : a ∉ Ideal.span ({x} : Set R) := by
    rintro hmem
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hmem
    refine Nat.find_min hex (Nat.sub_lt hkpos one_pos)
      (RegularNormal.mem_denomIdeal.mpr ⟨b, ?_⟩)
    have hxne : algebraMap R (FractionRing R) x ≠ 0 := by
      simpa using hinj.ne hx0
    have hkk : Nat.find hex - 1 + 1 = Nat.find hex := Nat.sub_add_cancel hkpos
    refine mul_left_cancel₀ hxne ?_
    rw [← mul_assoc, ← map_mul, ← pow_succ', hkk, ha, map_mul, mul_comm]
  -- but `z` has a denominator outside `(x)`
  obtain ⟨s, hs, c, hc⟩ := RegularNormal.exists_notMem_mem_denomIdeal R _ hxp h1 z hz
  have hkey : s * a = x ^ Nat.find hex * c := by
    refine hinj ?_
    rw [map_mul, map_mul, ← ha, ← hc]
    ring
  have hxa : x ∣ s * a := hkey ▸ Dvd.dvd.mul_right (dvd_pow_self x hkpos.ne') c
  rcases hxp.mem_or_mem (Ideal.mem_span_singleton.mpr hxa) with h | h
  · exact hs h
  · exact hax h

/-! ### Regular rings -/

/-- **A LOCALIZATION OF A REGULAR RING AT A PRIME IS A REGULAR RING** (PROVEN 2026-07-31).

The primes of `R_p` are the primes of `R` below `p`, and `(R_p)_q` is `R` localised at the
contraction of `q` — which is `IsLocalization.isLocalization_atPrime_localization_atPrime`,
already an INSTANCE in mathlib.  So the content is only the transport along
`IsLocalization.algEquiv`, plus noetherianity of the localization.

This is what lets the induction below re-establish its own hypothesis after localizing, and
it is the reason the induction is stated over `IsRegularRing` rather than being threaded
through a bespoke `∀ q, IsRegularLocalRing (Localization.AtPrime q)` side condition. -/
theorem IsRegularRing.localizationAtPrime {R : Type u} [CommRing R] [IsRegularRing R]
    (p : Ideal R) [p.IsPrime] : IsRegularRing (Localization.AtPrime p) := by
  haveI : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
  rw [isRegularRing_iff]
  intro q hq
  haveI := hq
  haveI : (q.comap (algebraMap R (Localization.AtPrime p))).IsPrime := hq.comap _
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (q.comap (algebraMap R (Localization.AtPrime p))).primeCompl
      (Localization.AtPrime (q.comap (algebraMap R (Localization.AtPrime p))))
      (Localization.AtPrime q)).toRingEquiv

/-- **THE INDUCTION** on the embedding dimension (PROVEN 2026-07-31).

As with `isDomain_of_isRegularLocalRing_aux` in `RegularStalks.lean`, the induction hypothesis
must quantify over the RING and not only over the dimension, because the inductive step passes
to `R_p` for a smaller prime `p`; hence the `∀ (R : Type u) [CommRing R] …` shape.

* `n = 0`: `spanFinrank 𝔪 = 0` forces `𝔪 = ⊥`, so `R` is a field.
* `n ≥ 1`: `𝔪 ⊄ 𝔪²` (else Nakayama gives `𝔪 = ⊥`), so a regular parameter `x` exists;
  `R ⧸ (x)` is regular local, hence a domain, so `(x)` is PRIME; `R_{(x)}` has principal
  maximal ideal, hence is integrally closed by
  `IsIntegrallyClosed.of_isPrincipal_maximalIdeal` — note this branch does NOT recurse; and
  for `p` prime with `x ∉ p` we have `p < 𝔪`, so
  `Ideal.height_add_one_le_of_lt_of_isPrime` plus
  `IsLocalization.AtPrime.ringKrullDim_eq_height` and
  `IsLocalRing.maximalIdeal_height_eq_ringKrullDim` — read through the regularity identity
  `spanFinrank 𝔪 = ringKrullDim` at BOTH ends — give a strictly smaller embedding dimension.
  `IsIntegrallyClosed.of_span_singleton_isPrime` assembles the two families. -/
theorem IsIntegrallyClosed.of_isRegularRing_aux (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsRegularRing R],
      (maximalIdeal R).spanFinrank = n → IsIntegrallyClosed R := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro R _ _ _ hn
    haveI : IsRegularLocalRing R := IsRegularLocalRing.of_isRegularRing_of_isLocalRing R
    haveI : IsDomain R := GaloisRepresentation.Modularity.isDomain_of_isRegularLocalRing R
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · have hbot : maximalIdeal R = ⊥ :=
        (Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).1 hn
      exact (IsLocalRing.isField_iff_maximalIdeal_eq.2 hbot).toField.instIsIntegrallyClosed
    -- a regular parameter exists, by Nakayama
    obtain ⟨x, hxm, hx2⟩ : ∃ x ∈ maximalIdeal R, x ∉ (maximalIdeal R) ^ 2 := by
      by_contra hcon
      push Not at hcon
      have hle : maximalIdeal R ≤ maximalIdeal R • maximalIdeal R := by
        intro y hy
        rw [Ideal.smul_eq_mul, ← pow_two]
        exact hcon y hy
      have hbot : maximalIdeal R = ⊥ :=
        Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) _
          (IsNoetherian.noetherian _) hle
          (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top])
      rw [hbot] at hn
      simp at hn
      omega
    have hx0 : x ≠ 0 := fun h => hx2 (h ▸ Submodule.zero_mem _)
    haveI : IsRegularLocalRing (R ⧸ Ideal.span {x}) :=
      GaloisRepresentation.Modularity.isRegularLocalRing_quotient_span_singleton hxm hx2
    have hxp : (Ideal.span ({x} : Set R)).IsPrime :=
      (Ideal.Quotient.isDomain_iff_prime _).mp
        (GaloisRepresentation.Modularity.isDomain_of_isRegularLocalRing _)
    haveI := hxp
    refine IsIntegrallyClosed.of_span_singleton_isPrime R hx0 hxp ?_ ?_
    · -- the localization at `(x)` has PRINCIPAL maximal ideal; no recursion here
      haveI : IsNoetherianRing (Localization.AtPrime (Ideal.span ({x} : Set R))) :=
        IsLocalization.isNoetherianRing (Ideal.span ({x} : Set R)).primeCompl _ inferInstance
      refine IsIntegrallyClosed.of_isPrincipal_maximalIdeal _ ⟨⟨
        algebraMap R (Localization.AtPrime (Ideal.span ({x} : Set R))) x, ?_⟩⟩
      rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]
    · -- the primes avoiding `x` are strictly lower, so the inductive hypothesis applies
      intro p hp hxnp
      haveI := hp
      haveI : IsRegularRing (Localization.AtPrime p) := IsRegularRing.localizationAtPrime p
      haveI : IsRegularLocalRing (Localization.AtPrime p) := inferInstance
      set m := (maximalIdeal (Localization.AtPrime p)).spanFinrank with hm
      have hplt : p < maximalIdeal R :=
        lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hp.ne_top) (fun h => hxnp (h ▸ hxm))
      have hheight : p.height + 1 ≤ (maximalIdeal R).height :=
        Ideal.height_add_one_le_of_lt_of_isPrime hplt
      have hmp : (m : WithBot ℕ∞) = (p.height : WithBot ℕ∞) := by
        rw [hm, IsRegularLocalRing.spanFinrank_maximalIdeal,
          IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)]
      have hnp : (n : WithBot ℕ∞) = ((maximalIdeal R).height : WithBot ℕ∞) := by
        rw [← hn, IsRegularLocalRing.spanFinrank_maximalIdeal,
          IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
      have hmh : (m : ℕ∞) = p.height := by exact_mod_cast hmp
      have hnh : (n : ℕ∞) = (maximalIdeal R).height := by exact_mod_cast hnp
      have hlt : m < n := by
        rw [← hmh, ← hnh] at hheight
        exact_mod_cast (by exact_mod_cast hheight : ((m + 1 : ℕ) : ℕ∞) ≤ ((n : ℕ) : ℕ∞))
      exact ih m hlt _ hm.symm

/-- **A LOCAL RING ALL OF WHOSE LOCALIZATIONS AT PRIMES ARE REGULAR LOCAL IS INTEGRALLY
CLOSED** (PROVEN 2026-07-31) — the general commutative-algebra statement of this file.

Read `IsRegularRing R` as exactly "`R` is noetherian and `R_p` is regular local for every
prime `p`"; together with `IsLocalRing R` it gives `IsRegularLocalRing R` for free
(`IsRegularLocalRing.of_isRegularRing_of_isLocalRing`).

**This is NOT `IsRegularLocalRing R → IsIntegrallyClosed R`**, and the gap between them is
one named mathlib TODO — see the WALL section of this module's header docstring.  Nothing in
this project's use is weakened by it, because smoothness supplies `IsRegularRing` outright. -/
theorem IsIntegrallyClosed.of_isRegularRing_of_isLocalRing (R : Type u) [CommRing R]
    [IsLocalRing R] [IsRegularRing R] : IsIntegrallyClosed R :=
  IsIntegrallyClosed.of_isRegularRing_aux _ R rfl

/-! ### Smooth algebras over a field -/

open CategoryTheory AlgebraicGeometry in
/-- **A LOCALIZATION AT A PRIME OF A SMOOTH ALGEBRA OVER A FIELD IS REGULAR LOCAL**
(PROVEN 2026-07-31) — the ring-level form of
`isRegularLocalRing_stalk_of_smooth_over_field`, obtained from it by taking the scheme to be
`Spec T` itself.

`Spec T ⟶ Spec K` is smooth by `HasRingHomProperty.Spec_iff` and
`RingHom.smooth_algebraMap`, the stalk of `Spec T` at `q` is `T` localised at `q`
(`StructureSheaf.IsLocalization.to_stalk`), and `IsLocalization.algEquiv` transports.

The statement takes the localization as a VARIABLE `S` rather than fixing
`Localization.AtPrime q`, for the reason recorded on
`exists_isRegularLocalRing_quotient_indepList_of_isStandardSmooth_of_isLocalization`: a
consumer holding a stalk should not have to make Lean unify a colimit in `CommRingCat`
against a concrete `Localization`. -/
theorem Algebra.Smooth.isRegularLocalRing_of_isLocalizationAtPrime
    (K : Type u) {T : Type u} [Field K] [CommRing T] [Algebra K T] [Algebra.Smooth K T]
    (q : Ideal T) [q.IsPrime] (S : Type u) [CommRing S] [Algebra T S]
    [IsLocalization.AtPrime S q] : IsRegularLocalRing S := by
  have hsm : AlgebraicGeometry.Smooth (Spec.map (CommRingCat.ofHom (algebraMap K T))) := by
    rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Smooth)]
    exact RingHom.smooth_algebraMap.mpr ‹_›
  have hqp : q.IsPrime := ‹_›
  set z : PrimeSpectrum T := ⟨q, hqp⟩ with hzdef
  have hreg : IsRegularLocalRing ↥((Spec (CommRingCat.of T)).presheaf.stalk z) :=
    GaloisRepresentation.Modularity.isRegularLocalRing_stalk_of_smooth_over_field
      (Spec.map (CommRingCat.ofHom (algebraMap K T))) hsm z
  letI : Algebra T ↥((Spec (CommRingCat.of T)).presheaf.stalk z) :=
    StructureSheaf.stalkAlgebra T z
  haveI : IsLocalization.AtPrime ↥((Spec (CommRingCat.of T)).presheaf.stalk z) q :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of T) z
  exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv q.primeCompl
    ↥((Spec (CommRingCat.of T)).presheaf.stalk z) S).toRingEquiv

/-- **A LOCALIZATION AT A PRIME OF A SMOOTH ALGEBRA OVER A FIELD IS A REGULAR RING**
(PROVEN 2026-07-31), not merely a regular LOCAL ring.

This is the step that makes the geometric corollaries of this file unconditional: it supplies
exactly the hypothesis that `IsIntegrallyClosed.of_isRegularRing_of_isLocalRing` needs and
that `IsRegularLocalRing` alone cannot give at this pin.  There is no circularity — the
primes of `T_q` are primes of `T`, so the previous theorem applies again at a DIFFERENT
prime of the SAME smooth algebra, never to a localization of a localization. -/
theorem Algebra.Smooth.isRegularRing_localizationAtPrime
    (K : Type u) {T : Type u} [Field K] [CommRing T] [Algebra K T] [Algebra.Smooth K T]
    (q : Ideal T) [q.IsPrime] : IsRegularRing (Localization.AtPrime q) := by
  haveI : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing K T
  haveI : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
  rw [isRegularRing_iff]
  intro P hP
  haveI := hP
  haveI : (P.comap (algebraMap T (Localization.AtPrime q))).IsPrime := hP.comap _
  exact Algebra.Smooth.isRegularLocalRing_of_isLocalizationAtPrime K
    (P.comap (algebraMap T (Localization.AtPrime q))) (Localization.AtPrime P)

/-- **A LOCALIZATION AT A PRIME OF A SMOOTH ALGEBRA OVER A FIELD IS INTEGRALLY CLOSED**
(PROVEN 2026-07-31) — the composite of the two previous theorems with
`IsIntegrallyClosed.of_isRegularRing_of_isLocalRing`. -/
theorem Algebra.Smooth.isIntegrallyClosed_of_isLocalizationAtPrime
    (K : Type u) {T : Type u} [Field K] [CommRing T] [Algebra K T] [Algebra.Smooth K T]
    (q : Ideal T) [q.IsPrime] (S : Type u) [CommRing S] [Algebra T S]
    [IsLocalization.AtPrime S q] : IsIntegrallyClosed S := by
  haveI := Algebra.Smooth.isRegularRing_localizationAtPrime K q
  haveI : IsRegularRing S :=
    IsRegularRing.of_ringEquiv
      (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) S).toRingEquiv
  haveI : IsRegularLocalRing S :=
    Algebra.Smooth.isRegularLocalRing_of_isLocalizationAtPrime K q S
  exact IsIntegrallyClosed.of_isRegularRing_of_isLocalRing S

/-! ### Stalks of a smooth scheme -/

namespace AlgebraicGeometry

open CategoryTheory in
/-- **THE STALKS OF A SCHEME SMOOTH OVER A FIELD ARE INTEGRALLY CLOSED**
(PROVEN 2026-07-31).

This is the geometric statement the project wanted, and it stands one step above
`isDomain_stalk_of_smooth_over_field` and `isReduced_of_smooth_over_field_stalkwise`, which
say the stalks are domains and reduced.

The chart bookkeeping is copied from
`exists_isRegularLocalRing_quotient_indepList_of_smooth_over_field` in `RegularStalks.lean`
and is unchanged: `Smooth.exists_isStandardSmooth` produces an affine `V ∋ z` with
`Γ(Z, V)` standard smooth over `Γ(Spec K, U)`; `Spec K` is a ONE-POINT space so `U = ⊤` and
`Γ(Spec K, ⊤) ≃+* K`; and `IsAffineOpen.isLocalization_stalk` presents `𝒪_{Z,z}` as
`Γ(Z, V)` localised at the prime of `z`.  `Algebra.IsStandardSmooth → Algebra.Smooth` is a
mathlib instance (`StandardSmoothCotangent.lean`), so
`Algebra.Smooth.isIntegrallyClosed_of_isLocalizationAtPrime` applies directly. -/
theorem isIntegrallyClosed_stalk_of_smooth_over_field {K : Type u} [Field K]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of K)) (hf : Smooth f) (z : Z) :
    IsIntegrallyClosed ↥(Z.presheaf.stalk z) := by
  haveI := hf
  obtain ⟨U, hU, V, hV, hzV, ele, hss⟩ := Smooth.exists_isStandardSmooth f z
  have hfz : f.base z ∈ U := ele hzV
  haveI : Subsingleton ↥(Spec (CommRingCat.of K)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have hUtop : U = ⊤ := by
    refine le_antisymm le_top fun x _ => ?_
    have hx : x = f.base z := Subsingleton.elim _ _
    exact hx ▸ hfz
  subst hUtop
  let eK : K ≃+* ↥Γ(Spec (CommRingCat.of K), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  letI : Algebra K ↥Γ(Z, V) := ((f.appLE ⊤ V ele).hom.comp eK.toRingHom).toAlgebra
  haveI : Algebra.IsStandardSmooth K ↥Γ(Z, V) :=
    RingHom.isStandardSmooth_respectsIso.2 _ eK hss
  haveI : Algebra.Smooth K ↥Γ(Z, V) := inferInstance
  letI : Algebra ↥Γ(Z, V) ↥(Z.presheaf.stalk z) :=
    Z.presheaf.algebra_section_stalk ⟨z, hzV⟩
  haveI hstalk : IsLocalization.AtPrime ↥(Z.presheaf.stalk z)
      (hV.primeIdealOf ⟨z, hzV⟩).asIdeal := hV.isLocalization_stalk ⟨z, hzV⟩
  exact Algebra.Smooth.isIntegrallyClosed_of_isLocalizationAtPrime K
    (hV.primeIdealOf ⟨z, hzV⟩).asIdeal ↥(Z.presheaf.stalk z)

end AlgebraicGeometry

open CategoryTheory AlgebraicGeometry in
/-- **THE STALKS OF AN ABELIAN SCHEME OVER A FIELD ARE INTEGRALLY CLOSED** (PROVEN
2026-07-31) — the shape `Fermat/FLT/Modularity/TateModule.lean` holds, where the smoothness
comes from `AbelianSchemeStruct.smooth`.

WHAT THIS IS FOR.  Together with `isDomain_stalk_of_smooth_over_field` it makes the reduction
of `exists_pow_eq_stalkMap_mulByNat_prime` to the FUNCTION FIELD available: `𝒪_{A',x}` is a
domain, so it embeds in `k(A')`, and it is integrally closed, so a `p`-th root in `k(A')` of
an element of `𝒪_{A',x}` — being a root of the monic `T ^ p - b` — lies back in `𝒪_{A',x}`.
The leaf's `∀ x : A'` then collapses to one statement about one field.  **The OTHER half of
that leaf, the criterion `{y ∈ K : d y = 0} = K ^ p` for `K` the function field of a smooth
variety over a perfect field, is separate missing library and is NOT supplied here.** -/
theorem Fermat.AbelianSchemeStruct.isIntegrallyClosed_stalk {k : Type u} [Field k]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)} (ab : Fermat.AbelianSchemeStruct f)
    (x : A) : IsIntegrallyClosed ↥(A.presheaf.stalk x) :=
  AlgebraicGeometry.isIntegrallyClosed_stalk_of_smooth_over_field f ab.smooth x

end
