/-
Modularity/RegularStalks.lean — own work for the Fermat project (not
vendored from the FLT project).

# Regular local stalks of a scheme smooth over a field

This module carries ONE theorem and its private commutative-algebra tower:

  `isRegularLocalRing_stalk_of_smooth_over_field` — if `Z ⟶ Spec K` is
  smooth and `K` is a field, then every stalk `𝒪_{Z,z}` is a regular
  local ring.

**WHY IT LIVES HERE AND NOT WHERE IT WAS PROVEN.**  The whole tower was
written inside `Modularity/KhareWintenberger.lean`, which is strictly
DOWNSTREAM of `Modularity/AbelianSchemeIsogeny.lean`
(`KhareWintenberger` `public import`s `TateModule`, which `public import`s
`AbelianSchemeIsogeny`).  `AbelianSchemeIsogeny.lean` needs exactly this
statement for the miracle-flatness input `isRegularLocalRing_stalk_of_smooth`
of `flat_of_finite_fibres_endo`, and could not reach it.  So the tower was
HOISTED here, upstream of both, on 2026-07-27; `KhareWintenberger.lean` now
consumes it through the import chain instead of declaring it, and nothing
was restated or reproved.  The declarations are byte-identical to the
originals, in the same namespace `GaloisRepresentation.Modularity`, so every
existing reference resolves unchanged.

## Contents, bottom-up

* `exists_finset_card_span_insert_eq_maximalIdeal` — Steinitz exchange: an
  element of `𝔪 ∖ 𝔪²` belongs to a minimal generating set of `𝔪`.
* `isRegularLocalRing_quotient_span_singleton` — `R` regular local and
  `x ∈ 𝔪 ∖ 𝔪²` gives `R ⧸ (x)` regular local.  Mathlib has no form of this.
* `isRegularLocalRing_quotient_span_list_aux` — the list induction: a
  quotient by part of a regular system of parameters is regular local.
* `nonempty_ringEquiv_localizationAtPrime_quotient_map_ker` — a localization
  of a quotient, presented as a quotient of a localization.
* `exists_isRegularLocalRing_quotient_indepList_of_submersivePresentation`
  and its `IsStandardSmooth` / localization / scheme-level corollaries —
  the Jacobian criterion, presenting the stalk as regular-local modulo an
  independent list.
* `isRegularLocalRing_stalk_of_smooth_over_field` — the assembly.

`isDomain_of_isRegularLocalRing` was deliberately NOT hoisted: it is not in
this theorem's dependency cone (it is a sibling consumer of the exchange
lemma), and it stays in `KhareWintenberger.lean` with its own consumers.
-/
module

public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Data.ENat.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.RingTheory.Spectrum.Prime.Topology

@[expose] public section

namespace GaloisRepresentation.Modularity

universe u

/-- **EXCHANGE STEP: AN ELEMENT OF `𝔪 ∖ 𝔪²` LIES IN A MINIMAL GENERATING SET**
(**PROVEN 2026-07-26**, the combinatorial half of `isDomain_of_isRegularLocalRing`).

For `R` noetherian local with `(maximalIdeal R).spanFinrank = n + 1` and
`x ∈ 𝔪 ∖ 𝔪²`, there is a finset `T` of `n` elements with
`span (insert x T) = 𝔪`.

THE PROOF is Steinitz exchange done by hand, which is what lets the whole
`regular ⟹ domain` development avoid the cotangent space entirely. Take a
generating finset `G` of `𝔪` with `#G = n + 1` and write `x = ∑_{g ∈ G} a_g g`.
Not every `a_g` lies in `𝔪`, since otherwise `x ∈ 𝔪 · 𝔪 = 𝔪²`; pick `g₀` with
`a_{g₀} ∉ 𝔪`, hence a UNIT because `R` is local. Then
`g₀ = a_{g₀}⁻¹ (x − ∑_{g ≠ g₀} a_g g)`, so `G ⊆ span (insert x (G.erase g₀))`
and `T := G.erase g₀` works. -/
theorem exists_finset_card_span_insert_eq_maximalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hx2 : x ∉ (IsLocalRing.maximalIdeal R) ^ 2)
    {n : ℕ} (hn : (IsLocalRing.maximalIdeal R).spanFinrank = n + 1) :
    ∃ T : Finset R, T.card = n ∧
      Ideal.span (insert x (T : Set R)) = IsLocalRing.maximalIdeal R := by
  classical
  obtain ⟨G, hGcard, hGspan⟩ :=
    (IsNoetherian.noetherian (IsLocalRing.maximalIdeal R)).exists_span_finset_card_eq_spanFinrank
  rw [hn] at hGcard
  have hxG : x ∈ Submodule.span R (G : Set R) := by rw [hGspan]; exact hx
  obtain ⟨a, -, ha⟩ := Submodule.mem_span_finset.1 hxG
  have hsome : ∃ g ∈ G, a g ∉ IsLocalRing.maximalIdeal R := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    refine hx2 ?_
    rw [pow_two, ← ha]
    refine Ideal.sum_mem _ fun g hg => ?_
    rw [smul_eq_mul]
    exact Ideal.mul_mem_mul (hcon g hg) (by rw [← hGspan]; exact Submodule.subset_span hg)
  obtain ⟨g₀, hg₀G, hg₀u⟩ := hsome
  refine ⟨G.erase g₀, by rw [Finset.card_erase_of_mem hg₀G, hGcard]; rfl, ?_⟩
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro y hy
    rcases hy with rfl | hy
    · exact hx
    · rw [← hGspan]
      exact Submodule.subset_span (Finset.mem_of_mem_erase (by exact_mod_cast hy))
  · rw [← hGspan, Ideal.span_le]
    intro g hg
    by_cases hgg : g = g₀
    · subst hgg
      have hsplit : ∑ h ∈ G, a h • h = a g • g + ∑ h ∈ G.erase g, a h • h :=
        (Finset.add_sum_erase _ _ hg).symm
      have hag : a g * g = x - ∑ h ∈ G.erase g, a h • h := by
        rw [← smul_eq_mul, ← ha, hsplit]; ring
      have hkey : a g * g ∈ Ideal.span (insert x ((G.erase g : Finset R) : Set R)) := by
        rw [hag]
        refine Ideal.sub_mem _ (Ideal.subset_span (Set.mem_insert _ _)) ?_
        refine Ideal.sum_mem _ fun h hh => ?_
        rw [smul_eq_mul]
        exact Ideal.mul_mem_left _ _
          (Ideal.subset_span (Set.mem_insert_of_mem _ (by exact_mod_cast hh)))
      obtain ⟨u, hu⟩ := IsLocalRing.notMem_maximalIdeal.1 hg₀u
      have hmul := Ideal.mul_mem_left
        (Ideal.span (insert x ((G.erase g : Finset R) : Set R))) ((↑u⁻¹ : R)) hkey
      rwa [← mul_assoc, ← hu, Units.inv_mul, one_mul] at hmul
    · exact Ideal.subset_span
        (Set.mem_insert_of_mem _ (by exact_mod_cast Finset.mem_erase.2 ⟨hgg, hg⟩))

/-- **REGULAR LOCAL MOD ONE ELEMENT OF `𝔪 ∖ 𝔪²` IS REGULAR LOCAL**
(**PROVEN 2026-07-26**).

For `R` regular local and `x ∈ 𝔪 ∖ 𝔪²`, the quotient `R ⧸ (x)` is again a
regular local ring — of embedding dimension and Krull dimension one less.

This is the single-element case of "a quotient by part of a regular system of
parameters is regular", and mathlib has NO form of it: `RegularLocalRing/`
consists of exactly two files (`Defs.lean`, `Polynomial.lean`) and neither
mentions quotients. It is a general, reusable statement and a genuine mathlib
contribution, on a par with `isDomain_of_isRegularLocalRing` above.

THE PROOF is the two halves of Krull's height theorem squeezing `dim R ⧸ (x)`
against the embedding dimension, exactly as in the inductive step of
`isDomain_of_isRegularLocalRing_aux`:

* `𝔪 ⊄ 𝔪²` gives `spanFinrank 𝔪 = m + 1`, hence `ringKrullDim R = m + 1` by
  regularity;
* the exchange lemma `exists_finset_card_span_insert_eq_maximalIdeal` (PROVEN
  above) produces `T` with `#T = m` and `span (insert x T) = 𝔪`; since `x ↦ 0`
  the image of `T` alone generates `𝔪 (R ⧸ (x))`, so
  `spanFinrank 𝔪 (R ⧸ (x)) ≤ m`;
* `ringKrullDim_le_ringKrullDim_quotient_add_encard` gives
  `ringKrullDim R ≤ ringKrullDim (R ⧸ (x)) + 1`, and cancelling the `+ 1` in
  `WithBot ℕ∞` (`ENat.WithBot.add_le_add_one_right_iff`) gives
  `m ≤ ringKrullDim (R ⧸ (x))`.

`IsRegularLocalRing.of_spanFinrank_maximalIdeal_le` closes it: the reverse
inequality `ringKrullDim ≤ spanFinrank 𝔪` is free.

NOTE this is deliberately a SEPARATE declaration rather than a refactoring of
`isDomain_of_isRegularLocalRing_aux`, whose inductive step contains the same
argument inline. That file region has another owner and concurrent worktrees
are editing it; duplicating twenty lines is cheaper than the merge conflict. -/
theorem isRegularLocalRing_quotient_span_singleton
    {R : Type u} [CommRing R] [IsRegularLocalRing R] {x : R}
    (hxm : x ∈ IsLocalRing.maximalIdeal R)
    (hx2 : x ∉ (IsLocalRing.maximalIdeal R) ^ 2) :
    IsRegularLocalRing (R ⧸ Ideal.span {x}) := by
  classical
  -- the embedding dimension is a successor, since `x ∈ 𝔪 ∖ 𝔪²`
  obtain ⟨m, hn⟩ : ∃ m, (IsLocalRing.maximalIdeal R).spanFinrank = m + 1 := by
    rcases Nat.eq_zero_or_pos (IsLocalRing.maximalIdeal R).spanFinrank with h | h
    · exfalso
      have hbot : IsLocalRing.maximalIdeal R = ⊥ :=
        (Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).1 h
      rw [hbot] at hxm
      simp only [Ideal.mem_bot] at hxm
      exact hx2 (hxm ▸ Ideal.zero_mem _)
    · exact ⟨_, (Nat.succ_pred_eq_of_pos h).symm⟩
  have hdim : ringKrullDim R = ((m + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R), hn]
  obtain ⟨T, hTcard, hTspan⟩ := exists_finset_card_span_insert_eq_maximalIdeal hxm hx2 hn
  set I : Ideal R := Ideal.span {x} with hI
  have hIm : I ≤ IsLocalRing.maximalIdeal R := by rw [hI, Ideal.span_le]; simpa using hxm
  have hInt : I ≠ ⊤ := fun h =>
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (h ▸ hIm))
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hInt
  haveI : IsLocalRing (R ⧸ I) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hmapmax : (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk I)
      = IsLocalRing.maximalIdeal (R ⧸ I) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hsr : (IsLocalRing.maximalIdeal (R ⧸ I)).spanFinrank ≤ m := by
    have himg : IsLocalRing.maximalIdeal (R ⧸ I)
        = Ideal.span ((Ideal.Quotient.mk I) '' (T : Set R)) := by
      rw [← hmapmax, ← hTspan, Ideal.map_span, Set.image_insert_eq]
      have hx0 : (Ideal.Quotient.mk I) x = 0 := by
        rw [Ideal.Quotient.eq_zero_iff_mem, hI]; exact Ideal.subset_span rfl
      rw [hx0, Ideal.span_insert_zero]
    rw [himg]
    refine le_trans (Submodule.spanFinrank_span_le_ncard_of_finite
      ((T : Set R).toFinite.image _)) ?_
    exact le_trans (Set.ncard_image_le (T : Set R).toFinite) (by simp [hTcard])
  have hjac : ({x} : Set R) ⊆ Ring.jacobson R := by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    show y ∈ Ring.jacobson R
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
    exact hxm
  have hkey : ringKrullDim R ≤ ringKrullDim (R ⧸ I) + 1 := by
    have h := ringKrullDim_le_ringKrullDim_quotient_add_encard ({x} : Set R) hjac
    simpa [hI] using h
  have hdimq : ((m : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ I) := by
    rw [hdim] at hkey
    push_cast at hkey
    exact ENat.WithBot.add_le_add_one_right_iff.mp hkey
  exact IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _
    (le_trans (by exact_mod_cast hsr) hdimq)

/-- **REGULAR LOCAL MOD A LIST INDEPENDENT MOD `𝔪²` IS REGULAR LOCAL**
(**PROVEN 2026-07-26** — the commutative-algebra ENGINE under
`isRegularLocalRing_stalk_of_smooth_over_field`).

For `R` regular local and `l = [f₀, …, f_{c-1}]` a list in `𝔪` satisfying the
ITERATED INDEPENDENCE condition

    ∀ n < c,  f_n ∉ 𝔪² ⊔ (f₀, …, f_{n-1}),

the quotient `R ⧸ (f₀, …, f_{c-1})` is again a regular local ring (of dimension
`dim R − c`). This is "a quotient by part of a regular system of parameters is
regular" in the generality the smooth case needs.

WHY THE HYPOTHESIS IS IN THIS FORM. The mathematically natural hypothesis is
that the images of the `f_i` be LINEARLY INDEPENDENT in the cotangent space
`𝔪/𝔪²` over the residue field. That is equivalent to the displayed condition —
a family in a vector space is independent iff no member lies in the span of its
predecessors — but the displayed form is what the induction consumes directly,
with no linear algebra and no residue-field bookkeeping at all. A future
consumer holding the linear-independence form should convert to this one; the
conversion is pure linear algebra over `IsLocalRing.CotangentSpace`.

THE PROOF is induction on `c`, quantified over the RING as well (as in
`isDomain_of_isRegularLocalRing_aux`, and for the same reason: the step passes
to `R ⧸ (f₀)`). At `c = 0` the ideal is `⊥` and `RingEquiv.quotientBot`
finishes. At `c = m + 1`:

* `n = 0` of the hypothesis says `f₀ ∈ 𝔪 ∖ 𝔪²`, so
  `isRegularLocalRing_quotient_span_singleton` makes `R' := R ⧸ (f₀)` regular
  local;
* the hypothesis TRANSPORTS to the mapped tail `t.map (mk (f₀))` in `R'`
  verbatim: `𝔪'² ⊔ (t.take n)` is the image of `𝔪² ⊔ (f₀ :: t.take n)`, and
  since that ideal contains `ker (mk (f₀)) = (f₀)`, `Ideal.comap_map_of_surjective`
  turns membership upstairs into membership downstairs with no loss. This is
  precisely why the condition is stated with the PREFIX `(f₀, …, f_{n-1})`
  rather than merely `f_n ∉ 𝔪²`: the prefix is what absorbs the kernel;
* the induction hypothesis applies to the tail, and
  `DoubleQuot.quotQuotEquivQuotSup` reassembles
  `(R ⧸ (f₀)) ⧸ (t) ≃+* R ⧸ ((f₀) ⊔ (t)) = R ⧸ (f₀ :: t)`.

Indices are by POSITION (`l[n]`, `l.take n`) rather than by splitting `l` into
`t ++ x :: s`: the mapped-list lemmas `List.getElem_map` and `List.map_take`
exist at this pin and make the transport a two-line rewrite, whereas the
split form needs `List.map_eq_append_iff`, which does NOT exist here. -/
theorem isRegularLocalRing_quotient_span_list_aux (c : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R] (l : List R),
      l.length = c →
      (∀ (n : ℕ) (hn : n < l.length),
        l[n] ∈ IsLocalRing.maximalIdeal R ∧
          l[n] ∉ (IsLocalRing.maximalIdeal R) ^ 2 ⊔ Ideal.span {y | y ∈ l.take n}) →
      IsRegularLocalRing (R ⧸ Ideal.span {y | y ∈ l}) := by
  classical
  induction c with
  | zero =>
    intro R _ _ l hlen _
    have hl : l = [] := List.eq_nil_of_length_eq_zero hlen
    subst hl
    have hbot : Ideal.span {y : R | y ∈ ([] : List R)} = ⊥ := by simp
    rw [hbot]
    exact IsRegularLocalRing.of_ringEquiv (RingEquiv.quotientBot R).symm
  | succ m ih =>
    intro R _ _ l hlen hind
    obtain ⟨x, t, rfl⟩ : ∃ x t, l = x :: t := by
      cases l with
      | nil => simp at hlen
      | cons a s => exact ⟨a, s, rfl⟩
    have htlen : t.length = m := by simpa using hlen
    -- the head lies in `𝔪 ∖ 𝔪²`
    obtain ⟨hxm, hx2'⟩ := hind 0 (by simp)
    simp only [List.getElem_cons_zero, List.take_zero] at hxm hx2'
    have hx2 : x ∉ (IsLocalRing.maximalIdeal R) ^ 2 := fun h => hx2' (Ideal.mem_sup_left h)
    set I : Ideal R := Ideal.span {x} with hI
    set f := Ideal.Quotient.mk I with hf
    haveI : IsRegularLocalRing (R ⧸ I) := isRegularLocalRing_quotient_span_singleton hxm hx2
    have hfx : f x = 0 := by
      rw [hf, Ideal.Quotient.eq_zero_iff_mem, hI]; exact Ideal.subset_span rfl
    have hker : Ideal.comap f (⊥ : Ideal (R ⧸ I)) = I := Ideal.mk_ker
    -- membership in the image of an ideal CONTAINING `ker f = (x)` loses nothing
    have hmem : ∀ (J : Ideal R), I ≤ J → ∀ y : R, f y ∈ J.map f ↔ y ∈ J := by
      intro J hJ y
      rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective f Ideal.Quotient.mk_surjective,
        hker, sup_eq_left.mpr hJ]
    have hmaxq : IsLocalRing.maximalIdeal (R ⧸ I) = (IsLocalRing.maximalIdeal R).map f :=
      (IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective).symm
    -- transport the independence hypothesis to the quotient
    have hind' : ∀ (n : ℕ) (hn : n < (t.map f).length),
        (t.map f)[n] ∈ IsLocalRing.maximalIdeal (R ⧸ I) ∧
          (t.map f)[n] ∉ (IsLocalRing.maximalIdeal (R ⧸ I)) ^ 2 ⊔
            Ideal.span {y | y ∈ (t.map f).take n} := by
      intro n hn
      have hn' : n < t.length := by simpa using hn
      obtain ⟨h1, h2⟩ := hind (n + 1) (by simp [hn'])
      simp only [List.getElem_cons_succ, List.take_succ_cons] at h1 h2
      have hget : (t.map f)[n] = f t[n] := by simp
      constructor
      · rw [hget, hmaxq]; exact Ideal.mem_map_of_mem _ h1
      · rw [hget]
        intro hcon
        refine h2 ?_
        have hspanmap : (Ideal.span {y : R | y ∈ x :: t.take n}).map f
            = Ideal.span {y | y ∈ (t.map f).take n} := by
          have e1 : {y : R | y ∈ x :: t.take n} = insert x {y : R | y ∈ t.take n} := by
            ext y; simp
          have e2 : {y | y ∈ (t.map f).take n} = f '' {y : R | y ∈ t.take n} := by
            ext y; simp [← List.map_take, List.mem_map]
          rw [Ideal.map_span, e1, Set.image_insert_eq, hfx, e2, Ideal.span_insert_zero]
        have hJ : ((IsLocalRing.maximalIdeal R) ^ 2 ⊔ Ideal.span {y | y ∈ x :: t.take n}).map f
            = (IsLocalRing.maximalIdeal (R ⧸ I)) ^ 2 ⊔
              Ideal.span {y | y ∈ (t.map f).take n} := by
          rw [Ideal.map_sup, hmaxq, ← Ideal.map_pow, hspanmap]
        rw [← hmem _ ?_ t[n], hJ]
        · exact hcon
        · rw [hI, Ideal.span_le]
          intro z hz
          rw [Set.mem_singleton_iff] at hz
          subst hz
          exact Ideal.mem_sup_right (Ideal.subset_span (by simp))
    haveI := ih (R ⧸ I) (t.map f) (by simpa using htlen) hind'
    -- reassemble `(R ⧸ (x)) ⧸ (t) ≃+* R ⧸ (x :: t)`
    have hspan : Ideal.span {y | y ∈ (t.map f)} = (Ideal.span {y | y ∈ t}).map f := by
      rw [Ideal.map_span]
      congr 1
      ext y
      simp [List.mem_map]
    rw [hspan] at this
    have hsup : I ⊔ Ideal.span {y | y ∈ t} = Ideal.span {y : R | y ∈ x :: t} := by
      rw [hI, ← Ideal.span_union]
      congr 1
      ext y
      simp
    exact IsRegularLocalRing.of_ringEquiv
      ((DoubleQuot.quotQuotEquivQuotSup I (Ideal.span {y | y ∈ t})).trans
        (Ideal.quotEquivOfEq hsup))

/-- **LOCALIZATION COMMUTES WITH THE QUOTIENT** (**PROVEN 2026-07-26**).

For `f : R →+* A` surjective, `p` a prime of `A` and `q = f⁻¹ p`, any
localization `Bq` of `R` at `q` satisfies `Bq ⧸ (ker f)·Bq ≅ A_p`.

STATED OVER AN ABSTRACT `Bq` ON PURPOSE. With the concrete
`Localization.AtPrime q` in the statement, the unification that
`IsLocalization.of_surjective` performs has to unfold the Ore-localization
`CommRing` instance underneath a quotient, and elaboration dies at `whnf`
inside the default heartbeat budget. Over a variable `Bq` nothing can be
unfolded and the same proof is instant. This is the project's standing
"state helpers over a variable base" rule in a new spot.

THE PROOF is `IsLocalization.of_surjective` applied to the pair of quotient
maps `R ↠ R ⧸ ker f` and `Bq ↠ Bq ⧸ (ker f)·Bq`, whose compatibility square
is definitional once the `R ⧸ ker f`-algebra structure on the target is taken
to be mathlib's `Ideal.Quotient.algebraQuotientOfLEComap`; the resulting
localization of `R ⧸ ker f` is transported to `A` along
`RingHom.quotientKerEquivOfSurjective` by `IsLocalization.ringEquivOfRingEquiv`. -/
theorem nonempty_ringEquiv_localizationAtPrime_quotient_map_ker
    {R : Type*} [CommRing R] {A : Type*} [CommRing A]
    (f : R →+* A) (hf : Function.Surjective f) {p : Ideal A} [p.IsPrime]
    (Bq : Type*) [CommRing Bq] [Algebra R Bq]
    [IsLocalization (Ideal.comap f p).primeCompl Bq] :
    Nonempty ((Localization.AtPrime p) ≃+*
      (Bq ⧸ Ideal.map (algebraMap R Bq) (RingHom.ker f))) := by
  classical
  set q : Ideal R := Ideal.comap f p with hqdef
  haveI : q.IsPrime := Ideal.IsPrime.comap _
  set J : Ideal R := RingHom.ker f with hJdef
  set fB : R →+* Bq := algebraMap R Bq with hfBdef
  have hle : J ≤ Ideal.comap fB (Ideal.map fB J) := Ideal.le_comap_map
  letI : Algebra (R ⧸ J) (Bq ⧸ Ideal.map fB J) := Ideal.Quotient.algebraQuotientOfLEComap hle
  have hH : (Ideal.Quotient.mk (Ideal.map fB J)).comp (algebraMap R Bq)
      = (algebraMap (R ⧸ J) (Bq ⧸ Ideal.map fB J)).comp (Ideal.Quotient.mk J) := by
    refine RingHom.ext fun x => ?_
    rfl
  have hH' : RingHom.ker (Ideal.Quotient.mk (Ideal.map fB J))
      ≤ Ideal.map (algebraMap R Bq) (RingHom.ker (Ideal.Quotient.mk J)) := by
    rw [Ideal.mk_ker, Ideal.mk_ker]
  haveI hloc : IsLocalization (Submonoid.map (Ideal.Quotient.mk J) q.primeCompl)
      (Bq ⧸ Ideal.map fB J) :=
    IsLocalization.of_surjective q.primeCompl Bq (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective (Ideal.Quotient.mk (Ideal.map fB J))
      Ideal.Quotient.mk_surjective hH hH'
  have hmon : Submonoid.map f q.primeCompl = p.primeCompl := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro ha
      obtain ⟨x, rfl⟩ := hf a
      exact ⟨x, ha, rfl⟩
  let ε : (R ⧸ J) ≃+* A := RingHom.quotientKerEquivOfSurjective hf
  have hεmk : ∀ x : R, ε (Ideal.Quotient.mk J x) = f x := fun _ => rfl
  have hHmon : Submonoid.map ε.toMonoidHom (Submonoid.map (Ideal.Quotient.mk J) q.primeCompl)
      = p.primeCompl := by
    rw [← hmon]
    ext a
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, hεmk x⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨Ideal.Quotient.mk J x, ⟨x, hx, rfl⟩, hεmk x⟩
  exact ⟨(IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.map (Ideal.Quotient.mk J) q.primeCompl)
    (S := Bq ⧸ Ideal.map fB J) (T := p.primeCompl)
    (Q := Localization.AtPrime p) ε hHmon).symm⟩

/-- **THE JACOBIAN CRITERION, IN THE FORM THE REGULARITY ENGINE CONSUMES**
(**PROVEN 2026-07-26** — this is the whole mathematical content of
`exists_isRegularLocalRing_quotient_indepList_of_smooth_over_field`).

Given a `SubmersivePresentation` `P` of a `K`-algebra `A` (so
`A = K[x_ι] ⧸ (r_σ)` with the `σ x σ` Jacobian minor a unit in `A`) and a prime
`p` of `A`, the localization `A_p` is `B ⧸ (r_σ)B` for `B := K[x_ι]_q` the
polynomial ring localized at `q := f⁻¹ p`, which is REGULAR LOCAL for free, and
the images of the `r_σ` in `B` satisfy the iterated independence condition of
`isRegularLocalRing_quotient_span_list_aux`.

THE ROUTE ACTUALLY TAKEN, and it is NOT the cotangent-complex route the parent
docstring predicted. The parent proposed base-changing
`SubmersivePresentation.cotangentComplex_injective` (split by
`sectionCotangent_comp`) to the residue field. That works, but it is not
needed: `PreSubmersivePresentation.jacobian` is by definition the image in `A`
of the DETERMINANT of the concrete matrix
`M i j = pderiv (P.map i) (P.relation j)` over `K[x_ι]`
(`jacobian_eq_jacobiMatrix_det`, `jacobiMatrix_apply`), so the independence is
plain linear algebra over the residue field, with no `Extension.Cotangent`
translation anywhere. Concretely, writing `e : K[x_ι] → κ(q)` for the residue
map and `d f := fun i => e (pderiv (P.map i) f)`:

* `d` is a `K`-derivation into `σ → κ(q)`, so it KILLS `q²` (both factors
  die under `e`) and sends `Ideal.span T` into the `κ(q)`-span of `d '' T`
  whenever `T ⊆ q` (the Leibniz term `e b * d a` vanishes for `b ∈ q`);
* `det M ∉ q`, since its image is the jacobian, a UNIT of `A`, and `p` is
  proper — so the matrix `e ∘ M` is invertible over the field `κ(q)` and its
  COLUMNS `j ↦ d (P.relation j)` are linearly independent
  (`Matrix.linearIndependent_cols_iff_isUnit`);
* a membership `r_n ∈ 𝔪_B² ⊔ (r_0, …, r_{n-1})` descends through
  `IsLocalization.mem_map_algebraMap_iff` to `u * r_n ∈ q² ⊔ (r_0, …, r_{n-1})`
  in `K[x_ι]` for some `u ∉ q`; applying `d` gives
  `e u • d r_n ∈ span_κ {d r_i : i < n}` with `e u ≠ 0`, contradicting the
  independence just established.

THE LIST is `Finset.univ.toList` over `σ`; its `Nodup` is exactly what supplies
`L[n] ∉ L.take n`, which is the index-level input to
`LinearIndependent.notMem_span_image`. No enumeration by `Fin c` and no list
surgery is needed.

NO DIMENSION THEORY IS USED, and none is available: this is why the route goes
through independence in `𝔪_B/𝔪_B²` rather than through `dim A_p = dim B - c`. -/
theorem exists_isRegularLocalRing_quotient_indepList_of_submersivePresentation
    {K : Type u} [Field K] {A : Type u} [CommRing A] [Algebra K A]
    {ι σ : Type} [Finite ι] [Finite σ]
    (P : Algebra.SubmersivePresentation K A ι σ) (p : Ideal A) [hp : p.IsPrime] :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsRegularLocalRing B) (l : List B),
      (∀ (n : ℕ) (hn : n < l.length),
        l[n] ∈ IsLocalRing.maximalIdeal B ∧
          l[n] ∉ (IsLocalRing.maximalIdeal B) ^ 2 ⊔ Ideal.span {y | y ∈ l.take n}) ∧
      Nonempty ((Localization.AtPrime p) ≃+* (B ⧸ Ideal.span {y | y ∈ l})) := by
  classical
  haveI : Fintype σ := Fintype.ofFinite σ
  -- The prime of the polynomial ring under `p`.
  have hsurjA : Function.Surjective (algebraMap P.Ring A) := P.algebraMap_surjective
  set q : Ideal P.Ring := p.comap (algebraMap P.Ring A) with hqdef
  haveI hq : q.IsPrime := Ideal.IsPrime.comap _
  set B := Localization.AtPrime q with hBdef
  haveI hBreg : IsRegularLocalRing B := inferInstance
  set fB : P.Ring →+* B := algebraMap P.Ring B with hfBdef
  have hmax : Ideal.map fB q = IsLocalRing.maximalIdeal B :=
    IsLocalization.AtPrime.map_eq_maximalIdeal q B
  -- The residue field of `q` and the "partial derivatives mod q" map.
  set κ := q.ResidueField with hκdef
  set e : P.Ring →+* κ := algebraMap P.Ring κ with hedef
  have hezero : ∀ x : P.Ring, e x = 0 ↔ x ∈ q := fun x =>
    Ideal.algebraMap_residueField_eq_zero
  set d : P.Ring → (σ → κ) := fun g i => e (MvPolynomial.pderiv (P.map i) g) with hddef
  have hdadd : ∀ x y : P.Ring, d (x + y) = d x + d y := by
    intro x y; funext i; simp [hddef]
  have hdzero : d 0 = 0 := by funext i; simp [hddef]
  have hdmul : ∀ x y : P.Ring, d (x * y) = e x • d y + e y • d x := by
    intro x y; funext i
    simp only [hddef, Pi.add_apply, Pi.smul_apply, smul_eq_mul, MvPolynomial.pderiv_mul,
      map_add, map_mul]
    ring
  -- `d` kills `q²`.
  have hd_sq : ∀ x ∈ q ^ 2, d x = 0 := by
    intro x hx
    rw [sq] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro m hm n hn
      rw [hdmul, (hezero m).mpr hm, (hezero n).mpr hn, zero_smul, zero_smul, add_zero]
    · intro a b ha hb; rw [hdadd, ha, hb, add_zero]
  -- `d` sends `span T` into the κ-span of `d '' T`, for `T ⊆ q`.
  have hd_span : ∀ (T : Set P.Ring), T ⊆ (q : Set P.Ring) →
      ∀ x ∈ Ideal.span T, d x ∈ Submodule.span κ (d '' T) := by
    intro T hT x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => rw [hdzero]; exact Submodule.zero_mem _
    | add a b _ _ ia ib => rw [hdadd]; exact Submodule.add_mem _ ia ib
    | smul a b hb ib =>
        have hbq : b ∈ q := (Ideal.span_le.mpr hT) hb
        rw [smul_eq_mul, hdmul, (hezero b).mpr hbq, zero_smul, add_zero]
        exact Submodule.smul_mem _ _ ib
  have hd_sup : ∀ (T : Set P.Ring), T ⊆ (q : Set P.Ring) →
      ∀ x ∈ q ^ 2 ⊔ Ideal.span T, d x ∈ Submodule.span κ (d '' T) := by
    intro T hT x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [hdadd, hd_sq y hy, zero_add]
    exact hd_span T hT z hz
  -- Every relation lies in `q`.
  have hrelq : ∀ s : σ, P.relation s ∈ q := by
    intro s
    have h1 : P.relation s ∈ P.ker := by
      rw [← P.span_range_relation_eq_ker]; exact Ideal.subset_span ⟨s, rfl⟩
    have h2 : algebraMap P.Ring A (P.relation s) = 0 := h1
    exact Ideal.mem_comap.mpr (by rw [h2]; exact p.zero_mem)
  -- The Jacobian determinant is not in `q`.
  have hjac : P.jacobiMatrix.det ∉ q := by
    intro hmem
    have h1 : P.jacobian ∈ p := by
      rw [P.jacobian_eq_jacobiMatrix_det]; exact Ideal.mem_comap.mp hmem
    exact hp.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 P.jacobian_isUnit)
  -- Hence the family `j ↦ d (relation j)` is linearly independent over κ.
  have hLI : LinearIndependent κ (fun j : σ => d (P.relation j)) := by
    have hdet : (e.mapMatrix P.jacobiMatrix).det ≠ 0 := by
      rw [← RingHom.map_det]
      intro h
      exact hjac ((hezero _).mp h)
    have hu : IsUnit (e.mapMatrix P.jacobiMatrix) :=
      Matrix.isUnit_iff_isUnit_det _ |>.mpr (isUnit_iff_ne_zero.mpr hdet)
    have hcols := Matrix.linearIndependent_cols_iff_isUnit.mpr hu
    have hcoleq : (e.mapMatrix P.jacobiMatrix).col = fun j : σ => d (P.relation j) := by
      funext j i
      simp [hddef, Matrix.col, P.jacobiMatrix_apply]
    rwa [hcoleq] at hcols
  -- The list of relations, indexed by a duplicate-free enumeration of `σ`.
  set L : List σ := (Finset.univ : Finset σ).toList with hLdef
  have hLnodup : L.Nodup := Finset.nodup_toList _
  have hLmem : ∀ s : σ, s ∈ L := by intro s; simp [hLdef]
  set l : List B := L.map (fun s => fB (P.relation s)) with hldef
  have hllen : l.length = L.length := by simp [hldef]
  have hlget : ∀ (n : ℕ) (hnL : n < L.length),
      l[n]'(by rw [hllen]; exact hnL) = fB (P.relation (L[n]'hnL)) := by
    intro n hnL; simp only [hldef, List.getElem_map]
  refine ⟨B, inferInstance, inferInstance, l, ?_, ?_⟩
  · -- the independence conditions
    intro n hn
    have hnL : n < L.length := by rw [← hllen]; exact hn
    constructor
    · rw [hlget n hnL, ← hmax]
      exact Ideal.mem_map_of_mem _ (hrelq _)
    · -- the real content
      intro hcon
      set T : Set P.Ring := P.relation '' {s | s ∈ L.take n} with hTdef
      have hTq : T ⊆ (q : Set P.Ring) := by rintro _ ⟨s, _, rfl⟩; exact hrelq s
      have hspan : Ideal.span {y : B | y ∈ l.take n} = Ideal.map fB (Ideal.span T) := by
        rw [Ideal.map_span]
        congr 1
        rw [hTdef, Set.image_image]
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_image, hldef, ← List.map_take, List.mem_map]
      have hJ : (IsLocalRing.maximalIdeal B) ^ 2 ⊔ Ideal.span {y : B | y ∈ l.take n}
          = Ideal.map fB (q ^ 2 ⊔ Ideal.span T) := by
        rw [Ideal.map_sup, Ideal.map_pow, hmax, hspan]
      rw [hJ, hlget n hnL] at hcon
      obtain ⟨⟨⟨y, hyJ⟩, ⟨s, hs⟩⟩, hey⟩ :=
        (IsLocalization.mem_map_algebraMap_iff q.primeCompl B).mp hcon
      simp only at hey
      rw [← map_mul] at hey
      obtain ⟨⟨t, ht⟩, hct⟩ := (IsLocalization.eq_iff_exists q.primeCompl B).mp hey
      simp only at hct
      -- `u * relation L[n] ∈ J` with `u ∉ q`
      set u : P.Ring := t * s with hudef
      have huq : u ∉ q := fun h => (hq.mem_or_mem h).elim ht hs
      have hmemJ : u * P.relation (L[n]'hnL) ∈ q ^ 2 ⊔ Ideal.span T := by
        have hrw : u * P.relation (L[n]'hnL) = t * y := by rw [hudef]; rw [← hct]; ring
        rw [hrw]
        exact Ideal.mul_mem_left _ _ hyJ
      have hdmem := hd_sup T hTq _ hmemJ
      rw [hdmul, (hezero _).mpr (hrelq _), zero_smul, add_zero] at hdmem
      have heu : e u ≠ 0 := fun h => huq ((hezero u).mp h)
      have hfin : d (P.relation (L[n]'hnL)) ∈ Submodule.span κ (d '' T) := by
        have hsm := Submodule.smul_mem (Submodule.span κ (d '' T)) (e u)⁻¹ hdmem
        rwa [smul_smul, inv_mul_cancel₀ heu, one_smul] at hsm
      -- but `d ∘ relation` is linearly independent and `L[n] ∉ L.take n`
      have hnotmem : (L[n]'hnL) ∉ {s | s ∈ L.take n} := by
        intro hmem
        obtain ⟨j, hj, hji⟩ := List.mem_iff_getElem.mp hmem
        rw [List.length_take] at hj
        have hjn : j < n := lt_of_lt_of_le hj (min_le_left _ _)
        rw [List.getElem_take] at hji
        have hij := hLnodup.getElem_inj_iff.mp hji
        omega
      have himg : d '' T = (fun j : σ => d (P.relation j)) '' {s | s ∈ L.take n} := by
        rw [hTdef, ← Set.image_comp]; rfl
      rw [himg] at hfin
      exact hLI.notMem_span_image hnotmem hfin
  · -- the presentation of the stalk
    have hspanl : Ideal.span {y : B | y ∈ l} = Ideal.map fB P.ker := by
      rw [← P.span_range_relation_eq_ker, Ideal.map_span]
      congr 1
      rw [← Set.range_comp]
      ext y
      simp [hldef, List.mem_map, hLmem, Function.comp_def]
    have hkerP : P.ker = RingHom.ker (algebraMap P.Ring A) := rfl
    rw [hspanl, hkerP]
    exact nonempty_ringEquiv_localizationAtPrime_quotient_map_ker
      (algebraMap P.Ring A) hsurjA B

/-- **THE SAME, FROM THE `IsStandardSmooth` CLASS** (**PROVEN 2026-07-26**):
unpacks the existential of `Algebra.IsStandardSmooth.out` into a concrete
`SubmersivePresentation` and applies the previous theorem. -/
theorem exists_isRegularLocalRing_quotient_indepList_of_isStandardSmooth
    {K : Type u} [Field K] {A : Type u} [CommRing A] [Algebra K A]
    [hA : Algebra.IsStandardSmooth K A] (p : Ideal A) [p.IsPrime] :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsRegularLocalRing B) (l : List B),
      (∀ (n : ℕ) (hn : n < l.length),
        l[n] ∈ IsLocalRing.maximalIdeal B ∧
          l[n] ∉ (IsLocalRing.maximalIdeal B) ^ 2 ⊔ Ideal.span {y | y ∈ l.take n}) ∧
      Nonempty ((Localization.AtPrime p) ≃+* (B ⧸ Ideal.span {y | y ∈ l})) := by
  obtain ⟨ι, σ, hσ, hι, ⟨Pr⟩⟩ := hA.out
  haveI := hσ
  haveI := hι
  exact exists_isRegularLocalRing_quotient_indepList_of_submersivePresentation Pr p

/-- **THE SAME, FOR AN ARBITRARY LOCALIZATION OF `A` AT `p`**
(**PROVEN 2026-07-26**).

This restatement exists purely for ELABORATION COST at the call site: the
scheme-level consumer holds the stalk `𝒪_{Z,z}`, a colimit in `CommRingCat`,
and asking Lean to unify that against the concrete `Localization.AtPrime p`
sends `whnf` into the colimit and blows the heartbeat budget. Taking the
localization as a variable `S` makes the consumer a single application. -/
theorem exists_isRegularLocalRing_quotient_indepList_of_isStandardSmooth_of_isLocalization
    {K : Type u} [Field K] {A : Type u} [CommRing A] [Algebra K A]
    [Algebra.IsStandardSmooth K A] (p : Ideal A) [p.IsPrime]
    (S : Type u) [CommRing S] [Algebra A S] [IsLocalization.AtPrime S p] :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsRegularLocalRing B) (l : List B),
      (∀ (n : ℕ) (hn : n < l.length),
        l[n] ∈ IsLocalRing.maximalIdeal B ∧
          l[n] ∉ (IsLocalRing.maximalIdeal B) ^ 2 ⊔ Ideal.span {y | y ∈ l.take n}) ∧
      Nonempty (S ≃+* (B ⧸ Ideal.span {y | y ∈ l})) := by
  obtain ⟨B, hBc, hBr, l, hindep, ⟨eqB⟩⟩ :=
    exists_isRegularLocalRing_quotient_indepList_of_isStandardSmooth (K := K) (A := A) p
  exact ⟨B, hBc, hBr, l, hindep,
    ⟨(IsLocalization.algEquiv p.primeCompl S (Localization.AtPrime p)).toRingEquiv.trans eqB⟩⟩

open CategoryTheory AlgebraicGeometry in
/-- **THE STALK OF A SMOOTH `K`-SCHEME IS A REGULAR LOCAL RING MODULO AN
INDEPENDENT LIST** (**PROVEN 2026-07-26**; cut 2026-07-26 out of
`isRegularLocalRing_stalk_of_smooth_over_field`, whose entire remaining
GEOMETRIC content it carried, and closed the same day).

For `Z` smooth over `Spec K` and `z : Z`, the stalk `𝒪_{Z,z}` is
`B ⧸ (f₀, …, f_{c-1})` for some REGULAR LOCAL `B` and some list satisfying the
iterated independence condition of `isRegularLocalRing_quotient_span_list_aux`.

THIS DECLARATION IS NOW ONLY THE CHART BOOKKEEPING. All the algebra lives in
`exists_isRegularLocalRing_quotient_indepList_of_submersivePresentation` and
its two restatements, immediately above. What happens here:

1. `AlgebraicGeometry.Smooth.exists_isStandardSmooth` gives affine opens
   `U ∋ f.base z` in `Spec K` and `V ∋ z` in `Z` with
   `(f.appLE U V e).hom.IsStandardSmooth`.
2. `Spec K` is a ONE-POINT space (`Unique (PrimeSpectrum K)` for a field), so
   the nonempty `U` is `⊤`, and `Scheme.ΓSpecIso` identifies `Γ(Spec K, ⊤)`
   with `K`. Transporting `IsStandardSmooth` across that iso is
   `RingHom.isStandardSmooth_respectsIso.2`, so `A := Γ(Z, V)` is a standard
   smooth `K`-algebra.
3. `IsAffineOpen.isLocalization_stalk` makes `𝒪_{Z,z}` a localization of `A` at
   `p := hV.primeIdealOf z`; the `Algebra Γ(Z, V) 𝒪_{Z,z}` instance has to be
   supplied by hand as `Z.presheaf.algebra_section_stalk ⟨z, hzV⟩`, because
   instance search cannot solve `↑?x = z` for `?x : ↥V` through the coercion.

CORRECTION TO THE ORIGINAL RECIPE (which is preserved below as the record of a
route that WORKS but is not the cheapest). The recipe's step 5 proposed the
cotangent complex: `SubmersivePresentation.cotangentComplex_injective`, split
by `sectionCotangent_comp`, hence stable under base change to `κ(p)`. That is
correct mathematics, and it is NOT what the proof does — the whole
`Extension.Cotangent` translation is avoidable. `jacobian` is by DEFINITION the
image of `Matrix.det` of `pderiv (P.map i) (P.relation j)`
(`jacobian_eq_jacobiMatrix_det` + `jacobiMatrix_apply`), so "the images of the
`r_σ` are independent in `𝔪_B/𝔪_B²`" is a statement about an explicit matrix
over `κ(q)` being invertible, and `Matrix.linearIndependent_cols_iff_isUnit`
closes it. See that theorem's docstring for the argument in full.

The estimate attached to this leaf at dispatch — "budget the translation, not
the mathematics" — was therefore the right shape but aimed at the wrong cost:
there was no translation to pay for. What DID cost real cycles was elaboration
performance, twice, and both times the fix was the project's own
"state helpers over a VARIABLE base" rule: unifying against the concrete
`Localization.AtPrime q` (an Ore localization) and against the stalk (a colimit
in `CommRingCat`) both send `whnf` past the heartbeat limit, and both dissolve
once the ring in question is a variable. That is why two of the three helper
theorems above exist at all.

WHY THIS IS THE RIGHT PLACE TO CUT. Everything downstream of the independence
statement was already PROVEN when the cut was made:
`isRegularLocalRing_quotient_span_singleton` and
`isRegularLocalRing_quotient_span_list_aux` (both above) are a complete,
general "quotient by part of a regular system of parameters is regular", which
mathlib does not have in any form — `RegularLocalRing/` is two files and
neither mentions quotients.

TWO ROUTES EXPLICITLY REJECTED, both recorded so nobody re-walks them:

* the **Kähler-differential / transcendence-degree** route needs the dimension
  formula `dim A_p + trdeg κ(p) = dim A`, and dimension theory over a field is
  barely present at this pin — even `dim k[x₁..xₙ] = n` is still a
  `proof_wanted` (`MvPolynomial.fin_ringKrullDim_eq_add_of_isNoetherianRing`,
  `Mathlib/RingTheory/KrullDimension/Basic.lean:94`), and there is NO
  transcendence-degree material under `KrullDimension/` at all;
* the **Cohen structure theorem** route needs both Cohen and a
  "completion regular ⟹ regular" transfer, neither of which exists here.

The route above needs NEITHER: the polynomial base is regular by an existing
instance, and the dimension drop is Krull's height theorem, which the engine
lemmas already consume. -/
theorem exists_isRegularLocalRing_quotient_indepList_of_smooth_over_field
    {K : Type u} [Field K] {Z : AlgebraicGeometry.Scheme.{u}}
    (f : Z ⟶ AlgebraicGeometry.Spec (CommRingCat.of K))
    (hf : AlgebraicGeometry.Smooth f) (z : Z) :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsRegularLocalRing B) (l : List B),
      (∀ (n : ℕ) (hn : n < l.length),
        l[n] ∈ IsLocalRing.maximalIdeal B ∧
          l[n] ∉ (IsLocalRing.maximalIdeal B) ^ 2 ⊔ Ideal.span {y | y ∈ l.take n}) ∧
      Nonempty ((Z.presheaf.stalk z : Type u) ≃+* (B ⧸ Ideal.span {y | y ∈ l})) := by
  haveI := hf
  obtain ⟨U, hU, V, hV, hzV, ele, hss⟩ := Smooth.exists_isStandardSmooth f z
  have hfz : f.base z ∈ U := ele hzV
  -- `Spec K` is a ONE-POINT space, so the affine open `U` downstairs is `⊤`
  -- and `Γ(Spec K, U)` is `K` itself.
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
  -- and the stalk is the localization of `Γ(Z, V)` at the prime of `z`
  letI : Algebra ↥Γ(Z, V) ↥(Z.presheaf.stalk z) :=
    Z.presheaf.algebra_section_stalk ⟨z, hzV⟩
  haveI hstalk : IsLocalization.AtPrime ↥(Z.presheaf.stalk z)
      (hV.primeIdealOf ⟨z, hzV⟩).asIdeal := hV.isLocalization_stalk ⟨z, hzV⟩
  exact exists_isRegularLocalRing_quotient_indepList_of_isStandardSmooth_of_isLocalization
    (K := K) (A := ↥Γ(Z, V)) (hV.primeIdealOf ⟨z, hzV⟩).asIdeal ↥(Z.presheaf.stalk z)

open CategoryTheory AlgebraicGeometry in
/-- **SMOOTH OVER A FIELD ⟹ THE STALKS ARE REGULAR LOCAL RINGS**
(**PROVEN 2026-07-26** over the single leaf
`exists_isRegularLocalRing_quotient_indepList_of_smooth_over_field` and the
commutative-algebra engine `isRegularLocalRing_quotient_span_list_aux`).

For `Z` smooth over `Spec K` with `K` any field, every local ring `𝒪_{Z,z}` is
a REGULAR local ring. Combined with `isDomain_of_isRegularLocalRing` (PROVEN
above) this gives the domain property, so this leaf is exactly the first of the
two gaps the parent's docstring named — and the second of them is closed.

WHY THIS IS THE HARD HALF. A smooth morphism has geometrically regular fibres
(EGA IV 17.5.1), so `Z` is a regular scheme over any field. Mathlib's
`AlgebraicGeometry/Morphisms/Smooth.lean` never mentions regularity: a
2026-07-26 sweep of pin `a3364fa` found ZERO cross-references between the
`Algebra.Smooth`/`RingHom.Smooth`/`AlgebraicGeometry.Smooth` hierarchy and
`IsRegularLocalRing`/`IsRegularRing`, and there is no `Geometrically/Regular.lean`.
The sweep was re-run when this leaf was cut and the result is unchanged.

THE TWO CLASSICAL ROUTES, and what each needs that the pin lacks.

* **Cohen structure theorem.** Formal smoothness makes the completion
  `𝒪̂_{Z,z}` a power-series ring over the residue field, and a local ring whose
  completion is regular is regular. Mathlib has `Algebra.FormallySmooth` and
  `Mathlib/RingTheory/Smooth/AdicCompletion.lean`, but no Cohen structure
  theorem and no "completion regular ⟹ regular" transfer.
* **Kähler differentials and the second fundamental exact sequence.** For
  `R = 𝒪_{Z,z}` with residue field `κ`, formal smoothness splits
  `0 → 𝔪/𝔪² → Ω_{A/K} ⊗_A κ → Ω_{κ/K} → 0`, whence
  `dim_κ 𝔪/𝔪² = rank Ω − trdeg(κ/K) = dim R`, which is regularity. Mathlib has
  `Mathlib/RingTheory/Smooth/Kaehler.lean`, so the exact sequence is the
  reachable part; what is missing is the dimension formula
  `dim A_p + trdeg κ(p) = dim A` for a finite-type domain over a field. Do NOT
  start there: dimension theory over a field is barely present at this pin —
  even `dim k[x₁..xₙ] = n` is still a `proof_wanted`
  (`MvPolynomial.fin_ringKrullDim_eq_add_of_isNoetherianRing`,
  `Mathlib/RingTheory/KrullDimension/Basic.lean:94`), and there is no
  transcendence-degree/dimension material anywhere under `KrullDimension/`.

* **THE THIRD ROUTE, AND THE ONE TO TAKE — smooth ASCENT of regularity from a
  base mathlib already knows is regular** (measured 2026-07-26, and it
  corrects the pessimistic reading above). The pin is much better supplied
  than the "nothing exists" sweep suggests: `IsRegularRing k` for a field,
  `IsRegularRing (MvPolynomial (Fin n) k)` and hence
  `IsRegularLocalRing (Localization.AtPrime p)` for every prime `p` of a
  polynomial ring over a field ALL discharge by `infer_instance`, out of
  `Mathlib/RingTheory/RegularLocalRing/Polynomial.lean`
  (`MvPolynomial.isRegularRing_of_isRegularRing`). `Noether normalization` is
  also present (`Mathlib/RingTheory/NoetherNormalization.lean`), and
  `Mathlib/RingTheory/KrullDimension/Regular.lean` carries the regular-sequence
  dimension drop (`ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors`
  and `ringKrullDim_add_length_eq_ringKrullDim_of_isRegular`).

  So the affine polynomial base is DONE, and the single genuinely missing
  statement is that regularity ASCENDS along a smooth ring map — concretely,
  via `Algebra.IsStandardSmooth`, that
  `k[x₁..xₙ] ⧸ (f₁, …, f_c)` localized at a prime is regular when the Jacobian
  is invertible there, i.e. that the `f_i` form a regular sequence whose images
  are linearly independent in `𝔪/𝔪²`. That is one theorem over machinery that
  exists, not a dimension theory built from scratch. Anyone taking this leaf
  should start by reading `Mathlib/RingTheory/Smooth/StandardSmooth.lean` and
  `StandardSmoothCotangent.lean`, NOT by formalizing Cohen or Noether–trdeg.

A FIRST CUT THAT WOULD HELP whoever takes this: reduce to the AFFINE statement
"`A` a smooth `K`-algebra, `p` prime ⟹ `IsRegularLocalRing (Localization.AtPrime p)`"
by transporting through an affine chart, exactly as
`AlgebraicGeometry.exists_isOpen_isIrreducible_nhds_of_isDomain_stalk` (PROVEN,
in `Fermat/FLT/Mathlib/AlgebraicGeometry/IrreducibleNhds.lean`) transports the
domain property: `Scheme.exists_Spec_apply_eq` gives an open immersion
`g : Spec R ⟶ Z` hitting `z`, `Spec.stalkIso` identifies the stalk with
`Localization.AtPrime y.asIdeal`, and `Smooth` is stable under composition with
the open immersion `g`, so `R` is a smooth `K`-algebra through
`HasRingHomProperty @Smooth RingHom.Smooth`. That reduction was NOT carried out
here — it is scheme-theoretic bookkeeping with no mathematical content, and it
is folded into the single remaining leaf above, whose docstring writes the
recipe out in five steps.

**STATUS 2026-07-26.** This node is PROVEN, in three lines, over
`exists_isRegularLocalRing_quotient_indepList_of_smooth_over_field` (**PROVEN
2026-07-26** — present the stalk as regular-local-modulo-an-independent-list)
and `isRegularLocalRing_quotient_span_list_aux` (PROVEN — that such a quotient
is regular local). **Both halves are now closed and this whole subtree is
sorry-free**: the presentation bookkeeping went through
`Smooth.exists_isStandardSmooth` plus `IsAffineOpen.isLocalization_stalk`, and
the Jacobian criterion did NOT need its cotangent-complex form — `jacobian` is
literally a determinant of partial derivatives, so the independence is an
invertible matrix over the residue field `κ(q)`. -/
theorem isRegularLocalRing_stalk_of_smooth_over_field {K : Type u} [Field K]
    {Z : AlgebraicGeometry.Scheme.{u}}
    (f : Z ⟶ AlgebraicGeometry.Spec (CommRingCat.of K))
    (hf : AlgebraicGeometry.Smooth f) (z : Z) :
    IsRegularLocalRing (Z.presheaf.stalk z) := by
  obtain ⟨B, _, _, l, hindep, ⟨e⟩⟩ :=
    exists_isRegularLocalRing_quotient_indepList_of_smooth_over_field f hf z
  haveI : IsRegularLocalRing (B ⧸ Ideal.span {y | y ∈ l}) :=
    isRegularLocalRing_quotient_span_list_aux l.length B l rfl hindep
  exact IsRegularLocalRing.of_ringEquiv e.symm

/-- **REGULAR LOCAL ⟹ DOMAIN, BY INDUCTION ON THE EMBEDDING DIMENSION**
(**PROVEN 2026-07-26** — this is mathlib's own open TODO, closed here).

The induction hypothesis has to quantify over the RING as well as the
dimension, because the inductive step passes to `R ⧸ (x)`; hence the
`∀ (R : Type u) [CommRing R] [IsRegularLocalRing R]` shape rather than a
statement about one fixed `R`.

THE PROOF (Atiyah–Macdonald 11.23 / Matsumura 14.3), by strong induction on
`d = (maximalIdeal R).spanFinrank`, which regularity identifies with
`ringKrullDim R`.

* `d = 0`: `spanFinrank 𝔪 = 0` forces `𝔪 = ⊥`, so `R` is a field.
* `d = m + 1`: `𝔪 ⊄ 𝔪²` (else Nakayama gives `𝔪 = ⊥` and `d = 0`) and `𝔪` is
  not a minimal prime (else `𝔪.height = 0 = ringKrullDim R`, contradicting
  `d = m + 1`). Since `R` is noetherian, `minimalPrimes R` is FINITE, so prime
  avoidance applies to the finite family `{𝔪²} ∪ minimalPrimes R` — with `𝔪²`
  in one of the two exceptional slots of `Ideal.subset_union_prime`, which is
  exactly why that non-prime member is allowed. It yields
  `x ∈ 𝔪`, `x ∉ 𝔪²`, `x` in no minimal prime.
* `R' = R ⧸ (x)` is regular local of embedding dimension `m`: the exchange
  lemma above gives `spanFinrank (𝔪 R') ≤ m`, and Krull's height theorem in the
  form `ringKrullDim_le_ringKrullDim_quotient_add_encard` gives the reverse
  dimension bound `ringKrullDim R ≤ ringKrullDim R' + 1`. Cancelling the `+ 1`
  in `WithBot ℕ∞` is `ENat.WithBot.add_le_add_one_right_iff`.
* By induction `R'` is a domain, i.e. `(x)` is PRIME. Some minimal prime
  `q ≤ (x)`; for `y ∈ q` write `y = c x`, and `x ∉ q` with `q` prime forces
  `c ∈ q`, so `q ≤ (x) · q` and Nakayama gives `q = ⊥`. So `⊥` is prime.

Both halves of Krull's height theorem are already in mathlib
(`Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean`); what was missing was
only this induction, and it is what the `RegularLocalRing/Defs.lean` docstring
records as an open TODO. -/
theorem isDomain_of_isRegularLocalRing_aux (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R],
      (IsLocalRing.maximalIdeal R).spanFinrank = n → IsDomain R := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro R _ _ hn
    match n, hn, ih with
    | 0, hn, _ =>
      have hbot : IsLocalRing.maximalIdeal R = ⊥ :=
        (Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).1 hn
      have hfield : IsField R := IsLocalRing.isField_iff_maximalIdeal_eq.2 hbot
      letI := hfield.toField
      infer_instance
    | (m + 1), hn, ih =>
      have hdim : ringKrullDim R = ((m + 1 : ℕ) : WithBot ℕ∞) := by
        rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R), hn]
      have hm2 : ¬ (IsLocalRing.maximalIdeal R ≤ (IsLocalRing.maximalIdeal R) ^ 2) := by
        intro hle
        have hb : IsLocalRing.maximalIdeal R = ⊥ := by
          refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) _
            (IsNoetherian.noetherian _) ?_ ?_
          · rwa [smul_eq_mul, ← pow_two]
          · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
        rw [hb] at hn
        simp at hn
      have hmp : ∀ p ∈ minimalPrimes R, ¬ (IsLocalRing.maximalIdeal R ≤ p) := by
        intro p hp hle
        haveI := IsMinimalPrime.isPrime hp
        have hpm : p = IsLocalRing.maximalIdeal R :=
          le_antisymm (IsLocalRing.le_maximalIdeal Ideal.IsPrime.ne_top') hle
        have h0 : (IsLocalRing.maximalIdeal R).height = 0 := Ideal.height_eq_zero_iff.2 (hpm ▸ hp)
        rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h0] at hdim
        have hz : ((0 : ℕ) : WithBot ℕ∞) = ((m + 1 : ℕ) : WithBot ℕ∞) := by simpa using hdim
        have h2 : (0 : ℕ) = m + 1 := by exact_mod_cast hz
        omega
      have hfin : (minimalPrimes R).Finite := minimalPrimes.finite_of_isNoetherianRing R
      set s : Finset (Ideal R) := insert ((IsLocalRing.maximalIdeal R) ^ 2) hfin.toFinset with hs
      have hnotsub :
          ¬ ((IsLocalRing.maximalIdeal R : Set R) ⊆ ⋃ i ∈ (↑s : Set (Ideal R)), (i : Set R)) := by
        intro hsub
        obtain ⟨i, his, hle⟩ :=
          (Ideal.subset_union_prime (s := s) (f := fun i => i)
            ((IsLocalRing.maximalIdeal R) ^ 2) ((IsLocalRing.maximalIdeal R) ^ 2)
            (fun i hi _ hne => by
              rw [hs, Finset.mem_insert] at hi
              rcases hi with rfl | hi
              · exact absurd rfl hne
              · exact IsMinimalPrime.isPrime (hfin.mem_toFinset.1 hi))).1 hsub
        rw [hs, Finset.mem_insert] at his
        rcases his with rfl | his
        · exact hm2 hle
        · exact hmp i (hfin.mem_toFinset.1 his) hle
      obtain ⟨x, hxm, hxni⟩ := Set.not_subset.1 hnotsub
      simp only [Set.mem_iUnion, not_exists] at hxni
      have hx2 : x ∉ (IsLocalRing.maximalIdeal R) ^ 2 := fun h =>
        hxni _ (by rw [hs, Finset.coe_insert]; exact Set.mem_insert _ _) h
      have hxmin : ∀ p ∈ minimalPrimes R, x ∉ p := fun p hp h =>
        hxni p (by
          rw [hs, Finset.coe_insert]
          exact Set.mem_insert_of_mem _ (Finset.mem_coe.2 (hfin.mem_toFinset.2 hp))) h
      obtain ⟨T, hTcard, hTspan⟩ :=
        exists_finset_card_span_insert_eq_maximalIdeal hxm hx2 hn
      set I : Ideal R := Ideal.span {x} with hI
      have hIm : I ≤ IsLocalRing.maximalIdeal R := by rw [hI, Ideal.span_le]; simpa using hxm
      have hInt : I ≠ ⊤ := fun h =>
        (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (h ▸ hIm))
      haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hInt
      haveI : IsLocalRing (R ⧸ I) :=
        IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
      have hmapmax : (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk I)
          = IsLocalRing.maximalIdeal (R ⧸ I) :=
        IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
      have hsr : (IsLocalRing.maximalIdeal (R ⧸ I)).spanFinrank ≤ m := by
        have himg : IsLocalRing.maximalIdeal (R ⧸ I)
            = Ideal.span ((Ideal.Quotient.mk I) '' (T : Set R)) := by
          rw [← hmapmax, ← hTspan, Ideal.map_span, Set.image_insert_eq]
          have hx0 : (Ideal.Quotient.mk I) x = 0 := by
            rw [Ideal.Quotient.eq_zero_iff_mem, hI]
            exact Ideal.subset_span rfl
          rw [hx0, Ideal.span_insert_zero]
        rw [himg]
        refine le_trans (Submodule.spanFinrank_span_le_ncard_of_finite
          ((T : Set R).toFinite.image _)) ?_
        exact le_trans (Set.ncard_image_le (T : Set R).toFinite) (by simp [hTcard])
      have hjac : ({x} : Set R) ⊆ Ring.jacobson R := by
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        show y ∈ Ring.jacobson R
        rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
        exact hxm
      have hkey : ringKrullDim R ≤ ringKrullDim (R ⧸ I) + 1 := by
        have h := ringKrullDim_le_ringKrullDim_quotient_add_encard ({x} : Set R) hjac
        simpa [hI] using h
      have hdimq : ((m : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ I) := by
        rw [hdim] at hkey
        push_cast at hkey
        exact ENat.WithBot.add_le_add_one_right_iff.mp hkey
      have hreg : IsRegularLocalRing (R ⧸ I) :=
        IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _
          (le_trans (by exact_mod_cast hsr) hdimq)
      have hsrq : (IsLocalRing.maximalIdeal (R ⧸ I)).spanFinrank = m := by
        refine le_antisymm hsr ?_
        have hfr := hreg.spanFinrank_maximalIdeal
        have h2 : ((m : ℕ) : WithBot ℕ∞)
            ≤ (((IsLocalRing.maximalIdeal (R ⧸ I)).spanFinrank : ℕ) : WithBot ℕ∞) := by
          rw [hfr]; exact hdimq
        exact_mod_cast h2
      haveI : IsDomain (R ⧸ I) := ih m (Nat.lt_succ_self m) (R ⧸ I) hsrq
      haveI hIprime : I.IsPrime := (Ideal.Quotient.isDomain_iff_prime I).1 inferInstance
      obtain ⟨q, hq, hqI⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := I) bot_le
      haveI hqp : q.IsPrime := IsMinimalPrime.isPrime hq
      have hxq : x ∉ q := hxmin q hq
      have hqq : q ≤ I • q := by
        intro y hy
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (hqI hy)
        have hcq : c ∈ q := by
          rcases hqp.mem_or_mem (show c * x ∈ q from hc ▸ hy) with h | h
          · exact h
          · exact absurd h hxq
        rw [← hc, smul_eq_mul, mul_comm]
        exact Ideal.mul_mem_mul hcq (Ideal.subset_span rfl)
      have hqbot : q = ⊥ := by
        refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I q
          (IsNoetherian.noetherian _) hqq ?_
        rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
        exact hIm
      have hbp : (⊥ : Ideal R).IsPrime := hqbot ▸ hqp
      haveI : NoZeroDivisors R := ⟨fun {a b} h => by
        have hm := hbp.mem_or_mem (show a * b ∈ (⊥ : Ideal R) by simpa using h)
        simpa using hm⟩
      exact NoZeroDivisors.to_isDomain R

/-- **REGULAR LOCAL RINGS ARE INTEGRAL DOMAINS** (**PROVEN 2026-07-26**).

This is the second of the two mathlib gaps named in the docstring of
`isDomain_stalk_of_smooth_over_field`, and it is no longer a gap: mathlib's
`Mathlib/RingTheory/RegularLocalRing/Defs.lean` records only
`IsRegularLocalRing`/`IsRegularRing` with a handful of instances, and its own
"TODO" is precisely this direction. The proof is
`isDomain_of_isRegularLocalRing_aux` instantiated at `n = spanFinrank 𝔪`.

Note the route taken is NOT the associated-graded one the earlier docstring
sketched — no `gr_𝔪(R)`, no filtered ring, no Krull intersection theorem. The
induction above uses only Nakayama, prime avoidance over the finitely many
minimal primes of a noetherian ring, and Krull's height theorem, all of which
mathlib already had. This is general, reusable, and a genuine mathlib
contribution. -/
theorem isDomain_of_isRegularLocalRing (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    IsDomain R :=
  isDomain_of_isRegularLocalRing_aux _ R rfl

end GaloisRepresentation.Modularity
