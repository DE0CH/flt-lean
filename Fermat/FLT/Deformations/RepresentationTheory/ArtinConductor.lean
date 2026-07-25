/-
Modularity/ArtinConductor.lean — own work for the Fermat project (not
vendored from the FLT project).
-/
module

public import Fermat.FLT.Deformations.RepresentationTheory.GaloisRep

/-!
# The Artin conductor exponent of a Galois representation

This module builds the local invariant that the three per-place
"level-lowering" citations of `Fermat/FLT/Modularity/Interface.lean` were
all spelling by hand, each in its own local dialect: the **Artin
conductor exponent** `a_v(V)` of a Galois representation at a finite
place `v`, through the classical dictionary (Serre, *Local Fields*,
VI §2)

  `a_v(V) = (dim V − dim V^{I_v}) + Sw_v(V)`,

the *tame* part read off the inertia invariants and the *wild* part the
Swan conductor.

## What is proven here and what is postponed

The **tame** part is built outright: `GaloisRep.inertiaInvariants` is the
honest `I_v`-fixed submodule (`localInertiaGroup v` acting through
`ρ.toLocal v`), and `GaloisRep.tameExponent` is its codimension, with the
two facts the consumers need proven — it vanishes for an unramified
representation (`GaloisRep.tameExponent_eq_zero_of_isUnramifiedAt`) and
it drops by at least one as soon as inertia fixes a nonzero vector
(`GaloisRep.tameExponent_add_one_le_finrank_of_fixed`).

The **wild** part is *not* definable on this pin, and this is a hard
absence rather than an oversight:

* mathlib has the decomposition and inertia subgroups of a valuation
  subring (`ValuationSubring.decompositionSubgroup`,
  `ValuationSubring.inertiaSubgroup`, i.e. `G_{-1}` and `G_0`) and an
  explicit `TODO: Define higher ramification groups in lower numbering`
  in `Mathlib/RingTheory/Valuation/RamificationGroup.lean`. There is no
  `Swan`, no `ramificationGroup`, no Artin conductor anywhere in the
  library (the `conductor`s it does have are the ring-theoretic
  conductor of a ring extension and the conductor of a Dirichlet
  character — unrelated invariants).
* the naive repair is unavailable *in principle*: over `Kᵥᵃˡᵍ` the
  lower numbering collapses. The value group of the integral closure of
  `𝒪ᵥ` in `Kᵥᵃˡᵍ` is divisible, so `𝔪 ^ (i + 1) = 𝔪` and every
  `AddSubgroup.inertia (𝔪 ^ (i+1))` equals `localInertiaGroup v`
  itself. The Swan conductor genuinely needs the *upper* numbering,
  i.e. Herbrand's function `ψ` and the finite-level ramification
  filtration — a development of its own.

So the wild part enters as an **explicit input**, and it enters
*soundly*: rather than an opaque `swanExponent` function (about which
any equation would be an unprovable, possibly false, assertion), the
conductor exponent is packaged as the RELATION

  `GaloisRep.HasConductorExponentAt ρ v a  ↔  ∃ s, a = tameExponent + s ∧ …`

with the wild summand `s` existentially quantified and constrained by
the properties of the Swan conductor that are available without the
filtration (currently: it vanishes when inertia acts trivially). Every
statement of the form `HasConductorExponentAt ρ v a` is therefore
*implied* by the true conductor-exponent identity `a_v(V) = a`, so a
sorried leaf asserting it is a genuine (if weaker) consequence of the
cited literature and can never be a false statement about an
under-determined constant.

## Consumers

`Fermat/FLT/Modularity/Interface.lean` states ONE shared Carayol leaf
`hasConductorExponentAt_factorization_of_isNewAtPrime` in these terms
and derives from it the per-place citations that previously each carried
their own copy of Carayol's theorem.
-/

@[expose] public section

open NumberField IsDedekindDomain

universe uK

variable {K : Type uK} [Field K] [NumberField K]
variable {A : Type*} [CommRing A] [TopologicalSpace A]
variable {M : Type*} [AddCommGroup M] [Module A M]

namespace GaloisRep

/-- **The inertia invariants of a Galois representation at a finite
place** `V^{I_v}`: the submodule of vectors fixed by every element of
`localInertiaGroup v` acting through the localization `ρ.toLocal v`.
This is the carrier of the TAME part of the Artin conductor exponent. -/
def inertiaInvariants (ρ : GaloisRep K A M) (v : HeightOneSpectrum (𝓞 K)) :
    Submodule A M where
  carrier := {x | ∀ σ ∈ localInertiaGroup v, ρ.toLocal v σ x = x}
  add_mem' {x y} hx hy := by
    intro σ hσ
    show ρ.toLocal v σ (x + y) = x + y
    rw [map_add, hx σ hσ, hy σ hσ]
  zero_mem' := by
    intro σ _
    show ρ.toLocal v σ 0 = 0
    rw [map_zero]
  smul_mem' c x hx := by
    intro σ hσ
    show ρ.toLocal v σ (c • x) = c • x
    rw [map_smul, hx σ hσ]

@[simp]
lemma mem_inertiaInvariants {ρ : GaloisRep K A M} {v : HeightOneSpectrum (𝓞 K)}
    {x : M} :
    x ∈ ρ.inertiaInvariants v ↔
      ∀ σ ∈ localInertiaGroup v, ρ.toLocal v σ x = x :=
  Iff.rfl

/-- **The tame part of the Artin conductor exponent** at `v`:
`dim V − dim V^{I_v}`, the codimension of the inertia invariants. For a
2-dimensional representation this is the `2 − dim V^{I_v}` of the
classical dictionary `a_v = (2 − dim V^{I_v}) + Sw_v`. -/
noncomputable def tameExponent (ρ : GaloisRep K A M)
    (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  Module.finrank A M - Module.finrank A (ρ.inertiaInvariants v)

/-- An unramified representation has all of `V` as inertia invariants. -/
lemma inertiaInvariants_eq_top_of_isUnramifiedAt (ρ : GaloisRep K A M)
    (v : HeightOneSpectrum (𝓞 K)) [ρ.IsUnramifiedAt v] :
    ρ.inertiaInvariants v = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  intro σ hσ
  have h1 : (ρ.toLocal v) σ = 1 :=
    GaloisRep.IsUnramifiedAt.localInertiaGroup_le (ρ := ρ) hσ
  rw [h1]
  rfl

/-- **The tame part of the conductor exponent vanishes for an unramified
representation** — the tame half of "`a_v = 0` for `ρ` unramified at
`v`". -/
lemma tameExponent_eq_zero_of_isUnramifiedAt (ρ : GaloisRep K A M)
    (v : HeightOneSpectrum (𝓞 K)) [ρ.IsUnramifiedAt v] :
    ρ.tameExponent v = 0 := by
  have h : Module.finrank A (ρ.inertiaInvariants v) = Module.finrank A M := by
    rw [ρ.inertiaInvariants_eq_top_of_isUnramifiedAt v]
    exact Submodule.topEquiv.finrank_eq
  rw [tameExponent, h, Nat.sub_self]

/-- **A nonzero inertia-fixed vector lowers the tame exponent** — the
tame half of the at-`2` exponent bound `a_2 ≤ 1`: over a field, an
inertia-fixed `w₀ ≠ 0` makes `dim V^{I_v} ≥ 1`, hence
`tameExponent + 1 ≤ dim V`. -/
lemma tameExponent_add_one_le_finrank_of_fixed {k : Type*} [Field k]
    [TopologicalSpace k] {W : Type*} [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] (ρ : GaloisRep K k W)
    (v : HeightOneSpectrum (𝓞 K)) {w₀ : W} (hw₀ : w₀ ≠ 0)
    (hfix : ∀ σ ∈ localInertiaGroup v, ρ.toLocal v σ w₀ = w₀) :
    ρ.tameExponent v + 1 ≤ Module.finrank k W := by
  have hmem : w₀ ∈ ρ.inertiaInvariants v := hfix
  have hne : (ρ.inertiaInvariants v) ≠ ⊥ := fun h => hw₀ (by
    rw [h] at hmem; exact hmem)
  have hpos : 1 ≤ Module.finrank k (ρ.inertiaInvariants v) :=
    Submodule.one_le_finrank_iff.mpr hne
  have hle : Module.finrank k (ρ.inertiaInvariants v) ≤ Module.finrank k W :=
    Submodule.finrank_le _
  have hW : 1 ≤ Module.finrank k W := hpos.trans hle
  have hsub : Module.finrank k W - Module.finrank k (ρ.inertiaInvariants v)
      ≤ Module.finrank k W - 1 := Nat.sub_le_sub_left hpos _
  rw [tameExponent]
  calc Module.finrank k W - Module.finrank k (ρ.inertiaInvariants v) + 1
      ≤ (Module.finrank k W - 1) + 1 := Nat.add_le_add_right hsub 1
    _ = Module.finrank k W := Nat.sub_add_cancel hW

/-- **The Artin conductor exponent at a finite place**, as a relation
between the representation and a natural number:
`ρ.HasConductorExponentAt v a` says that `a` decomposes according to the
classical dictionary

  `a_v(V) = (dim V − dim V^{I_v}) + Sw_v(V)`

as the TAME part `ρ.tameExponent v` — computed here — plus a WILD
summand `s` playing the role of the Swan conductor `Sw_v(V)`, subject to
the Swan-conductor properties that are available on this pin, namely:

* `s = 0` when `ρ` is unramified at `v` (the Swan conductor is supported
  on the wild inertia, which is trivial for an unramified
  representation).

The wild summand is EXISTENTIALLY quantified rather than computed
because the Swan conductor is not definable here: the higher
ramification filtration in the upper numbering is absent from mathlib
and, as explained in the module docstring, cannot be replaced by the
lower numbering over `Kᵥᵃˡᵍ` (whose value group is divisible, collapsing
every lower ramification group onto `localInertiaGroup v`).

Soundness of this packaging: the true conductor exponent `a_v(V)`
satisfies `HasConductorExponentAt ρ v (a_v(V))` — take `s := Sw_v(V)`,
which does vanish for an unramified `ρ` — so a cited identity
`a_v(V) = a` always yields `HasConductorExponentAt ρ v a`. In other
words this relation is a WEAKENING of the conductor-exponent identity,
never an assertion about an under-determined constant: sorried leaves
stated with it are consequences of the literature, not conjectures about
an opaque symbol. -/
def HasConductorExponentAt (ρ : GaloisRep K A M)
    (v : HeightOneSpectrum (𝓞 K)) (a : ℕ) : Prop :=
  ∃ s : ℕ, a = ρ.tameExponent v + s ∧ (ρ.IsUnramifiedAt v → s = 0)

/-- The tame part is a lower bound for the conductor exponent (the Swan
conductor is nonnegative). -/
lemma HasConductorExponentAt.tameExponent_le {ρ : GaloisRep K A M}
    {v : HeightOneSpectrum (𝓞 K)} {a : ℕ} (h : ρ.HasConductorExponentAt v a) :
    ρ.tameExponent v ≤ a := by
  obtain ⟨s, hs, -⟩ := h
  omega

/-- **The conductor exponent vanishes at a place of unramifiedness** —
the full `a_v = 0` statement, tame part by
`tameExponent_eq_zero_of_isUnramifiedAt` and wild part by the Swan
clause of `HasConductorExponentAt`. This is the shape in which the
away-from-`p` per-place citation consumes the shared conductor leaf. -/
lemma HasConductorExponentAt.eq_zero_of_isUnramifiedAt {ρ : GaloisRep K A M}
    {v : HeightOneSpectrum (𝓞 K)} {a : ℕ} (h : ρ.HasConductorExponentAt v a)
    [ρ.IsUnramifiedAt v] : a = 0 := by
  obtain ⟨s, hs, hs0⟩ := h
  rw [hs, ρ.tameExponent_eq_zero_of_isUnramifiedAt v, hs0 ‹_›]

end GaloisRep
