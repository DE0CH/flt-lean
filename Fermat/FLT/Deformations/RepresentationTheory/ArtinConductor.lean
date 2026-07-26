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

So the wild part enters as an **uninterpreted constant**
`GaloisRep.swanExponentAux`, declared with Lean's `opaque` command, and
the conductor exponent is the honest sum

  `GaloisRep.conductorExponent ρ v = ρ.tameExponent v + ρ.swanExponent v`,

with `HasConductorExponentAt ρ v a` the *equation* `a = conductorExponent ρ v`.

`opaque` introduces **no axiom and no `sorry`** (`#print axioms` on
anything using it stays empty) and the kernel will not unfold it, so
nothing about its value is provable — which is exactly the intent: the
symbol *denotes* the Swan conductor without computing it. The one
property of the Swan conductor that this development actually needs,
vanishing at an unramified place, is built into `swanExponent` by
construction (`swanExponent ρ v = if ρ.IsUnramifiedAt v then 0 else
swanExponentAux ρ v`), so
`GaloisRep.swanExponent_eq_zero_of_isUnramifiedAt` is a *theorem* rather
than a further leaf.

Soundness of this packaging is model-theoretic and is the standard one
for axiomatising an invariant that cannot yet be defined: interpret
`swanExponentAux ρ v` as the true Swan conductor `Sw_v(V)`. Under that
interpretation `conductorExponent ρ v` **is** `a_v(V)`, so every leaf
stated with `HasConductorExponentAt` is precisely the corresponding
statement of the literature — no weaker and no stronger.

## HISTORY: why the previous, existential packaging was WITHDRAWN

Until 2026-07-25 this file packaged the wild summand *existentially*,

  `HasConductorExponentAt ρ v a  :=  ∃ s, a = tameExponent + s ∧
                                     (ρ.IsUnramifiedAt v → s = 0)`,

on the argument that every such statement is *implied* by the true
identity `a_v(V) = a`, hence can never be false.

**That argument is valid only in CONCLUSION position.** The predicate is
UPWARD CLOSED in `a` for a representation that is ramified at `v` (take
`s := a − tameExponent`; the only clause constraining `s` is conditioned
on unramifiedness and is then vacuous). So in HYPOTHESIS position the
weakening *strengthens* the statement, and a leaf consuming
`HasConductorExponentAt ρ v a` in order to derive an UPPER bound on `a`
is thereby asserting `ρ` is unramified at `v`. Exactly one leaf did
this — `hasConductorExponentAt_two_le_one_of_inertia_sq_eq_zero` in
`Fermat/FLT/Modularity/Interface.lean` — and it was consequently FALSE
AS STATED, refuted by the curve `E/ℚ` of conductor `14` at `p = 5` (see
that leaf's docstring for the counterexample in full).

The generalizable rule: an existentially weakened invariant can carry
LOWER-bound content (`a ≠ 0 → ρ` ramified) but never UPPER-bound
content. Pinning `a` to a single opaque value, as is now done, restores
both directions at the cost of an uninterpreted symbol — which is the
right trade, since the alternative is a definition under which half the
intended consumers are unstatable.

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

/-- **The tame exponent never exceeds the dimension.** It is the
codimension of a submodule, so `dim V − dim V^{I_v} ≤ dim V` holds
unconditionally (indeed by `Nat` truncated subtraction alone).

This trivial bound is the arithmetic that decides how much content a
CITED conductor bound actually carries: since the tame part is all that
`HasConductorExponentAt ρ v a` constrains at a ramified place
(`hasConductorExponentAt_iff_tameExponent_le_of_not_isUnramifiedAt`), a
citation `a_v(V) = a` with `a ≥ dim V` contributes NOTHING beyond
ramifiedness. For the 2-dimensional representations of the
level-lowering assemblies that means: a cited conductor exponent `≥ 2`
is exactly the assertion "`ρ` is ramified at `v`", and only the
`a = 1` case carries tame information. -/
lemma tameExponent_le_finrank (ρ : GaloisRep K A M)
    (v : HeightOneSpectrum (𝓞 K)) :
    ρ.tameExponent v ≤ Module.finrank A M :=
  Nat.sub_le _ _

/-- **The Swan conductor, as an UNINTERPRETED constant.**

`swanExponentAux ρ v` stands for `Sw_v(V)`, the wild part of the Artin
conductor exponent. It is declared `opaque`: the kernel will not unfold
it, so **nothing about its value is provable**, and — unlike an
`axiom` — it contributes nothing to `#print axioms` (the `:= 0` is only
the inhabitation witness Lean's `opaque` command requires; `= 0` is NOT
derivable from it).

This is deliberate, and it is the only honest option at this pin: the
Swan conductor needs the higher ramification filtration in the UPPER
numbering, which mathlib does not have and which the lower numbering
cannot substitute for over `Kᵥᵃˡᵍ` (divisible value group — see the
module docstring). Rather than pretend to define it, or existentially
quantify it away (which cost this development a FALSE leaf — again see
the module docstring), we name it and say nothing about it.

Do not state or prove any equation about `swanExponentAux` itself.
Facts about the Swan conductor belong on `swanExponent` below, and any
such fact that is not a theorem is a citation leaf whose soundness is
checked against the intended interpretation `swanExponentAux ρ v :=
Sw_v(V)`. -/
opaque swanExponentAux {K : Type uK} [Field K] [NumberField K]
    {A : Type*} [CommRing A] [TopologicalSpace A]
    {M : Type*} [AddCommGroup M] [Module A M]
    (ρ : GaloisRep K A M) (v : HeightOneSpectrum (𝓞 K)) : ℕ := 0

open scoped Classical in
/-- **The wild part of the Artin conductor exponent** at `v`, i.e. the
Swan conductor `Sw_v(V)`.

It is `swanExponentAux` — an opaque constant — with the ONE property
this development needs BUILT IN rather than assumed: the Swan conductor
is supported on the wild inertia, so it vanishes when `ρ` is unramified
at `v`. Baking that case in keeps
`swanExponent_eq_zero_of_isUnramifiedAt` a *theorem*; it is a
conservative move, since the true Swan conductor does vanish there, so
the intended interpretation `swanExponentAux := Sw_v` still makes
`swanExponent = Sw_v` on the nose. -/
noncomputable def swanExponent (ρ : GaloisRep K A M)
    (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  if ρ.IsUnramifiedAt v then 0 else ρ.swanExponentAux v

/-- **The Swan conductor vanishes at a place of unramifiedness** — true
by construction of `swanExponent`, see its docstring. -/
lemma swanExponent_eq_zero_of_isUnramifiedAt (ρ : GaloisRep K A M)
    (v : HeightOneSpectrum (𝓞 K)) [ρ.IsUnramifiedAt v] :
    ρ.swanExponent v = 0 := by
  classical
  rw [swanExponent, if_pos ‹_›]

/-- **The Artin conductor exponent at a finite place**, through the
classical dictionary (Serre, *Local Fields* VI §2)

  `a_v(V) = (dim V − dim V^{I_v}) + Sw_v(V)`:

the TAME part `ρ.tameExponent v`, computed here from the inertia
invariants, plus the WILD part `ρ.swanExponent v`, an opaque constant.

Because the wild summand is a FUNCTION of `(ρ, v)` rather than an
existentially quantified witness, this number is PINNED — which is what
lets consumers read UPPER bounds off it. See the module docstring for
why the previous existential packaging had to be withdrawn. -/
noncomputable def conductorExponent (ρ : GaloisRep K A M)
    (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  ρ.tameExponent v + ρ.swanExponent v

/-- **The Artin conductor exponent at a finite place**, as a relation
between the representation and a natural number: `a` IS the conductor
exponent `ρ.conductorExponent v`.

This is the shape in which the literature citations of
`Fermat/FLT/Modularity/Interface.lean` are stated — Carayol's
`ord_q(cond ρ) = ord_q M` reads
`ρ.HasConductorExponentAt v_q (M.factorization q)` — and it is an
EQUATION, not a weakening: a leaf stated with it asserts exactly the
cited identity, under the interpretation of `swanExponentAux` as the
Swan conductor. -/
def HasConductorExponentAt (ρ : GaloisRep K A M)
    (v : HeightOneSpectrum (𝓞 K)) (a : ℕ) : Prop :=
  a = ρ.conductorExponent v

/-- The defining equation, in usable form. -/
lemma HasConductorExponentAt.eq {ρ : GaloisRep K A M}
    {v : HeightOneSpectrum (𝓞 K)} {a : ℕ} (h : ρ.HasConductorExponentAt v a) :
    a = ρ.conductorExponent v := h

/-- The tame part is a lower bound for the conductor exponent (the Swan
conductor is nonnegative). -/
lemma HasConductorExponentAt.tameExponent_le {ρ : GaloisRep K A M}
    {v : HeightOneSpectrum (𝓞 K)} {a : ℕ} (h : ρ.HasConductorExponentAt v a) :
    ρ.tameExponent v ≤ a := by
  rw [h.eq, conductorExponent]
  omega

/-- **An upper bound on the conductor exponent transfers to any `a`
carrying it.** This is the direction the at-`2` level-lowering consumer
needs, and the direction the previous existential packaging could not
supply. -/
lemma HasConductorExponentAt.le_of_conductorExponent_le {ρ : GaloisRep K A M}
    {v : HeightOneSpectrum (𝓞 K)} {a n : ℕ} (h : ρ.HasConductorExponentAt v a)
    (hn : ρ.conductorExponent v ≤ n) : a ≤ n := by
  rw [h.eq]; exact hn

/-- **The conductor exponent vanishes at a place of unramifiedness** —
the full `a_v = 0` statement, tame part by
`tameExponent_eq_zero_of_isUnramifiedAt` and wild part by
`swanExponent_eq_zero_of_isUnramifiedAt`. This is the shape in which the
away-from-`p` per-place citation consumes the shared conductor leaf. -/
lemma HasConductorExponentAt.eq_zero_of_isUnramifiedAt {ρ : GaloisRep K A M}
    {v : HeightOneSpectrum (𝓞 K)} {a : ℕ} (h : ρ.HasConductorExponentAt v a)
    [ρ.IsUnramifiedAt v] : a = 0 := by
  rw [h.eq, conductorExponent, ρ.tameExponent_eq_zero_of_isUnramifiedAt v,
    ρ.swanExponent_eq_zero_of_isUnramifiedAt v]

/-- **A positive conductor exponent forces ramification** — the
contrapositive of `HasConductorExponentAt.eq_zero_of_isUnramifiedAt`,
in the form the level-lowering assemblies consume it: if some conductor
exponent of `ρ` at `v` is nonzero then `ρ` is ramified at `v`. -/
lemma HasConductorExponentAt.not_isUnramifiedAt_of_ne_zero
    {ρ : GaloisRep K A M} {v : HeightOneSpectrum (𝓞 K)} {a : ℕ}
    (h : ρ.HasConductorExponentAt v a) (ha : a ≠ 0) :
    ¬ ρ.IsUnramifiedAt v := by
  intro hun
  haveI : ρ.IsUnramifiedAt v := hun
  exact ha h.eq_zero_of_isUnramifiedAt

/-! ### WITHDRAWN 2026-07-26: the four lemmas about the EXISTENTIAL packaging

Until 2026-07-26 `HasConductorExponentAt` was the existential weakening
`∃ s, a = tameExponent + s ∧ (IsUnramifiedAt → s = 0)`, and this file
carried four lemmas exploiting it:
`hasConductorExponentAt_iff_tameExponent_le_of_not_isUnramifiedAt`,
`hasConductorExponentAt_of_finrank_le_of_not_isUnramifiedAt`,
`hasConductorExponentAt_of_fixed_of_not_isUnramifiedAt` and
`HasConductorExponentAt.mono_of_not_isUnramifiedAt`.

All four are FALSE under the pinned definition above, and that is the
point of the pin. The weakening is UPWARD CLOSED in `a` at a ramified
place, so those lemmas let a Carayol-type conductor identity be
"proved" from ramifiedness alone — which is what
`hasConductorExponentAt_two_le_one_of_inertia_sq_eq_zero` was refuted
for (counterexample: `E/ℚ` of conductor `14` at `p = 5`; inertia at `2`
acts through the Tate parametrisation by square-zero unipotents, `τ` is
ramified at `2` since `5 ∤ v₂(q_E) = 6`, so the weak relation holds at
`a = 2` while the asserted `2 ≤ 1` fails).

An existentially weakened invariant carries LOWER-bound content only.
Do not reintroduce these lemmas; upper bounds now transfer through
`HasConductorExponentAt.le_of_conductorExponent_le`. -/

end GaloisRep
