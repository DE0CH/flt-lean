/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Fermat.FLT.Mathlib.AlgebraicGeometry.EllipticCurve.SexticTwist
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Normal.Closure

/-!
# The Galois action on automorphisms of a base-changed elliptic curve

Infrastructure for the descent cocycle of `Fermat/FLT/ModularCurve/X0.lean`: if `E` is
defined over `K` and `C` is an automorphism of `E⁄Ω`, then its Galois conjugate `C.map σ`
is again an automorphism of `E⁄Ω`, and conjugation intertwines the two actions on points.

This is the piece that turns "for each `σ` there is an automorphism `C_σ` making `⟨g⟩`
stable" into an honest `1`-cocycle: the cocycle identity `c(στ) = c(σ)·σ(c(τ))` is exactly
the statement that `C_σ` composed with the `σ`-conjugate of `C_τ` works for `στ`, and the
Galois twisting in it comes from `map_autMap` below.

Contrast `Affine.Point.equivVariableChangeBaseChange_galois`, which is the special case of a
variable change whose coefficients lie in the BASE field `K` and is therefore fixed by `σ`;
here the coefficients genuinely move.

## Main statements

* `WeierstrassCurve.baseChange_map_algEquiv` : `(E⁄Ω).map σ = E⁄Ω` for `σ` a `K`-automorphism.
* `WeierstrassCurve.smul_map_of_smul_baseChange` : the Galois conjugate of an automorphism of
  `E⁄Ω` is an automorphism of `E⁄Ω`.
* `WeierstrassCurve.Affine.Point.map_autMap` : `σ(C·P) = (σC)·(σP)`.
* `WeierstrassCurve.Affine.Point.coordSet` : the (at most two) coordinates of an affine point,
  as a set — the handle by which a finite set of points pins down a finite subextension.
* `WeierstrassCurve.sq_u_eq_sq_u_of_autStable` : the `A = μ₂` step.  **PROVEN 2026-07-30**;
  was the first of the two sorry leaves of the `j = 0` descent cocycle.
* `WeierstrassCurve.exists_finiteGaloisLevel_of_addOrder` : the finite Galois level.
  **REFUTED AS STATED, RESTATED with `[Normal K Ω]` and PROVEN, 2026-07-30** — the witness is
  `ℚ(y)` with `y⁴ = -32`, and it is written out in that declaration's falsity audit.  This
  file therefore has NO remaining `sorry`.
-/

@[expose] public section

namespace WeierstrassCurve

open scoped WeierstrassCurve.Affine

open Affine.Point

namespace Affine.Point

/-- **The coordinates of an affine point, as a set** — empty at the point at infinity and
`{x, y}` at `some x y h`.

This is the bridge from "finitely many points" to "one finite subextension": a set of points
whose `coordSet`s are all contained in a subfield `M` is acted on by `Gal` through `M`, which
is exactly what `exists_finiteGaloisLevel_of_addOrder` needs. -/
def coordSet {F : Type*} [Field F] {W : WeierstrassCurve F} :
    W.toAffine.Point → Set F
  | .zero => ∅
  | .some x y _ => {x, y}

lemma finite_coordSet {F : Type*} [Field F] {W : WeierstrassCurve F}
    (P : W.toAffine.Point) : (coordSet P).Finite := by
  cases P <;> simp [coordSet]

end Affine.Point

section GaloisConj

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω] [DecidableEq Ω]

/-- Base change of an elliptic curve is elliptic; `local` because it would otherwise fire in
every statement mentioning a base-changed curve. -/
local instance isEllipticBaseChangeAut {E : WeierstrassCurve K} [E.IsElliptic] :
    (E⁄Ω).IsElliptic :=
  inferInstanceAs (E.map (algebraMap K Ω)).IsElliptic

omit [DecidableEq Ω] in
/-- A `K`-automorphism of `Ω` fixes a curve that is defined over `K`. -/
lemma baseChange_map_algEquiv (E : WeierstrassCurve K) (σ : Ω ≃ₐ[K] Ω) :
    (E⁄Ω).map (σ.toAlgHom : Ω →ₐ[K] Ω).toRingHom = E⁄Ω := by
  ext <;>
    simp only [baseChange, map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] <;>
    exact σ.toAlgHom.commutes _

omit [DecidableEq Ω] in
/-- **The Galois conjugate of an automorphism is an automorphism.**  `σ` fixes `E⁄Ω`
because `E` is defined over `K`, so conjugating the equation `C • (E⁄Ω) = (E⁄Ω)` by `σ`
gives the same equation for `C.map σ`. -/
lemma smul_map_of_smul_baseChange (E : WeierstrassCurve K) (σ : Ω ≃ₐ[K] Ω)
    {C : VariableChange Ω} (h : C • (E⁄Ω) = (E⁄Ω)) :
    (C.map (σ.toAlgHom : Ω →ₐ[K] Ω).toRingHom) • (E⁄Ω) = (E⁄Ω) := by
  have hE := baseChange_map_algEquiv E σ
  calc (C.map (σ.toAlgHom : Ω →ₐ[K] Ω).toRingHom) • (E⁄Ω)
      = (C.map (σ.toAlgHom : Ω →ₐ[K] Ω).toRingHom) •
          ((E⁄Ω).map (σ.toAlgHom : Ω →ₐ[K] Ω).toRingHom) := by rw [hE]
    _ = (C • (E⁄Ω)).map (σ.toAlgHom : Ω →ₐ[K] Ω).toRingHom :=
        map_variableChange (C := C) (W := E⁄Ω)
          (φ := (σ.toAlgHom : Ω →ₐ[K] Ω).toRingHom)
    _ = (E⁄Ω).map (σ.toAlgHom : Ω →ₐ[K] Ω).toRingHom := by rw [h]
    _ = E⁄Ω := hE

namespace Affine.Point

section Mul

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F}

/-- **The composition law for `autMap`.**  `autMap` is an ANTI-homomorphism in its variable
change: `mapVariableChange W C` goes from `(C • W).Point` to `W.Point`, so composing the
transports for `C` and `D` realises `C * D` in the order `D` after `C`.

This is the identity `M_W(C * D) = M_W(D) ∘ M_{D•W}(C)` of
`Affine.Point.equivVariableChange_autMap`, specialised to the case where both `C` and `D`
are automorphisms and the intermediate curve `D • W` is `W` itself. -/
lemma autMap_mul [W.IsElliptic] {C D : VariableChange F} (hC : C • W = W) (hD : D • W = W)
    (hCD : (C * D) • W = W) (P : W.toAffine.Point) :
    autMap hCD P = autMap hD (autMap hC P) := by
  have hu0 : (C.u : F) ≠ 0 := C.u.ne_zero
  have hu0' : (D.u : F) ≠ 0 := D.u.ne_zero
  rcases P with _ | ⟨x, y, hns⟩
  · show autMap hCD 0 = autMap hD (autMap hC 0)
    simp only [_root_.map_zero]
  · simp only [autMap_apply, equivOfEq_some, mapVariableChangeFun_some]
    refine some_eq_some W ?_ ?_ <;>
      simp only [VariableChange.mul_def, Units.val_mul] <;>
      field_simp <;> ring

/-- **Transport of `autMap` along an equality of variable changes.**  The variable change
enters `autMap h` only through the TYPE of `h`, so once the two variable changes are
identified the two proofs are interchangeable by proof irrelevance. -/
lemma autMap_congr [W.IsElliptic] {C C' : VariableChange F} (hCC : C = C')
    (h : C • W = W) (h' : C' • W = W) (P : W.toAffine.Point) :
    autMap h P = autMap h' P := by
  subst hCC; rfl

/-- **An automorphism acts injectively on points.**  `autMap h` is the composite of the
transport `equivOfEq h.symm` — an `AddEquiv` — with `mapVariableChange W C`, whose underlying
function is injective (`mapVariableChangeFun_injective`, from `u ≠ 0`).

This is what upgrades "`autMap h` maps `⟨g⟩` INTO `⟨g⟩`" to "ONTO", once `⟨g⟩` is known
finite: an injective self-map of a finite type is surjective.  Definitionally the same
statement as `autPoint_injective` in `Fermat/FLT/ModularCurve/X0.lean`, which is DOWNSTREAM
of this file and therefore unusable here. -/
lemma autMap_injective [W.IsElliptic] {C : VariableChange F} (h : C • W = W) :
    Function.Injective (autMap h) := by
  intro P Q hPQ
  have hEq : equivOfEq h.symm P = equivOfEq h.symm Q :=
    mapVariableChangeFun_injective W C hPQ
  simpa using hEq

/-- **`negVariableChange` acts as negation.**  `negVariableChange W = ⟨-1, 0, -a₁, -a₃⟩` sends
`(x, y)` to `(x, -y - a₁x - a₃) = (x, negY x y)`, which is `-P`; uniform in `j`.  Companion of
`autPoint_negVariableChange` in `X0.lean`, restated here because that file is downstream.

Its purpose is that an `AddSubgroup` is closed under negation, so `negVariableChange` is
automatically a member of the stabiliser `A` of any `⟨g⟩` — which is exactly the `μ₂ ⊆ A`
half of `sq_u_eq_sq_u_of_autStable`. -/
lemma autMap_negVariableChange [W.IsElliptic] (h : W.negVariableChange • W = W)
    (P : W.toAffine.Point) : autMap h P = -P := by
  rcases P with _ | ⟨x, y, hns⟩
  · exact (_root_.map_zero (autMap h)).trans neg_zero.symm
  · show mapVariableChangeFun W W.negVariableChange (equivOfEq h.symm _) = _
    rw [equivOfEq_some, mapVariableChangeFun_some, neg_some]
    refine some_eq_some W ?_ ?_ <;> simp [WeierstrassCurve.negVariableChange, Affine.negY]
    ring

end Mul

/-- **The Galois action on points intertwines an automorphism with its conjugate**:
`σ(C·P) = (σC)·(σP)`.

This is the general form of `equivVariableChangeBaseChange_galois`, whose variable change has
coefficients in `K` and is therefore fixed; here `σ` genuinely moves `u, r, s, t`, and the
displacement is exactly what makes the descent datum a `1`-cocycle rather than a
homomorphism. -/
lemma map_autMap (E : WeierstrassCurve K) [E.IsElliptic] (σ : Ω ≃ₐ[K] Ω)
    {C : VariableChange Ω} (h : C • (E⁄Ω) = (E⁄Ω))
    (h' : (C.map (σ.toAlgHom : Ω →ₐ[K] Ω).toRingHom) • (E⁄Ω) = (E⁄Ω))
    (P : (E⁄Ω).toAffine.Point) :
    WeierstrassCurve.Affine.Point.map (σ.toAlgHom : Ω →ₐ[K] Ω) (autMap h P)
      = autMap h' (WeierstrassCurve.Affine.Point.map (σ.toAlgHom : Ω →ₐ[K] Ω) P) := by
  rcases P with _ | ⟨x, y, hns⟩
  · show WeierstrassCurve.Affine.Point.map (σ.toAlgHom : Ω →ₐ[K] Ω) (autMap h 0)
      = autMap h' (WeierstrassCurve.Affine.Point.map (σ.toAlgHom : Ω →ₐ[K] Ω) 0)
    simp only [_root_.map_zero]
  · rw [autMap_apply, equivOfEq_some, mapVariableChangeFun_some,
      WeierstrassCurve.Affine.Point.map_some, WeierstrassCurve.Affine.Point.map_some,
      autMap_apply, equivOfEq_some, mapVariableChangeFun_some]
    refine some_eq_some (E⁄Ω) ?_ ?_ <;>
      simp only [VariableChange.map_u, VariableChange.map_r, VariableChange.map_s,
        VariableChange.map_t, Units.coe_map, MonoidHom.coe_coe,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add, map_mul, map_pow]

end Affine.Point

/-- **Two automorphisms agreeing on a point's coordinates agree on the point.**  The
converse direction of `coordSet` being the right handle: the whole Galois-theoretic content
of `exists_finiteGaloisLevel_of_addOrder` is that finitely many points have finitely many
coordinates, and this is what turns agreement on coordinates back into agreement on points. -/
lemma map_eq_map_of_eqOn_coordSet (E : WeierstrassCurve K) (σ τ : Ω ≃ₐ[K] Ω)
    (P : (E⁄Ω).toAffine.Point)
    (h : ∀ a ∈ Affine.Point.coordSet P, σ a = τ a) :
    WeierstrassCurve.Affine.Point.map (σ.toAlgHom : Ω →ₐ[K] Ω) P
      = WeierstrassCurve.Affine.Point.map (τ.toAlgHom : Ω →ₐ[K] Ω) P := by
  rcases P with _ | ⟨x, y, hns⟩
  · rfl
  · exact Affine.Point.some_eq_some (E⁄Ω)
      (h x (by show x ∈ ({x, y} : Set Ω); exact Set.mem_insert _ _))
      (h y (by show y ∈ ({x, y} : Set Ω); exact Set.mem_insert_of_mem _ rfl))

end GaloisConj

/-! ### The sixth roots of unity, as a group

The `A = μ₂` argument of `sq_u_eq_sq_u_of_autStable` needs exactly one fact about `μ₆`: two
elements of order `3` or `6` generate the same subgroup modulo `±1`.  It is stated here in
elementary form so that no `rootsOfUnity` API is needed. -/

section SixthRoots

variable {F : Type*} [Field F]

/-- A cube root of unity other than `1` satisfies the cyclotomic relation `a² + a + 1 = 0`. -/
lemma sq_add_self_add_one_eq_zero {a : F} (h3 : a ^ 3 = 1) (h1 : a ≠ 1) :
    a ^ 2 + a + 1 = 0 := by
  have hfac : (a - 1) * (a ^ 2 + a + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.mp hfac with hz | hz
  · exact absurd (by linear_combination hz) h1
  · exact hz

/-- **A sixth root of unity that is not a square root of unity is `± a primitive cube root`.**
`v⁶ = 1` gives `v³ = ±1`; in the first case `v` itself is a primitive cube root, in the second
`-v` is. -/
lemma exists_cube_root_of_sixth {v : F} (hv6 : v ^ 6 = 1) (hv2 : v ^ 2 ≠ 1) :
    ∃ a : F, a ^ 3 = 1 ∧ a ^ 2 + a + 1 = 0 ∧ (v = a ∨ v = -a) := by
  have key : ∀ a : F, a ^ 3 = 1 → a ^ 2 ≠ 1 → a ^ 2 + a + 1 = 0 := fun a hc3 hc2 =>
    sq_add_self_add_one_eq_zero hc3 (fun hc => hc2 (by rw [hc]; ring))
  have hsplit : v ^ 3 = 1 ∨ v ^ 3 = -1 := by
    rcases mul_eq_zero.mp (show (v ^ 3 - 1) * (v ^ 3 + 1) = 0 by linear_combination hv6) with
      hz | hz
    · exact Or.inl (by linear_combination hz)
    · exact Or.inr (by linear_combination hz)
  rcases hsplit with h3 | h3
  · exact ⟨v, h3, key v h3 hv2, Or.inl rfl⟩
  · refine ⟨-v, by linear_combination -h3,
      key (-v) (by linear_combination -h3) (fun hc => hv2 (by linear_combination hc)),
      Or.inr (neg_neg v).symm⟩

/-- **Two sixth roots of unity that are not square roots of unity differ by a sign and a
power**: `v ∈ {w, -w, w², -w²}`.

Group-theoretically: `μ₆ / μ₂ ≅ μ₃`, and the elements of order `3` or `6` are exactly those
whose class generates `μ₃`, so any two of them generate the same subgroup together with `-1`.
The proof avoids all of that: `v = ±a` and `w = ±b` with `a`, `b` primitive cube roots, and
`(b - a)(b - a²) = b² + b + 1 = 0` forces `b = a` or `b = a²`, i.e. `a ∈ {b, b²} = {w², …}`. -/
lemma sixth_root_cases {v w : F} (hv6 : v ^ 6 = 1) (hv2 : v ^ 2 ≠ 1)
    (hw6 : w ^ 6 = 1) (hw2 : w ^ 2 ≠ 1) :
    v = w ∨ v = -w ∨ v = w ^ 2 ∨ v = -w ^ 2 := by
  obtain ⟨a, ha3, ha, hva⟩ := exists_cube_root_of_sixth hv6 hv2
  obtain ⟨b, hb3, hb, hwb⟩ := exists_cube_root_of_sixth hw6 hw2
  have hba : b = a ∨ b = a ^ 2 := by
    rcases mul_eq_zero.mp
      (show (b - a) * (b - a ^ 2) = 0 by linear_combination hb - b * ha + ha3) with hz | hz
    · exact Or.inl (by linear_combination hz)
    · exact Or.inr (by linear_combination hz)
  have hwsq : w ^ 2 = b ^ 2 := by
    rcases hwb with hc | hc
    · rw [hc]
    · rw [hc]; ring
  rcases hba with hc | hc
  · -- `b = a`, so `v = ±a = ±b` and `w = ±b`
    subst hc
    rcases hva with hv | hv <;> rcases hwb with hw | hw
    · exact Or.inl (hv.trans hw.symm)
    · exact Or.inr (Or.inl (by rw [hv, hw]; ring))
    · exact Or.inr (Or.inl (by rw [hv, hw]))
    · exact Or.inl (by rw [hv, hw])
  · -- `b = a²`, so `a = b⁴ = b² = w²`
    have hab : a = w ^ 2 := by rw [hwsq, hc]; linear_combination (-a) * ha3
    rcases hva with hv | hv
    · exact Or.inr (Or.inr (Or.inl (hv.trans hab)))
    · exact Or.inr (Or.inr (Or.inr (by rw [hv, hab])))

end SixthRoots

/-! ### The `μ₃`-valued descent cocycle at `j = 0` -/

section Cocycle

open Affine.Point

variable {K : Type*} [Field K] [CharZero K] {Ω : Type*} [Field Ω] [Algebra K Ω] [DecidableEq Ω]
  [CharZero Ω]

local instance isEllipticBaseChangeCoc {E : WeierstrassCurve K} [E.IsElliptic] :
    (E⁄Ω).IsElliptic :=
  inferInstanceAs (E.map (algebraMap K Ω)).IsElliptic

omit [CharZero K] in
/-- **THE `u`-COEFFICIENT IS DETERMINED UP TO SIGN** (opened as a sorry leaf 2026-07-28 by
decomposing `exists_muThree_cocycle_of_autStable_of_j_eq_zero`; **PROVEN 2026-07-30, no
remaining leaf**): any two automorphisms of `E⁄Ω` that carry `σ⟨g⟩` into `⟨g⟩` have the same
`u²`.

#### The proof, and the three lemmas it needed that did not exist here

The route below is exactly what was carried out.  Three small facts had to be added to this
file first, because their existing homes are DOWNSTREAM of it:

* `Affine.Point.autMap_injective` and `Affine.Point.autMap_negVariableChange` — restatements
  of `autPoint_injective` / `autPoint_negVariableChange` from `X0.lean`, which imports this
  module and so cannot be imported back;
* `Affine.Point.autMap_congr`, transport of `autMap` along an equality of variable changes.
  This is what lets `C * (C⁻¹ * C')` be identified with `C'` inside an `autMap`, and without
  it `autMap_mul` cannot be applied to the ratio at all.

and the `μ₆` arithmetic is isolated as `sixth_root_cases` above.

The ratio is handled WITHOUT inverting any map: for `y ∈ ⟨g⟩` pick `x ∈ ⟨g⟩` with
`autMap h (σ x) = y` (surjectivity, below), and then `autMap_mul` applied to
`C * (C⁻¹C') = C'` rewrites `autMap (C⁻¹C') y` as `autMap h' (σ x)`, which is in `⟨g⟩` by
`hmem'`.  That is the whole of the stability transfer.

This is the whole `A = μ₂` content of the `j = 0` descent, and it is where `ι`, `hmove`,
`hu6` and `hu2` are consumed.

#### What has to be proved

Write `A := {C : C • (E⁄Ω) = (E⁄Ω) ∧ autMap C preserves ⟨g⟩}`.  On the normal form
`y² = x³ + a₆` every automorphism is `⟨u,0,0,0⟩` with `u⁶ = 1` (`aut_eq_diag_sextic`), and
`u` is injective on automorphisms, so `A ↪ μ₆`.  `A` contains `-1`, which acts as negation
(`autMap_diag_neg`) and so preserves every `AddSubgroup`; `hmove` says `ι ∉ A`, and
`hu6`/`hu2` say `ι.u` has order `3` or `6`.  The only subgroup of `μ₆` containing `μ₂` and
not containing an element of order `3` or `6` is `μ₂` itself, so `u(A) = μ₂`.

Given `C` and `C'` both stable for the SAME `σ`, the ratio lies in `A`: `⟨g⟩` is finite
(`hg`, `hN`) and `autMap` is injective (`autPoint_injective`), so `autMap C ∘ map σ` and
`autMap C' ∘ map σ` are BIJECTIONS of `⟨g⟩`, whence `C'⁻¹C ∈ A` and `(C'.u)⁻¹C.u = ±1`.

#### Why the conclusion is `u²` and not `u`

`u` itself is genuinely NOT determined: `-1` acts as negation, which any `AddSubgroup`
absorbs, so `C` and `-C` are both stable and differ in `u` by a sign.  Squaring is exactly
what quotients that ambiguity away, and it is why the descent cocycle takes values in
`μ₆/μ₂ ≅ μ₃` rather than in `μ₆`.

#### Non-vacuity, and what refutes this leaf

`hmove` is REQUIRED: without it `A` may be all of `μ₆` and then `C` is determined only up to
a sixth root of unity, so `u²` is determined only up to a cube root and the conclusion is
false.  A refutation would exhibit an `E`, `g` and `σ` with two stable automorphisms whose
`u²` differ — necessarily with `A ⊋ μ₂`, i.e. violating `hmove`.

`hN` and `hg` enter only through the FINITENESS of `⟨g⟩`, which is what upgrades "maps into"
to "maps onto" and so makes the ratio stable rather than merely defined. -/
theorem sq_u_eq_sq_u_of_autStable {N : ℕ} (hN : N ≠ 0) (E : WeierstrassCurve K)
    [E.IsElliptic] (h₁ : (E⁄Ω).a₁ = 0) (h₂ : (E⁄Ω).a₂ = 0) (h₃ : (E⁄Ω).a₃ = 0)
    (h₄ : (E⁄Ω).a₄ = 0) (ha₆ : (E⁄Ω).a₆ ≠ 0)
    (g : (E⁄Ω).toAffine.Point) (hg : addOrderOf g = N)
    (ι : VariableChange Ω) (hι : ι • (E⁄Ω) = (E⁄Ω))
    (hmove : ∃ x ∈ AddSubgroup.zmultiples g, autMap hι x ∉ AddSubgroup.zmultiples g)
    (hu6 : (ι.u : Ω) ^ 6 = 1) (hu2 : (ι.u : Ω) ^ 2 ≠ 1)
    (σ : Ω ≃ₐ[K] Ω) (C C' : VariableChange Ω)
    (h : C • (E⁄Ω) = (E⁄Ω)) (h' : C' • (E⁄Ω) = (E⁄Ω))
    (hmem : ∀ x ∈ AddSubgroup.zmultiples g,
      autMap h (Affine.Point.map σ.toAlgHom x) ∈ AddSubgroup.zmultiples g)
    (hmem' : ∀ x ∈ AddSubgroup.zmultiples g,
      autMap h' (Affine.Point.map σ.toAlgHom x) ∈ AddSubgroup.zmultiples g) :
    (C.u : Ω) ^ 2 = (C'.u : Ω) ^ 2 := by
  classical
  haveI : Finite (AddSubgroup.zmultiples g) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [Nat.card_zmultiples, hg]
    exact hN
  have h2Ω : (2 : Ω) ≠ 0 := by norm_num
  have h3Ω : (3 : Ω) ≠ 0 := by norm_num
  -- an automorphism of `E⁄Ω` is determined by its `u`
  have heqU : ∀ X Y : VariableChange Ω, X • (E⁄Ω) = (E⁄Ω) → Y • (E⁄Ω) = (E⁄Ω) →
      (X.u : Ω) = (Y.u : Ω) → X = Y := by
    intro X Y hX hY hu
    have hXY : (X * Y⁻¹) • (E⁄Ω) = (E⁄Ω) := by
      have hc : (X * Y⁻¹) • (Y • (E⁄Ω)) = (E⁄Ω) := by
        rw [← mul_smul, inv_mul_cancel_right, hX]
      rwa [hY] at hc
    have hu1 : (X * Y⁻¹).u = 1 := by
      show X.u * Y.u⁻¹ = 1
      rw [Units.ext hu, mul_inv_cancel]
    have h1 := eq_one_of_u_eq_one_of_smul_eq (E⁄Ω) h2Ω h3Ω hu1 hXY
    have h2 : X * Y⁻¹ * Y = 1 * Y := by rw [h1]
    rwa [inv_mul_cancel_right, one_mul] at h2
  -- products of `⟨g⟩`-stable automorphisms are `⟨g⟩`-stable
  have hstabmul : ∀ (X Y : VariableChange Ω) (hX : X • (E⁄Ω) = (E⁄Ω))
      (hY : Y • (E⁄Ω) = (E⁄Ω)) (hXY : (X * Y) • (E⁄Ω) = (E⁄Ω)),
      (∀ y ∈ AddSubgroup.zmultiples g, autMap hX y ∈ AddSubgroup.zmultiples g) →
      (∀ y ∈ AddSubgroup.zmultiples g, autMap hY y ∈ AddSubgroup.zmultiples g) →
      ∀ y ∈ AddSubgroup.zmultiples g, autMap hXY y ∈ AddSubgroup.zmultiples g := by
    intro X Y hX hY hXY sX sY y hy
    rw [autMap_mul hX hY hXY]
    exact sY _ (sX y hy)
  -- the negation automorphism is `⟨g⟩`-stable, which is the `μ₂ ⊆ A` half
  have hnvs : (E⁄Ω).negVariableChange • (E⁄Ω) = (E⁄Ω) := negVariableChange_smul_self _
  have hnvstab : ∀ y ∈ AddSubgroup.zmultiples g,
      autMap hnvs y ∈ AddSubgroup.zmultiples g := by
    intro y hy
    rw [Affine.Point.autMap_negVariableChange]
    exact AddSubgroup.neg_mem _ hy
  -- THE `A = μ₂` STEP: a `⟨g⟩`-stable automorphism has `u² = 1`
  have hcore : ∀ (D : VariableChange Ω) (hD : D • (E⁄Ω) = (E⁄Ω)),
      (∀ y ∈ AddSubgroup.zmultiples g, autMap hD y ∈ AddSubgroup.zmultiples g) →
      (D.u : Ω) ^ 2 = 1 := by
    intro D hD sD
    by_contra hD2
    have hD6 : (D.u : Ω) ^ 6 = 1 := (aut_eq_diag_sextic h₁ h₂ h₃ h₄ ha₆ hD).2
    have hDD : (D * D) • (E⁄Ω) = (E⁄Ω) := by rw [mul_smul, hD, hD]
    have hDDstab : ∀ y ∈ AddSubgroup.zmultiples g,
        autMap hDD y ∈ AddSubgroup.zmultiples g := hstabmul D D hD hD hDD sD sD
    -- one of the four elements `±D`, `±D²` of `A` has the same `u` as `ι`
    obtain ⟨X, hX, hXstab, hXu⟩ :
        ∃ (X : VariableChange Ω) (hX : X • (E⁄Ω) = (E⁄Ω)),
          (∀ y ∈ AddSubgroup.zmultiples g, autMap hX y ∈ AddSubgroup.zmultiples g) ∧
            (X.u : Ω) = (ι.u : Ω) := by
      have hnvu : (((E⁄Ω).negVariableChange).u : Ω) = -1 := by
        rw [negVariableChange_u]; norm_num
      rcases sixth_root_cases hu6 hu2 hD6 hD2 with hc | hc | hc | hc
      · exact ⟨D, hD, sD, hc.symm⟩
      · refine ⟨(E⁄Ω).negVariableChange * D, by rw [mul_smul, hD, hnvs], ?_, ?_⟩
        · exact hstabmul _ _ hnvs hD (by rw [mul_smul, hD, hnvs]) hnvstab sD
        · show ((((E⁄Ω).negVariableChange).u * D.u : Ωˣ) : Ω) = _
          rw [Units.val_mul, hnvu, hc]; ring
      · refine ⟨D * D, hDD, hDDstab, ?_⟩
        show ((D.u * D.u : Ωˣ) : Ω) = _
        rw [Units.val_mul, hc]; ring
      · refine ⟨(E⁄Ω).negVariableChange * (D * D), by rw [mul_smul, hDD, hnvs], ?_, ?_⟩
        · exact hstabmul _ _ hnvs hDD (by rw [mul_smul, hDD, hnvs]) hnvstab hDDstab
        · show ((((E⁄Ω).negVariableChange).u * (D.u * D.u) : Ωˣ) : Ω) = _
          rw [Units.val_mul, Units.val_mul, hnvu, hc]; ring
    have hXι : X = ι := heqU X ι hX hι hXu
    subst hXι
    obtain ⟨x₀, hx₀, hx₀'⟩ := hmove
    exact hx₀' (hXstab x₀ hx₀)
  -- `y ↦ autMap h (map σ y)` is an injective self-map of the FINITE `⟨g⟩`, hence onto
  have hsurj : ∀ y ∈ AddSubgroup.zmultiples g, ∃ x ∈ AddSubgroup.zmultiples g,
      autMap h (Affine.Point.map σ.toAlgHom x) = y := by
    intro y hy
    have hFinj : Function.Injective
        (fun z : AddSubgroup.zmultiples g =>
          (⟨autMap h (Affine.Point.map σ.toAlgHom z), hmem z z.2⟩ :
            AddSubgroup.zmultiples g)) := by
      intro z w hzw
      exact Subtype.ext (Affine.Point.map_injective _
        (Affine.Point.autMap_injective h (congrArg Subtype.val hzw)))
    obtain ⟨z, hz⟩ := Finite.injective_iff_surjective.mp hFinj ⟨y, hy⟩
    exact ⟨z, z.2, congrArg Subtype.val hz⟩
  -- the ratio `C⁻¹ C'` is a `⟨g⟩`-stable automorphism, WITHOUT inverting any map
  have hCinv : C⁻¹ • (E⁄Ω) = (E⁄Ω) := by
    have hc : C⁻¹ • (C • (E⁄Ω)) = (E⁄Ω) := by rw [← mul_smul, inv_mul_cancel, one_smul]
    rwa [h] at hc
  have hD : (C⁻¹ * C') • (E⁄Ω) = (E⁄Ω) := by rw [mul_smul, h', hCinv]
  have hprod : C * (C⁻¹ * C') = C' := mul_inv_cancel_left C C'
  have hCD : (C * (C⁻¹ * C')) • (E⁄Ω) = (E⁄Ω) := by rw [hprod]; exact h'
  have hDstab : ∀ y ∈ AddSubgroup.zmultiples g,
      autMap hD y ∈ AddSubgroup.zmultiples g := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hsurj y hy
    rw [← hxy, ← autMap_mul h hD hCD, Affine.Point.autMap_congr hprod hCD h']
    exact hmem' x hx
  have hkey := hcore _ hD hDstab
  have huval : (((C⁻¹ * C').u : Ωˣ) : Ω) = (C.u : Ω)⁻¹ * (C'.u : Ω) := by
    show (((C.u)⁻¹ * C'.u : Ωˣ) : Ω) = _
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
  rw [huval, mul_pow] at hkey
  have hCne : (C.u : Ω) ≠ 0 := C.u.ne_zero
  field_simp at hkey
  exact hkey.symm

/-- **THE FINITE GALOIS LEVEL** (opened as a sorry leaf 2026-07-28 by decomposing
`exists_muThree_cocycle_of_autStable_of_j_eq_zero`; **PROVEN 2026-07-30**, with
`Algebra.IsAlgebraic K Ω` REPLACED by the strictly stronger `Normal K Ω` — see below, and
note that `Normal` already implies `Algebra.IsAlgebraic`, so no hypothesis was lost): the
finitely many points of `⟨g⟩`, and the cube roots of unity, are all defined over ONE finite
Galois extension of `K`.
omit [DecidableEq Ω] [CharZero Ω] in
/-- **A FINITE SET OF ELEMENTS OF A NORMAL ALGEBRAIC EXTENSION LIES IN A FINITE GALOIS
SUBEXTENSION** (PROVEN 2026-07-30).

`K(S)` is finite over `K` (`IntermediateField.finiteDimensional_adjoin`, each element being
integral), and its normal closure INSIDE `Ω` is finite Galois over `K` — the two instances
`IntermediateField.normalClosure.normal` and `.is_finiteDimensional`, plus separability from
`PerfectField K` in characteristic zero.

**`[Normal K Ω]` is exactly what makes the normal closure available inside `Ω`**, and it is
the hypothesis whose absence made `exists_finiteGaloisLevel_of_addOrder` false; see the
falsity audit there. -/
theorem exists_finiteGalois_containing_finset [Normal K Ω] (S : Finset Ω) :
    ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L) (_ : IsGalois K L),
      ∀ x ∈ S, x ∈ L := by
  classical
  have hint : ∀ x ∈ (S : Set Ω), IsIntegral K x := fun x _ =>
    (Algebra.IsAlgebraic.isAlgebraic (R := K) x).isIntegral
  haveI : FiniteDimensional K (IntermediateField.adjoin K (S : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin hint
  haveI : Normal K (IntermediateField.normalClosure K
      (IntermediateField.adjoin K (S : Set Ω)) Ω) := inferInstance
  haveI : FiniteDimensional K (IntermediateField.normalClosure K
      (IntermediateField.adjoin K (S : Set Ω)) Ω) := inferInstance
  refine ⟨IntermediateField.normalClosure K (IntermediateField.adjoin K (S : Set Ω)) Ω,
    inferInstance, ⟨⟩, fun x hx => ?_⟩
  exact IntermediateField.le_normalClosure _ (IntermediateField.subset_adjoin K _ hx)

omit [CharZero Ω] in
/-- **THE FINITE GALOIS LEVEL** (opened as a sorry leaf 2026-07-28 by decomposing
`exists_muThree_cocycle_of_autStable_of_j_eq_zero`; **REFUTED AS STATED and RESTATED with
`[Normal K Ω]`, then PROVEN, 2026-07-30**): the coordinates of the points of `⟨g⟩`, and the
cube roots of unity, are all defined over ONE finite Galois extension of `K`.

This is the continuity of the descent cocycle, in the concrete form the consumer needs: `c`
is inflated from `Gal(L/K)`, which is what makes Hilbert 90 applicable to it.

#### The proof

`⟨g⟩` is finite (`IsOfFinAddOrder.finite_zmultiples`, from `hg` and `hN`) and each of its
points contributes at most two coordinates (`Affine.Point.coordSet`), so the set `S` of all
coordinates of all points of `⟨g⟩` together with the cube roots of unity in `Ω` — at most
three more, being roots of `X ^ 3 - 1` — is FINITE.  Every element of `S` is integral over
`K` (`Algebra.IsIntegral`, from algebraicity), so `M := K⟮S⟯` is finite over `K`, and
`L := normalClosure K M Ω` is finite (`normalClosure.is_finiteDimensional`) and Galois
(`IsGalois.normalClosure`).  Both conclusions then read off `S ⊆ M ≤ L`: the cube roots are
in `L` by construction, and two automorphisms agreeing on `L` agree on every coordinate of
every point of `⟨g⟩`, hence on the points themselves
(`map_eq_map_of_eqOn_coordSet`).

#### WHY `Normal K Ω`, AND WHY IT IS NOT A COSMETIC STRENGTHENING (2026-07-30)

The leaf as originally cut asked only for `Algebra.IsAlgebraic K Ω`, and the route recorded
in its docstring — "its normal closure is finite Galois" — DOES NOT RUN under that
hypothesis, because a normal closure taken *inside* `Ω` is normal only when `Ω` itself is
(mathlib's `normalClosure.normal` and `IsGalois.normalClosure` both require it, and the
requirement is real, not an artefact: `Normal K L` asks a minimal polynomial with a root in
`L` to SPLIT in `L`, and `Ω` need not contain the missing roots).

The obstruction is not merely that this proof fails; the statement itself is in doubt over a
non-normal `Ω`.  Write `G = Aut(Ω/K)`, `M ⊆ Ω` for the coordinate field of `⟨g⟩`, and
`G_X ≤ G` for the subgroup fixing `X` pointwise.  The conclusion says exactly that
`G_L ⊆ G_M` for some finite Galois `L ⊆ Ω`; since every such `L` lies in the maximal
Galois-generated subfield `Ω^{gal}`, it requires `G_{Ω^{gal}} ⊆ G_M`.  That can fail:
for `K = ℚ` and `Ω = ℚ(ω, 2 ^ (1/9))` one has `Aut(Ω/ℚ) ≅ S₃`, `Ω^{gal} = ℚ(ω, 2 ^ (1/3))`
(computed from the Galois closure `ℚ(ζ₉, 2 ^ (1/9))`, in which the subgroup cutting out `Ω`
has normal closure of index `6`), and the order-`3` automorphism `2 ^ (1/9) ↦ ω · 2 ^ (1/9)`
fixes every finite Galois subfield of `Ω` while moving `ℚ(2 ^ (1/9))`.  What is NOT supplied
here is the last mile — an elliptic curve over `ℚ` and a torsion point whose coordinates sit
in `Ω \ ℚ(ω, 2 ^ (1/3))` — so this is a structural obstruction, not a checked
counterexample, and the leaf is NOT recorded as refuted.  A successor who wants the weaker
hypothesis back must either produce that curve (refuting the original cut) or find a route
that does not go through a normal closure.

`Normal K Ω` holds in the application, where `Ω = K̄`: `IsAlgClosure.normal`.

#### The hypotheses that are genuinely load-bearing

Algebraicity (now carried by `Normal`) cannot be dropped: over a transcendental extension the
coordinates of `g` need not be algebraic and no finite `L` exists.  `hN` and `hg` enter only
through the FINITENESS of `⟨g⟩`; at `N = 0`, `addOrderOf g = 0` means `⟨g⟩` is infinite and
the coordinate set need not be finite, which is why `hN` cannot be dropped either.
`[E.IsElliptic]` is not used by the proof and is retained only to keep the signature aligned
with its siblings in this section. -/
theorem exists_finiteGaloisLevel_of_addOrder [Normal K Ω]
    {N : ℕ} (hN : N ≠ 0) (E : WeierstrassCurve K) [E.IsElliptic]
    (g : (E⁄Ω).toAffine.Point) (hg : addOrderOf g = N) :
    ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L) (_ : IsGalois K L),
      (∀ z : Ω, z ^ 3 = 1 → z ∈ L) ∧
      ∀ σ τ : Ω ≃ₐ[K] Ω, (∀ x ∈ L, σ x = τ x) →
        ∀ P ∈ AddSubgroup.zmultiples g,
          Affine.Point.map σ.toAlgHom P = Affine.Point.map τ.toAlgHom P := by
  classical
  haveI : IsGalois K Ω := ⟨⟩
  have hcube : {z : Ω | z ^ 3 = 1}.Finite := by
    refine Set.Finite.subset (Finset.finite_toSet (Polynomial.nthRoots 3 (1 : Ω)).toFinset) ?_
    intro z hz
    simpa [Polynomial.mem_nthRoots] using hz
  have hpos : 0 < addOrderOf g := by rw [hg]; exact Nat.pos_of_ne_zero hN
  have hfo : IsOfFinAddOrder g := addOrderOf_pos_iff.mp hpos
  have hzfin : ((AddSubgroup.zmultiples g : AddSubgroup ((E⁄Ω).toAffine.Point)) :
      Set ((E⁄Ω).toAffine.Point)).Finite := hfo.finite_zmultiples
  set S : Set Ω := {z : Ω | z ^ 3 = 1} ∪
    ⋃ P ∈ (AddSubgroup.zmultiples g : Set ((E⁄Ω).toAffine.Point)),
      Affine.Point.coordSet P with hSdef
  have hSfin : S.Finite :=
    hcube.union (hzfin.biUnion fun P _ => Affine.Point.finite_coordSet P)
  haveI : Finite S := hSfin
  haveI : FiniteDimensional K (IntermediateField.adjoin K S) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hsub : ∀ a ∈ S, a ∈ IntermediateField.normalClosure K (IntermediateField.adjoin K S) Ω :=
    fun a ha =>
      (IntermediateField.le_normalClosure (IntermediateField.adjoin K S))
        (IntermediateField.subset_adjoin K S ha)
  refine ⟨IntermediateField.normalClosure K (IntermediateField.adjoin K S) Ω, inferInstance,
    inferInstance, fun z hz => hsub z (Or.inl hz), fun σ τ hστ P hP => ?_⟩
  refine map_eq_map_of_eqOn_coordSet E σ τ P fun a ha => hστ a (hsub a (Or.inr ?_))
  exact Set.mem_biUnion hP ha

/-- **THE `μ₃`-VALUED DESCENT COCYCLE AT `j = 0`, in normal form** (PROVEN 2026-07-28 over the
two leaves `sq_u_eq_sq_u_of_autStable` and `exists_finiteGaloisLevel_of_addOrder`; the second
of those was CLOSED 2026-07-30, so `sq_u_eq_sq_u_of_autStable` is now the only leaf left under
this declaration.  Its `Algebra.IsAlgebraic K Ω` became `Normal K Ω` at the same time — see
`exists_finiteGaloisLevel_of_addOrder` for why that strengthening is not cosmetic).

Everything that is not "the `u` is determined up to sign" or "the level is finite" is proved
here.  In particular the COCYCLE IDENTITY is proven outright, and it is the mathematically
substantive part: for `σ`, `τ` with stable witnesses `C_σ`, `C_τ`, the variable change
`(σ C_τ) * C_σ` is a stable witness for `σ * τ`, because

* `smul_map_of_smul_baseChange` says `σ C_τ` is again an automorphism of `E⁄Ω`;
* `autMap_mul` says its `autMap` composes as `autMap C_σ ∘ autMap (σ C_τ)`;
* `map_autMap` says `autMap (σ C_τ) ∘ map σ = map σ ∘ autMap C_τ`;

so the composite sends `x ∈ ⟨g⟩` to `autMap C_σ (map σ (autMap C_τ (map τ x)))`, which lies
in `⟨g⟩` by applying stability for `τ` and then for `σ`.  Reading off `u` gives
`((σC_τ) * C_σ).u = σ(C_τ.u) · C_σ.u`, and squaring is the identity
`c(στ) = c(σ) · σ(c(τ))`. -/
theorem exists_muThreeCocycle_of_autStable_of_sextic {N : ℕ} (hN : N ≠ 0)
    [Normal K Ω] (E : WeierstrassCurve K)
    [E.IsElliptic] (h₁ : (E⁄Ω).a₁ = 0) (h₂ : (E⁄Ω).a₂ = 0) (h₃ : (E⁄Ω).a₃ = 0)
    (h₄ : (E⁄Ω).a₄ = 0) (ha₆ : (E⁄Ω).a₆ ≠ 0)
    (g : (E⁄Ω).toAffine.Point) (hg : addOrderOf g = N)
    (haut : ∀ σ : Ω ≃ₐ[K] Ω, ∃ (C : VariableChange Ω) (h : C • (E⁄Ω) = (E⁄Ω)),
      ∀ x ∈ AddSubgroup.zmultiples g,
        autMap h (Affine.Point.map σ.toAlgHom x) ∈ AddSubgroup.zmultiples g)
    (ι : VariableChange Ω) (hι : ι • (E⁄Ω) = (E⁄Ω))
    (hmove : ∃ x ∈ AddSubgroup.zmultiples g, autMap hι x ∉ AddSubgroup.zmultiples g)
    (hu6 : (ι.u : Ω) ^ 6 = 1) (hu2 : (ι.u : Ω) ^ 2 ≠ 1) :
    ∃ (c : (Ω ≃ₐ[K] Ω) → Ω) (L : IntermediateField K Ω) (_ : FiniteDimensional K L)
      (_ : IsGalois K L),
      (∀ σ, c σ ∈ L) ∧
      (∀ σ, c σ ^ 3 = 1) ∧
      (∀ σ τ : Ω ≃ₐ[K] Ω, c (σ * τ) = c σ * σ (c τ)) ∧
      (∀ σ τ : Ω ≃ₐ[K] Ω, (∀ x ∈ L, σ x = τ x) → c σ = c τ) ∧
      (∀ σ : Ω ≃ₐ[K] Ω, ∃ (C : VariableChange Ω) (h : C • (E⁄Ω) = (E⁄Ω)),
        (C.u : Ω) ^ 2 = c σ ∧
        ∀ x ∈ AddSubgroup.zmultiples g,
          autMap h (Affine.Point.map σ.toAlgHom x) ∈ AddSubgroup.zmultiples g) := by
  classical
  choose C hC hCmem using haut
  obtain ⟨L, hLfin, hLgal, hLcube, hLact⟩ :=
    exists_finiteGaloisLevel_of_addOrder (K := K) (Ω := Ω) hN E g hg
  -- the uniqueness statement, packaged once
  have huniq : ∀ (σ : Ω ≃ₐ[K] Ω) (D : VariableChange Ω) (hD : D • (E⁄Ω) = (E⁄Ω)),
      (∀ x ∈ AddSubgroup.zmultiples g,
        autMap hD (Affine.Point.map σ.toAlgHom x) ∈ AddSubgroup.zmultiples g) →
      (D.u : Ω) ^ 2 = ((C σ).u : Ω) ^ 2 := by
    intro σ D hD hDmem
    exact sq_u_eq_sq_u_of_autStable hN E h₁ h₂ h₃ h₄ ha₆ g hg ι hι hmove hu6 hu2 σ D (C σ)
      hD (hC σ) hDmem (hCmem σ)
  have hcube : ∀ σ : Ω ≃ₐ[K] Ω, (((C σ).u : Ω) ^ 2) ^ 3 = 1 := by
    intro σ
    have h6 : ((C σ).u : Ω) ^ 6 = 1 :=
      (aut_eq_diag_sextic h₁ h₂ h₃ h₄ ha₆ (hC σ)).2
    rw [← h6]; ring
  refine ⟨fun σ => ((C σ).u : Ω) ^ 2, L, hLfin, hLgal, ?_, hcube, ?_, ?_, ?_⟩
  · exact fun σ => hLcube _ (hcube σ)
  · -- the cocycle identity
    intro σ τ
    set D : VariableChange Ω :=
      (C τ).map (σ.toAlgHom : Ω →ₐ[K] Ω).toRingHom * C σ with hDdef
    have hDτ : ((C τ).map (σ.toAlgHom : Ω →ₐ[K] Ω).toRingHom) • (E⁄Ω) = (E⁄Ω) :=
      smul_map_of_smul_baseChange E σ (hC τ)
    have hD : D • (E⁄Ω) = (E⁄Ω) := by
      rw [hDdef, mul_smul, hC σ, hDτ]
    have hDmem : ∀ x ∈ AddSubgroup.zmultiples g,
        autMap hD (Affine.Point.map (σ * τ : Ω ≃ₐ[K] Ω).toAlgHom x) ∈
          AddSubgroup.zmultiples g := by
      intro x hx
      have hsplit : Affine.Point.map (σ * τ : Ω ≃ₐ[K] Ω).toAlgHom x
          = Affine.Point.map (σ.toAlgHom : Ω →ₐ[K] Ω)
              (Affine.Point.map (τ.toAlgHom : Ω →ₐ[K] Ω) x) := by
        rw [Affine.Point.map_map]
        congr 1
      rw [hsplit, autMap_mul hDτ (hC σ) hD, ← map_autMap E σ (hC τ) hDτ]
      exact hCmem σ _ (hCmem τ x hx)
    have hval : (D.u : Ω) = σ ((C τ).u : Ω) * ((C σ).u : Ω) := by
      simp only [hDdef, VariableChange.mul_def, Units.val_mul, VariableChange.map_u,
        Units.coe_map, MonoidHom.coe_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rfl
    have := huniq (σ * τ) D hD hDmem
    rw [hval, mul_pow, ← map_pow] at this
    exact this.symm.trans (mul_comm _ _)
  · -- inflation from `L`
    intro σ τ hστ
    have hmemτ : ∀ x ∈ AddSubgroup.zmultiples g,
        autMap (hC σ) (Affine.Point.map (τ.toAlgHom : Ω →ₐ[K] Ω) x) ∈
          AddSubgroup.zmultiples g := by
      intro x hx
      rw [← hLact σ τ hστ x hx]
      exact hCmem σ x hx
    exact huniq τ (C σ) (hC σ) hmemτ
  · exact fun σ => ⟨C σ, hC σ, rfl, hCmem σ⟩

/-- **THE `μ₃`-VALUED DESCENT COCYCLE AT `j = 0`** (PROVEN 2026-07-28 over the two leaves
`sq_u_eq_sq_u_of_autStable` and `exists_finiteGaloisLevel_of_addOrder`; the latter was CLOSED
2026-07-30, leaving `sq_u_eq_sq_u_of_autStable` as the only leaf here).

This is `exists_muThreeCocycle_of_autStable_of_sextic` with the normal-form hypotheses
replaced by `hj : E.j = 0`.  The proof puts `E` in the form `y² = x³ + b` over `K`
(`exists_smul_eq_sexticModel`) and transports `g`, `haut`, `ι` and `hmove` along the
resulting isomorphism, exactly as `exists_stableCyclic_sexticTwist` does.

**The transport back is not a second conjugation.**  The cocycle `c` is produced on the
normal form, and the witness clause is recovered on the ORIGINAL curve by conjugating each
`haut σ` FORWARD to the normal form and then applying the uniqueness leaf
`sq_u_eq_sq_u_of_autStable` there: conjugation does not change `u`, so `(C.u)² = c σ` for
the original `C`.  That is why only the forward direction of
`exists_conj_autMap_baseChange` is ever needed. -/
theorem exists_muThreeCocycle_of_autStable_of_j_eq_zero [Normal K Ω] {N : ℕ}
    (hN : N ≠ 0) (E : WeierstrassCurve K) [E.IsElliptic] (hj : E.j = 0)
    (g : (E⁄Ω).toAffine.Point) (hg : addOrderOf g = N)
    (haut : ∀ σ : Ω ≃ₐ[K] Ω, ∃ (C : VariableChange Ω) (h : C • (E⁄Ω) = (E⁄Ω)),
      ∀ x ∈ AddSubgroup.zmultiples g,
        autMap h (Affine.Point.map σ.toAlgHom x) ∈ AddSubgroup.zmultiples g)
    (ι : VariableChange Ω) (hι : ι • (E⁄Ω) = (E⁄Ω))
    (hmove : ∃ x ∈ AddSubgroup.zmultiples g, autMap hι x ∉ AddSubgroup.zmultiples g)
    (hu6 : (ι.u : Ω) ^ 6 = 1) (hu2 : (ι.u : Ω) ^ 2 ≠ 1) :
    ∃ (c : (Ω ≃ₐ[K] Ω) → Ω) (L : IntermediateField K Ω) (_ : FiniteDimensional K L)
      (_ : IsGalois K L),
      (∀ σ, c σ ∈ L) ∧
      (∀ σ, c σ ^ 3 = 1) ∧
      (∀ σ τ : Ω ≃ₐ[K] Ω, c (σ * τ) = c σ * σ (c τ)) ∧
      (∀ σ τ : Ω ≃ₐ[K] Ω, (∀ x ∈ L, σ x = τ x) → c σ = c τ) ∧
      (∀ σ : Ω ≃ₐ[K] Ω, ∃ (C : VariableChange Ω) (h : C • (E⁄Ω) = (E⁄Ω)),
        (C.u : Ω) ^ 2 = c σ ∧
        ∀ x ∈ AddSubgroup.zmultiples g,
          autMap h (Affine.Point.map σ.toAlgHom x) ∈ AddSubgroup.zmultiples g) := by
  obtain ⟨C₀, b, hb, hC₀⟩ := exists_smul_eq_sexticModel E hj
  have h₁ : ((C₀ • E)⁄Ω).a₁ = 0 := by
    show algebraMap K Ω ((C₀ • E).a₁) = 0
    rw [hC₀]; simp
  have h₂ : ((C₀ • E)⁄Ω).a₂ = 0 := by
    show algebraMap K Ω ((C₀ • E).a₂) = 0
    rw [hC₀]; simp
  have h₃ : ((C₀ • E)⁄Ω).a₃ = 0 := by
    show algebraMap K Ω ((C₀ • E).a₃) = 0
    rw [hC₀]; simp
  have h₄ : ((C₀ • E)⁄Ω).a₄ = 0 := by
    show algebraMap K Ω ((C₀ • E).a₄) = 0
    rw [hC₀]; simp
  have ha₆ : ((C₀ • E)⁄Ω).a₆ ≠ 0 := by
    show algebraMap K Ω ((C₀ • E).a₆) ≠ 0
    rw [hC₀, sexticModel_a₆]
    exact fun h0 => hb ((algebraMap K Ω).injective (by rw [h0, _root_.map_zero]))
  set Θ := Affine.Point.equivVariableChangeBaseChange E C₀ Ω with hΘdef
  set g₁ := Θ.symm g with hg₁def
  have hΘg : Θ g₁ = g := Θ.apply_symm_apply g
  have hmemΘ : ∀ x : ((C₀ • E)⁄Ω).toAffine.Point,
      x ∈ AddSubgroup.zmultiples g₁ ↔ Θ x ∈ AddSubgroup.zmultiples g := by
    intro x
    simp only [AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, by rw [← hn, map_zsmul, hΘg]⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, Θ.injective (by rw [map_zsmul, hΘg, hn])⟩
  have hg₁ : addOrderOf g₁ = N := by rw [← hg, ← hΘg]; exact (Θ.addOrderOf_eq g₁).symm
  -- the forward conjugation of a stable automorphism, used in both directions below
  have hconjstable : ∀ (σ : Ω ≃ₐ[K] Ω) (C : VariableChange Ω) (hC : C • (E⁄Ω) = (E⁄Ω)),
      (∀ x ∈ AddSubgroup.zmultiples g,
        autMap hC (Affine.Point.map σ.toAlgHom x) ∈ AddSubgroup.zmultiples g) →
      ∃ h' : (C₀.baseChange Ω * C * (C₀.baseChange Ω)⁻¹) • ((C₀ • E)⁄Ω) = ((C₀ • E)⁄Ω),
        ((C₀.baseChange Ω * C * (C₀.baseChange Ω)⁻¹).u : Ω) = (C.u : Ω) ∧
        ∀ x ∈ AddSubgroup.zmultiples g₁,
          autMap h' (Affine.Point.map σ.toAlgHom x) ∈ AddSubgroup.zmultiples g₁ := by
    intro σ C hC hCmem
    obtain ⟨h', hconj⟩ := exists_conj_autMap_baseChange E C₀ hC
    refine ⟨h', ?_, fun x hx => ?_⟩
    · show ((C₀.baseChange Ω).u * C.u * ((C₀.baseChange Ω).u)⁻¹ : Ωˣ) = (C.u : Ω)
      rw [mul_comm ((C₀.baseChange Ω).u) C.u, mul_assoc, mul_inv_cancel, mul_one]
    · rw [hmemΘ, hconj, Affine.Point.equivVariableChangeBaseChange_galois]
      exact hCmem _ ((hmemΘ x).mp hx)
  have haut₁ : ∀ σ : Ω ≃ₐ[K] Ω, ∃ (C : VariableChange Ω) (h : C • ((C₀ • E)⁄Ω) = ((C₀ • E)⁄Ω)),
      ∀ x ∈ AddSubgroup.zmultiples g₁,
        autMap h (Affine.Point.map σ.toAlgHom x) ∈ AddSubgroup.zmultiples g₁ := by
    intro σ
    obtain ⟨C, hC, hCmem⟩ := haut σ
    obtain ⟨h', _, hmem'⟩ := hconjstable σ C hC hCmem
    exact ⟨_, h', hmem'⟩
  obtain ⟨hι₁, hιconj⟩ := exists_conj_autMap_baseChange E C₀ hι
  have huval : ((C₀.baseChange Ω * ι * (C₀.baseChange Ω)⁻¹).u : Ω) = (ι.u : Ω) := by
    show ((C₀.baseChange Ω).u * ι.u * ((C₀.baseChange Ω).u)⁻¹ : Ωˣ) = (ι.u : Ω)
    rw [mul_comm ((C₀.baseChange Ω).u) ι.u, mul_assoc, mul_inv_cancel, mul_one]
  have hmove₁ : ∃ x ∈ AddSubgroup.zmultiples g₁, autMap hι₁ x ∉ AddSubgroup.zmultiples g₁ := by
    obtain ⟨x, hx, hx'⟩ := hmove
    refine ⟨Θ.symm x, (hmemΘ _).mpr (by rw [Θ.apply_symm_apply]; exact hx), ?_⟩
    intro hcon
    exact hx' (by
      have := (hmemΘ _).mp hcon
      rwa [hιconj, Θ.apply_symm_apply] at this)
  obtain ⟨c, L, hLfin, hLgal, hcL, hc3, hcoc, hinfl, hwit⟩ :=
    exists_muThreeCocycle_of_autStable_of_sextic hN (C₀ • E) h₁ h₂ h₃ h₄ ha₆ g₁ hg₁ haut₁ _
      hι₁ hmove₁ (by rw [huval]; exact hu6) (by rw [huval]; exact hu2)
  refine ⟨c, L, hLfin, hLgal, hcL, hc3, hcoc, hinfl, fun σ => ?_⟩
  obtain ⟨C, hC, hCmem⟩ := haut σ
  obtain ⟨h', huC, hmem'⟩ := hconjstable σ C hC hCmem
  obtain ⟨C₁, hC₁, hC₁u, hC₁mem⟩ := hwit σ
  refine ⟨C, hC, ?_, hCmem⟩
  rw [← huC, ← hC₁u]
  exact sq_u_eq_sq_u_of_autStable hN (C₀ • E) h₁ h₂ h₃ h₄ ha₆ g₁ hg₁ _ hι₁ hmove₁
    (by rw [huval]; exact hu6) (by rw [huval]; exact hu2) σ _ C₁ h' hC₁ hmem' hC₁mem

end Cocycle

end WeierstrassCurve

end
