/-
GaloisRepresentation/ComplexConjugation.lean — own work for the Fermat
project (not vendored from the FLT project).

# Complex conjugation as an element of `Gal(ℚ̄/ℚ)`

`Γ ℚ = Field.absoluteGaloisGroup ℚ` is the automorphism group of the
ABSTRACT algebraic closure `AlgebraicClosure ℚ`, which carries no complex
structure and hence no complex conjugation.  Yet *oddness* of a
two-dimensional Galois representation — `det ρ c = −1` for `c` complex
conjugation — is stated in terms of exactly such an element, and oddness
recurs throughout the hardly ramified / pillar-α cluster (it is what
`IsHardlyRamified.det` delivers once the cyclotomic character is evaluated at
`c`).  Before this module the repository had NO complex-conjugation
vocabulary at all, which is why Schlessinger's H4 stratum
(`exists_smul_eq_of_commute_of_isIrreducible` in
`HardlyRamified/Deformation.lean`) could not even be approached.  This module
supplies the missing vocabulary as a reusable node rather than as an ad-hoc
inlined construction:

* `complexConj : Γ ℚ`, complex conjugation, with `complexConjRingEquiv` its
  `RingEquiv` shadow (the shape `cyclotomicCharacter` consumes);
* `complexConj_mul_self : complexConj * complexConj = 1` — it is an
  involution;
* `cyclotomicCharacter_complexConj` — the `p`-adic cyclotomic character sends
  it to `−1`, for `p` an odd prime.

Those are exactly the three facts an oddness argument needs.

## The construction, and the choice it involves

`AlgebraicClosure ℚ` is *abstractly* isomorphic to the field
`algebraicClosure ℚ ℂ` of algebraic numbers inside `ℂ` (mathlib's relative
algebraic closure, which is an absolute algebraic closure of `ℚ` because `ℂ`
is algebraically closed — `algebraicClosure.isAlgClosure`), but not
canonically so: such an isomorphism IS the datum of an embedding `ℚ̄ ↪ ℂ`, and
there is no distinguished one.  **The choice is made explicit here**:
`ratAlgClosureEquiv` is `IsAlgClosure.equiv`, mathlib's arbitrary
(choice-dependent) isomorphism between two algebraic closures, and
`complexConj` is complex conjugation of `ℂ` — which preserves the algebraic
numbers because it is a `ℚ`-algebra map — transported along it.

Nothing downstream depends on which embedding is chosen: two embeddings
differ by an automorphism of `ℚ̄`, so the resulting complex conjugations are
conjugate in `Γ ℚ`, and both exported facts are conjugation-invariant (being
an involution is; the value of the cyclotomic character is because `ℤ_[p]ˣ`
is abelian, so the character is a class function).

## Proof of the character value

`complexConj` is an involution, so `χ_p(c)² = 1` in `ℤ_[p]ˣ`; `ℤ_[p]` is a
domain, so `χ_p(c) = ±1`.  It is not `+1`: at level one,
`cyclotomicCharacter.spec` would then say that `c` fixes a primitive `p`-th
root of unity `ζ`.  Transported into `ℂ`, `ζ` becomes a complex `p`-th root
of unity fixed by conjugation, hence real; a real `p`-th root of unity with
`p` ODD is `1` (`Odd.strictMono_pow` is injective on `ℝ`), contradicting
primitivity for `p > 1`.  Oddness of `p` is genuinely used: for `p = 2` the
level-one root of unity is `−1`, which conjugation does fix, and one has to
go to level two (`i ↦ −i`).

## Implementation note: the `ℚ`-algebra diamond

`Algebra ℚ (AlgebraicClosure ℚ)` and `Algebra ℚ ↥(algebraicClosure ℚ ℂ)` each
have two definitionally equal but syntactically different instances —
`AlgebraicClosure.instAlgebra` / `IntermediateField.algebra'` on one side and
`DivisionRing.toRatAlgebra` (every characteristic-zero division ring is a
`ℚ`-algebra) on the other.  Typeclass *search* in this file finds the latter,
while mathlib's `IsAlgClosure` instances — and mathlib's own `Γ ℚ` — are
stated for the former, so a bare `inferInstance` fails on
`IsAlgClosure ℚ (ℚᵃˡᵍ)`.  The two `attribute [local instance 100000]` lines
below re-prioritise the mathlib instances FOR THIS FILE ONLY, which makes
search agree with `Γ ℚ`.  Additionally the transported maps are packaged as
`RingEquiv`s rather than `AlgEquiv`s, so that no `Algebra` instance appears
in any exported type and the diamond cannot leak to consumers; the single
`AlgEquiv` that must exist, `complexConj` itself, is built by
`AlgEquiv.ofRingEquiv` (a ring map out of a characteristic-zero field is
automatically `ℚ`-linear, `Rat.subsingleton_ringHom`).
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
-- `IsAlgClosed ℂ`, the reason `algebraicClosure ℚ ℂ` is an algebraic closure
-- of `ℚ`; also `Complex.conjAe`.
public import Mathlib.Analysis.Complex.Polynomial.Basic
-- proof-only: `Odd.strictMono_pow`, the real-number step ruling out the
-- trivial value of the cyclotomic character.
import Mathlib.Algebra.Order.Ring.Basic

@[expose] public section

namespace GaloisRepresentation

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K

-- See the module docstring: this makes typeclass search pick the same
-- `ℚ`-algebra structures that mathlib's `IsAlgClosure` instances and `Γ ℚ`
-- are stated with, instead of `DivisionRing.toRatAlgebra`.
attribute [local instance 100000] AlgebraicClosure.instAlgebra
attribute [local instance 100000] IntermediateField.algebra'

/-- **The chosen embedding `ℚ̄ ↪ ℂ`**, presented as an isomorphism onto the
field of algebraic numbers inside `ℂ`.  This is the one arbitrary choice in
the construction of `complexConj`; see the module docstring.  Packaged as a
`RingEquiv` so that no `ℚ`-algebra instance appears in its type. -/
noncomputable def ratAlgClosureEquiv : ℚᵃˡᵍ ≃+* algebraicClosure ℚ ℂ :=
  (IsAlgClosure.equiv ℚ (ℚᵃˡᵍ) (algebraicClosure ℚ ℂ)).toRingEquiv

/-- Complex conjugation as a `ℚ`-algebra automorphism of `ℂ`: mathlib's
`Complex.conjAe` with its `ℝ`-linearity weakened to `ℚ`-linearity.  Weakening
is what makes it restrict to the algebraic numbers. -/
noncomputable def conjRat : ℂ ≃ₐ[ℚ] ℂ := Complex.conjAe.restrictScalars ℚ

/-- Complex conjugation restricted to the field of algebraic numbers inside
`ℂ`.  The restriction exists because conjugation is a `ℚ`-algebra map, hence
carries algebraic numbers to algebraic numbers
(`algebraicClosure.algEquivOfAlgEquiv`). -/
noncomputable def conjAlgebraic : algebraicClosure ℚ ℂ ≃+* algebraicClosure ℚ ℂ :=
  (algebraicClosure.algEquivOfAlgEquiv conjRat).toRingEquiv

@[simp] lemma coe_conjAlgebraic (y : algebraicClosure ℚ ℂ) :
    ((conjAlgebraic y : algebraicClosure ℚ ℂ) : ℂ) = starRingEnd ℂ (y : ℂ) := rfl

/-- **Complex conjugation of `ℚ̄`**, as a ring automorphism: conjugation of
`ℂ`, restricted to the algebraic numbers and transported along the chosen
embedding `ratAlgClosureEquiv`.  This is the shape `cyclotomicCharacter`
consumes; `complexConj` is its packaging as an element of `Γ ℚ`. -/
noncomputable def complexConjRingEquiv : ℚᵃˡᵍ ≃+* ℚᵃˡᵍ :=
  ratAlgClosureEquiv.trans (conjAlgebraic.trans ratAlgClosureEquiv.symm)

/-- **Complex conjugation as an element of the absolute Galois group of
`ℚ`.**  A ring automorphism of a characteristic-zero field is automatically a
`ℚ`-algebra automorphism, which is how `complexConjRingEquiv` is promoted. -/
noncomputable def complexConj : Γ ℚ :=
  AlgEquiv.ofRingEquiv (f := complexConjRingEquiv) (fun q => by
    have h1 : algebraMap ℚ (ℚᵃˡᵍ) q = (q : ℚᵃˡᵍ) := by simp
    rw [h1, map_ratCast])

@[simp] lemma complexConj_toRingEquiv :
    complexConj.toRingEquiv = complexConjRingEquiv := rfl

/-- Complex conjugation is an involution, pointwise. -/
lemma complexConjRingEquiv_involutive (x : ℚᵃˡᵍ) :
    complexConjRingEquiv (complexConjRingEquiv x) = x := by
  show ratAlgClosureEquiv.symm (conjAlgebraic (ratAlgClosureEquiv
    (ratAlgClosureEquiv.symm (conjAlgebraic (ratAlgClosureEquiv x))))) = x
  rw [RingEquiv.apply_symm_apply]
  have h : conjAlgebraic (conjAlgebraic (ratAlgClosureEquiv x)) = ratAlgClosureEquiv x :=
    Subtype.ext (by rw [coe_conjAlgebraic, coe_conjAlgebraic, Complex.conj_conj])
  rw [h, RingEquiv.symm_apply_apply]

/-- **Complex conjugation is an involution in `Γ ℚ`.**  This is the form the
oddness arguments consume: `ρ c * ρ c = 1` for any representation `ρ`. -/
lemma complexConj_mul_self : complexConj * complexConj = 1 := by
  apply AlgEquiv.ext
  intro x
  exact complexConjRingEquiv_involutive x

/-- The `RingEquiv` shadow of `complexConj_mul_self`. -/
lemma complexConjRingEquiv_mul_self :
    complexConjRingEquiv * complexConjRingEquiv = 1 := by
  ext x
  exact complexConjRingEquiv_involutive x

/-- **Complex conjugation moves every primitive `p`-th root of unity**, for
`p` an odd prime power `> 1`.  Under the chosen embedding a fixed root of
unity becomes a complex root of unity fixed by conjugation, hence real; a
real `p`-th root of unity with `p` odd is `1`, contradicting primitivity. -/
lemma complexConjRingEquiv_ne_of_isPrimitiveRoot {p : ℕ} (hp : Odd p) (hp1 : 1 < p)
    {ζ : ℚᵃˡᵍ} (hζ : IsPrimitiveRoot ζ p) :
    complexConjRingEquiv ζ ≠ ζ := by
  intro hfix
  set z : ℂ := ((ratAlgClosureEquiv ζ : algebraicClosure ℚ ℂ) : ℂ) with hzdef
  have hconj : starRingEnd ℂ z = z := by
    have h1 : conjAlgebraic (ratAlgClosureEquiv ζ) = ratAlgClosureEquiv ζ := by
      have h2 : ratAlgClosureEquiv (complexConjRingEquiv ζ) = ratAlgClosureEquiv ζ :=
        congrArg ratAlgClosureEquiv hfix
      rwa [show ratAlgClosureEquiv (complexConjRingEquiv ζ)
            = conjAlgebraic (ratAlgClosureEquiv ζ) from
          RingEquiv.apply_symm_apply _ _] at h2
    rw [hzdef, ← coe_conjAlgebraic, h1]
  have hzp : z ^ p = 1 := by
    have h1 : (ratAlgClosureEquiv ζ) ^ p = 1 := by
      rw [← map_pow, hζ.pow_eq_one, map_one]
    have h2 := congrArg (fun y : algebraicClosure ℚ ℂ => (y : ℂ)) h1
    simpa [hzdef] using h2
  have him : z.im = 0 := Complex.conj_eq_iff_im.mp hconj
  have hre : z = (z.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hrepow : z.re ^ p = 1 := by
    have h3 : ((z.re ^ p : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      push_cast
      rw [← hre, hzp]
    exact_mod_cast h3
  have hre1 : z.re = 1 :=
    (hp.strictMono_pow (R := ℝ)).injective (show z.re ^ p = (1 : ℝ) ^ p by simpa using hrepow)
  have hz1 : z = 1 := by rw [hre, hre1]; norm_num
  have h4 : ratAlgClosureEquiv ζ = 1 := by
    apply Subtype.ext
    rw [← hzdef, hz1]
    rfl
  have hζ1 : ζ = 1 := by
    have h5 := congrArg ratAlgClosureEquiv.symm h4
    rwa [RingEquiv.symm_apply_apply, map_one] at h5
  exact hζ.ne_one hp1 hζ1

/-- **The `p`-adic cyclotomic character sends complex conjugation to `−1`**,
for `p` an odd prime.  This is the arithmetic input of every oddness
argument: composed with `IsHardlyRamified.det` it says
`det (ρ complexConj) = −1`. -/
theorem cyclotomicCharacter_complexConj (p : ℕ) [Fact p.Prime] (hp : Odd p) :
    cyclotomicCharacter (ℚᵃˡᵍ) p complexConj.toRingEquiv = -1 := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  haveI : NeZero ((p : ℕ) : ℚ) :=
    ⟨by simpa using (Nat.cast_ne_zero (R := ℚ)).mpr (Fact.out : p.Prime).ne_zero⟩
  haveI : Fact (1 < p ^ 1) := ⟨by simpa using hp1⟩
  rw [complexConj_toRingEquiv]
  set u := cyclotomicCharacter (ℚᵃˡᵍ) p complexConjRingEquiv with hu
  -- `u` is a square root of `1` because complex conjugation is an involution
  have husq : u * u = 1 := by
    rw [hu, ← map_mul, complexConjRingEquiv_mul_self, map_one]
  -- hence `u = ±1`, `ℤ_[p]` being a domain
  have hval : (u : ℤ_[p]) = 1 ∨ (u : ℤ_[p]) = -1 := by
    have h0 : ((u : ℤ_[p]) - 1) * ((u : ℤ_[p]) + 1) = 0 := by
      have h1 : (u : ℤ_[p]) * (u : ℤ_[p]) = 1 := by
        rw [← Units.val_mul, husq, Units.val_one]
      linear_combination h1
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  -- and it is not `+1`: complex conjugation moves a primitive `p`-th root of unity
  have hne : (u : ℤ_[p]) ≠ 1 := by
    intro h1
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (ℚᵃˡᵍ) p
    have hspec := cyclotomicCharacter.spec (L := ℚᵃˡᵍ) p (n := 1)
      complexConjRingEquiv ζ (by rw [pow_one]; exact hζ.pow_eq_one)
    rw [← hu, h1, map_one, ZMod.val_one, pow_one] at hspec
    exact complexConjRingEquiv_ne_of_isPrimitiveRoot hp hp1 hζ hspec
  refine Units.ext ?_
  simpa using hval.resolve_left hne

end GaloisRepresentation
