/-
PotentiallyGoodModel.lean — own work for the Fermat project.

HOISTED VERBATIM out of `Fermat/FLT/FreyCurve/MazurTorsion.lean` on
2026-07-28 (the block that ran from the docstring of
`WeierstrassCurve.PotentiallyGoodModel` to
`WeierstrassCurve.exists_potentiallyGoodModel_of_jIntegral`, inclusive).

WHY THE MOVE.  Lean has no forward references, and the potentially-good
reduction datum was declared ~700 lines BELOW the Néron–Ogg–Shafarevich
leaves of `MazurTorsion.lean` that need it — in particular
`WeierstrassCurve.map_pow_twentyFour_eq_self_of_potentiallyGoodModel` and
`WeierstrassCurve.isogenyCharacter_pow_twentyFour_eq_one_of_padicValRat_j_nonneg`.
Hoisting it into its own module is the same repair the Minkowski block
received (`Fermat.FLT.GaloisRepresentation.MinkowskiUnramified`), and it is
what the `B₀¹` docstring in `MazurTorsion.lean` prescribed.

NOTHING WAS CHANGED.  The declarations, their docstrings and their proofs
are byte-identical to what stood in `MazurTorsion.lean`; only their file
changed.  The import list below is `MazurTorsion.lean`'s own, with every
entry made `public` so that the moved signatures see exactly the
environment they were elaborated in.  Consumers keep working unchanged
because `MazurTorsion.lean` now `public import`s this module.
-/
module

public import Fermat.FLT.FreyCurve.Basic
public import Fermat.FLT.EllipticCurve.MordellWeil
public import Fermat.FLT.EllipticCurve.Torsion
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
public import Fermat.FLT.EllipticCurve.PhiPsiCoprime
public import Fermat.FLT.EllipticCurve.Velu
public import Fermat.FLT.EllipticCurve.Isogeny
public import Fermat.FLT.EllipticCurve.IsogenyTrace
public import Fermat.FLT.GaloisRepresentation.Chebotarev
public import Fermat.FLT.EllipticCurve.WeilPairing
public import Fermat.FLT.EllipticCurve.HasseBound
public import Fermat.FLT.GaloisRepresentation.HardlyRamified.FreyConditions
public import Fermat.FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
public import Fermat.FLT.GaloisRepresentation.SubQuotCharacter
public import Fermat.FLT.GaloisRepresentation.MinkowskiUnramified
public import Fermat.FLT.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Fermat.FLT.KnownIn1980s.EllipticCurves.PointReduction
public import Fermat.FLT.EllipticCurve.TorsionReduction
public import Fermat.FLT.EllipticCurve.KernelPolynomial
public import Fermat.FLT.EllipticCurve.GenusOneKernelPolynomials
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.NumberTheory.NumberField.ExistsRamified
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Fermat.FLT.Deformations.RepresentationTheory.LocalInertiaFixedField
public import Fermat.FLT.DedekindDomain.AdicValuation
public import Mathlib.Data.Nat.Factorization.PrimePow
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.Data.Rat.Lemmas
public import Fermat.FLT.KnownIn1980s.EllipticCurves.QuadraticTwists.SplitMultiplicativeReduction
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.NumberTheory.FLT.Four
public import Mathlib.NumberTheory.FLT.Three
public import Fermat.FLT.EllipticCurve.TorsionCharP
public import Fermat.FLT.ModularCurve.HyperellipticJacobian
public import Fermat.FLT.FreyCurve.QuarticDescent
public import Fermat.FLT.ModularCurve.X0
public import Fermat.FLT.ModularCurve.X1
public import Fermat.FLT.FreyCurve.TateNormalForm

@[expose] public section

open WeierstrassCurve WeierstrassCurve.Affine

/-- **A potentially-good-reduction datum for `E` at `q`, with residue degree
one** (interface opened 2026-07-27 while decomposing
`exists_frobeniusAut_of_potentiallyGoodReduction` below into its ARITHMETIC and
its GALOIS halves).

THE CONTENT. A `PotentiallyGoodModel E q` is exactly the sentence "`E` acquires
good reduction over a finite extension of `ℚ` at a prime above `q` whose residue
field is the PRIME field `𝔽_q`", written as data:

* `K` — a number field (`FiniteDimensional ℚ K` is field `instFin`);
* `R` — a DVR with fraction field `K`, i.e. the local ring of a prime of `K`.
  No hypothesis says `R` lies above `q`: `resEquiv` already forces it, since a
  residue field of characteristic `q` forces `q ∈ 𝔪`;
* `resEquiv : ResidueField R ≃+* ZMod q` — **this is where TOTAL RAMIFICATION
  is encoded**, exactly as `TameGoodModel.res` encodes it in
  `EllipticCurve/TorsionReduction.lean`: landing in the PRIME field rather than
  in an extension of it says the residue degree is `1`, hence
  `e = [K_𝔮 : ℚ_q]`;
* `V` — the good model, with mathlib's `HasGoodReduction R` (which extends
  `IsMinimal R`, so `V` is a minimal integral equation whose discriminant is a
  unit), and `V_eq` pinning `V` as a model OF `E` rather than an unrelated
  curve.

WHY THIS IS THE RIGHT CUT, and it is the standing rule that a cut may need a
theory only STATED rather than PROVEN. The old single leaf mixed two
difficulties that share no technique:

1. *Arithmetic*: `0 ≤ v_q(j)` ⟹ such a datum exists. Reduction theory of
   Weierstrass equations, Kummer/wild extensions of `ℚ_q`, and a Krasner-style
   descent to a number field. Nothing Galois-theoretic appears.
2. *Galois*: given the datum, `ρ(σ_q)` is an automorphism composed with the
   `q`-power Frobenius of the reduction. Néron–Ogg–Shafarevich and Serre–Tate.
   No reduction theory appears — the model is handed over.

They are now `exists_potentiallyGoodModel_of_jIntegral` and
`exists_frobeniusAut_of_potentiallyGoodModel`, separately ownable.

RELATION TO `TameGoodModel` (`EllipticCurve/TorsionReduction.lean`), whose
existence leaf `exists_tameGoodModel_of_jIntegral` is ALREADY OPEN and being
worked: the two structures say the same thing in different vocabularies —
`TameGoodModel` carries a `ValuationSubring L` with a residue map to `ZMod ℓ`
and an abstract injection of points, this one carries a DVR with mathlib's
`HasGoodReduction`. Neither subsumes the other as written and NEITHER SHOULD BE
DUPLICATED: whoever proves one should expect to write the (routine, but not
free) translation rather than reprove the arithmetic. The two differences that
matter are that `TameGoodModel` assumes `5 ≤ ℓ` at its producer — so it does
NOT cover `q = 3`, which the consumers of this file need — and that it does not
ask `L` to be a NUMBER field, which is what makes `Γ K ≤ Γ ℚ` available to the
Galois half here.

NOT VACUOUS, and `V_eq` is what prevents it: `V` is pinned to `C • E_K`, so no
choice of an unrelated good curve satisfies the structure. `resEquiv` cannot be
degenerate either — `ZMod q` is a field of `q` elements, so a residue field of
any other size (in particular any nontrivial extension of `𝔽_q`, which is what
a prime of residue degree `> 1` would give) simply admits no such equivalence.
-/
structure WeierstrassCurve.PotentiallyGoodModel (E : WeierstrassCurve ℚ)
    (q : ℕ) [Fact q.Prime] where
  /-- The number field over which `E` acquires good reduction. -/
  K : Type
  [instField : Field K]
  [instDec : DecidableEq K]
  [instAlgebra : Algebra ℚ K]
  [instFin : FiniteDimensional ℚ K]
  /-- The local ring of the chosen prime of `K` above `q`. -/
  R : Type
  [instCommRing : CommRing R]
  [instDomain : IsDomain R]
  [instDVR : IsDiscreteValuationRing R]
  [instAlgRK : Algebra R K]
  [instFrac : IsFractionRing R K]
  /-- **Residue degree one.** Landing in the PRIME field `ZMod q` rather than in
  an extension of it is where total ramification is encoded. -/
  resEquiv : IsLocalRing.ResidueField R ≃+* ZMod q
  /-- The good model itself. -/
  V : WeierstrassCurve K
  [V_elliptic : V.IsElliptic]
  [V_good : V.HasGoodReduction R]
  /-- The variable change carrying `E` over `K` to that model. -/
  C : WeierstrassCurve.VariableChange K
  /-- `V` is genuinely a model of `E`, not an unrelated curve. -/
  V_eq : V = C • (E.baseChange K)

attribute [instance] WeierstrassCurve.PotentiallyGoodModel.instField
  WeierstrassCurve.PotentiallyGoodModel.instDec
  WeierstrassCurve.PotentiallyGoodModel.instAlgebra
  WeierstrassCurve.PotentiallyGoodModel.instFin
  WeierstrassCurve.PotentiallyGoodModel.instCommRing
  WeierstrassCurve.PotentiallyGoodModel.instDomain
  WeierstrassCurve.PotentiallyGoodModel.instDVR
  WeierstrassCurve.PotentiallyGoodModel.instAlgRK
  WeierstrassCurve.PotentiallyGoodModel.instFrac
  WeierstrassCurve.PotentiallyGoodModel.V_elliptic
  WeierstrassCurve.PotentiallyGoodModel.V_good

/-! ### The tame valuation subring is a DVR

`PotentiallyGoodModel` asks for a DISCRETE VALUATION RING, because that is what
mathlib's `HasGoodReduction` (and the already-proven
`torsion_unramified_of_good_reduction` that the Galois half consumes) is stated
over. `TameBaseAux.tameSubring q` — the valuation subring of `ℚ(q^{1/12})` above
`q`, built by Chevalley extension in `EllipticCurve/TorsionReduction.lean` — is
only a `ValuationSubring` there, and Chevalley says nothing about discreteness.
The four declarations below upgrade it, using the SAME power-basis input that
`TameBaseAux.exists_tameResidueHom` uses: `exists_repr` writes every `x : L` as
`∑_{i<12} c i · π^i`, and the twelve exponents `12·v_q(c i) + i` are pairwise
distinct mod `12`, so `Valuation.map_sum_eq_of_lt` computes `v x` exactly and the
value group is generated by `v(π)`. -/

/-- **Every nonzero element of `L = ℚ(ℓ^{1/12})` has valuation an integer power of
`v(π)`** (PROVEN 2026-07-27). This is `TameBaseAux.padicValRat_coeff_nonneg`'s
unique-minimum computation, kept rather than discarded: that lemma only needed the
minimum to be `≥ 0`, this one needs its VALUE, which is what makes the value group
`ℤ` and hence the subring discrete. -/
theorem WeierstrassCurve.TameBaseAux.exists_valuation_eq_zpow (ℓ : ℕ) [Fact ℓ.Prime]
    {x : AdjoinRoot (TameBaseAux.qpoly ℓ)} (hx : x ≠ 0) :
    ∃ n : ℤ, (TameBaseAux.tameSubring ℓ).valuation x
      = (TameBaseAux.tameSubring ℓ).valuation (TameBaseAux.unif ℓ) ^ n := by
  classical
  obtain ⟨c, hc⟩ := TameBaseAux.exists_repr ℓ x
  set e : ℕ → ℤ := fun k => 12 * padicValRat ℓ (c k) + (k : ℤ) with he
  set S : Finset ℕ := (Finset.range 12).filter (fun k => c k ≠ 0) with hS
  have hmemS : ∀ k, k ∈ S ↔ (k < 12 ∧ c k ≠ 0) := by
    intro k; simp [hS, Finset.mem_filter, Finset.mem_range]
  have hSne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    refine hx ?_
    rw [hc]
    refine Finset.sum_eq_zero fun k hk => ?_
    have hck : c k = 0 := by
      by_contra hc0
      have hkS : k ∈ S := (hmemS k).mpr ⟨Finset.mem_range.mp hk, hc0⟩
      rw [h] at hkS
      exact absurd hkS (Finset.notMem_empty k)
    simp [hck]
  obtain ⟨j, hjS, hj⟩ := S.exists_min_image e hSne
  obtain ⟨hj12, hcj⟩ := (hmemS j).mp hjS
  have hsum : ∑ k ∈ S, TameBaseAux.ofQ ℓ (c k) * TameBaseAux.unif ℓ ^ k
      = ∑ k ∈ Finset.range 12, TameBaseAux.ofQ ℓ (c k) * TameBaseAux.unif ℓ ^ k := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro k hk hkn
    have hck : c k = 0 := by
      by_contra h
      exact hkn ((hmemS k).mpr ⟨Finset.mem_range.mp hk, h⟩)
    simp [hck]
  have hlt : ∀ k ∈ S \ {j},
      (TameBaseAux.tameSubring ℓ).valuation
          (TameBaseAux.ofQ ℓ (c k) * TameBaseAux.unif ℓ ^ k)
        < (TameBaseAux.tameSubring ℓ).valuation
          (TameBaseAux.ofQ ℓ (c j) * TameBaseAux.unif ℓ ^ j) := by
    intro k hk
    obtain ⟨hkS, hkj⟩ := Finset.mem_sdiff.mp hk
    obtain ⟨hk12, hck⟩ := (hmemS k).mp hkS
    have hejk : e j < e k := by
      rcases lt_or_eq_of_le (hj k hkS) with h | h
      · exact h
      · exfalso
        have hkj' : k ≠ j := by simpa using hkj
        simp only [he] at h
        omega
    rw [TameBaseAux.valuation_term ℓ hck k, TameBaseAux.valuation_term ℓ hcj j]
    exact (TameBaseAux.zpow_lt_zpow_iff_of_lt_one (TameBaseAux.valuation_unif_ne_zero ℓ)
      (TameBaseAux.valuation_unif_lt_one ℓ) _ _).mpr hejk
  refine ⟨e j, ?_⟩
  rw [hc, ← hsum, Valuation.map_sum_eq_of_lt _ hjS hlt, TameBaseAux.valuation_term ℓ hcj j]

/-- The uniformizer lies in the tame valuation subring. -/
theorem WeierstrassCurve.TameBaseAux.unif_mem (ℓ : ℕ) [Fact ℓ.Prime] :
    TameBaseAux.unif ℓ ∈ TameBaseAux.tameSubring ℓ :=
  ValuationSubring.mem_of_valuation_le_one _ _ (TameBaseAux.valuation_unif_lt_one ℓ).le

/-- `n ↦ v(π)^n` is injective, because `v(π) < 1`. -/
theorem WeierstrassCurve.TameBaseAux.valuation_zpow_inj (ℓ : ℕ) [Fact ℓ.Prime] {m n : ℤ}
    (h : (TameBaseAux.tameSubring ℓ).valuation (TameBaseAux.unif ℓ) ^ m
      = (TameBaseAux.tameSubring ℓ).valuation (TameBaseAux.unif ℓ) ^ n) : m = n := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h2 := (TameBaseAux.zpow_lt_zpow_iff_of_lt_one (TameBaseAux.valuation_unif_ne_zero ℓ)
      (TameBaseAux.valuation_unif_lt_one ℓ) m n).mpr hlt
    rw [h] at h2; exact lt_irrefl _ h2
  · have h2 := (TameBaseAux.zpow_lt_zpow_iff_of_lt_one (TameBaseAux.valuation_unif_ne_zero ℓ)
      (TameBaseAux.valuation_unif_lt_one ℓ) n m).mpr hlt
    rw [h] at h2; exact lt_irrefl _ h2

/-- Every nonzero element of `A` has valuation `v(π)^n` for a NATURAL `n`. -/
theorem WeierstrassCurve.TameBaseAux.exists_valuation_eq_pow (ℓ : ℕ) [Fact ℓ.Prime]
    {x : TameBaseAux.tameSubring ℓ} (hx : x ≠ 0) :
    ∃ n : ℕ, (TameBaseAux.tameSubring ℓ).valuation (x : AdjoinRoot (TameBaseAux.qpoly ℓ))
      = (TameBaseAux.tameSubring ℓ).valuation (TameBaseAux.unif ℓ) ^ (n : ℤ) := by
  obtain ⟨n, hn⟩ := TameBaseAux.exists_valuation_eq_zpow ℓ
    (x := (x : AdjoinRoot (TameBaseAux.qpoly ℓ))) (by simpa using hx)
  have hle : (TameBaseAux.tameSubring ℓ).valuation (TameBaseAux.unif ℓ) ^ n ≤ 1 := by
    rw [← hn]; exact ValuationSubring.valuation_le_one _ x
  have hn0 : 0 ≤ n := (TameBaseAux.zpow_le_one_iff_of_lt_one
    (TameBaseAux.valuation_unif_ne_zero ℓ) (TameBaseAux.valuation_unif_lt_one ℓ) _).mp hle
  exact ⟨n.toNat, by rwa [Int.toNat_of_nonneg hn0]⟩

/-- **Every nonzero element of `A` is a unit times a power of `π`** — the hypothesis of
`IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization`. -/
theorem WeierstrassCurve.TameBaseAux.tameSubring_hasUnitMulPow (ℓ : ℕ) [Fact ℓ.Prime] :
    IsDiscreteValuationRing.HasUnitMulPowIrreducibleFactorization
      (TameBaseAux.tameSubring ℓ) := by
  classical
  refine ⟨⟨TameBaseAux.unif ℓ, TameBaseAux.unif_mem ℓ⟩, ⟨?_, ?_⟩, ?_⟩
  · -- `π` is not a unit, because `v(π) < 1`
    intro hu
    rw [ValuationSubring.valuation_eq_one_iff] at hu
    exact absurd hu (TameBaseAux.valuation_unif_lt_one ℓ).ne
  · -- irreducibility: `v(π) = v(a)·v(b)` with both factors of valuation `≤ v(π)`
    rintro a b hab
    by_contra hcon
    simp only [not_or] at hcon
    obtain ⟨ha, hb⟩ := hcon
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact (TameBaseAux.unif_ne_zero ℓ) (by simpa [Subtype.ext_iff] using hab)
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact (TameBaseAux.unif_ne_zero ℓ) (by simpa [Subtype.ext_iff] using hab)
    obtain ⟨m, hm⟩ := TameBaseAux.exists_valuation_eq_pow ℓ ha0
    obtain ⟨k, hk⟩ := TameBaseAux.exists_valuation_eq_pow ℓ hb0
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · exact absurd (by rw [ValuationSubring.valuation_eq_one_iff, hm, h]; simp) ha
      · exact h
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · exact absurd (by rw [ValuationSubring.valuation_eq_one_iff, hk, h]; simp) hb
      · exact h
    have hval : (TameBaseAux.tameSubring ℓ).valuation (TameBaseAux.unif ℓ)
        = (TameBaseAux.tameSubring ℓ).valuation (TameBaseAux.unif ℓ) ^ ((m : ℤ) + k) := by
      have hcoe : TameBaseAux.unif ℓ = (a : AdjoinRoot (TameBaseAux.qpoly ℓ))
          * (b : AdjoinRoot (TameBaseAux.qpoly ℓ)) := by
        have := congrArg
          (fun z : TameBaseAux.tameSubring ℓ => (z : AdjoinRoot (TameBaseAux.qpoly ℓ))) hab
        simpa using this
      rw [zpow_add₀ (TameBaseAux.valuation_unif_ne_zero ℓ), ← hm, ← hk, ← map_mul, ← hcoe]
    have := TameBaseAux.valuation_zpow_inj ℓ (m := 1) (n := (m : ℤ) + k)
      (by rw [zpow_one]; exact hval)
    omega
  · -- and every nonzero element is an associate of a power of `π`
    intro x hx
    obtain ⟨n, hn⟩ := TameBaseAux.exists_valuation_eq_pow ℓ hx
    refine ⟨n, ?_⟩
    have hv : (TameBaseAux.tameSubring ℓ).valuation
        (((⟨TameBaseAux.unif ℓ, TameBaseAux.unif_mem ℓ⟩ : TameBaseAux.tameSubring ℓ) ^ n :
            TameBaseAux.tameSubring ℓ) : AdjoinRoot (TameBaseAux.qpoly ℓ))
        = (TameBaseAux.tameSubring ℓ).valuation
          (x : AdjoinRoot (TameBaseAux.qpoly ℓ)) := by
      rw [hn]
      push_cast
      rw [map_pow, zpow_natCast]
    obtain ⟨u, hu⟩ := (ValuationSubring.valuation_eq_iff _ _ _).mp hv.symm
    exact ⟨u, Subtype.ext (by simpa [mul_comm] using hu)⟩

/-- **`A = ℤ_(ℓ)[ℓ^{1/12}]` is a discrete valuation ring** (PROVEN 2026-07-27). This is
what lets `PotentiallyGoodModel` be phrased with a DVR — which is not a stylistic
choice: `torsion_unramified_of_good_reduction`, which the Galois half consumes, is
stated over a DVR, and mathlib's `HasGoodReduction` needs one to define `IsMinimal`
at all. -/
instance WeierstrassCurve.TameBaseAux.instIsDiscreteValuationRingTameSubring
    (ℓ : ℕ) [Fact ℓ.Prime] : IsDiscreteValuationRing (TameBaseAux.tameSubring ℓ) :=
  IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    (TameBaseAux.tameSubring_hasUnitMulPow ℓ)

/-- **`ℚ` has a unique ring hom into a field**, so whichever `Algebra ℚ`-instance
elaboration happens to pick on `L = ℚ(ℓ^{1/12})`, its structure map is `ofQ`. This is the
clean way around the instance clash that `TameBaseAux.ofQ`'s docstring records: rather
than pinning one instance with a `letI` (which loses to the `Module ℚ` found through
`Submodule`), note that the two can only differ by a `Subsingleton.elim`. -/
theorem WeierstrassCurve.TameBaseAux.algebraMap_eq_ofQ (ℓ : ℕ) [Fact ℓ.Prime] :
    (algebraMap ℚ (AdjoinRoot (TameBaseAux.qpoly ℓ))) = TameBaseAux.ofQ ℓ :=
  Subsingleton.elim _ _

/-- `ℓ`-integrality of a rational is exactly `ℓ ∤ den`. The argument is the one inside
`TameBaseAux.exists_intCast_sub_valuation_lt_one`, isolated so that both phrasings of
`j`-integrality — `0 ≤ padicValRat q j` here, `¬ q ∣ j.den` in
`padicValRat_Δ_le_of_jIntegral` — can be used interchangeably. -/
theorem WeierstrassCurve.TameBaseAux.not_dvd_den_of_padicValRat_nonneg {ℓ : ℕ}
    [hℓ : Fact ℓ.Prime] {x : ℚ} (hx : 0 ≤ padicValRat ℓ x) : ¬ (ℓ ∣ x.den) := by
  intro hdvd
  have hd1 : 1 ≤ padicValNat ℓ x.den := one_le_padicValNat_of_dvd x.den_nz hdvd
  have hnum1 : 1 ≤ padicValInt ℓ x.num := by
    have h := hx; rw [padicValRat_def] at h; omega
  have hnum0 : ℓ ∣ x.num.natAbs := by
    by_contra h
    have : padicValInt ℓ x.num = 0 := padicValNat.eq_zero_of_not_dvd h
    omega
  have h1 : ℓ = 1 := Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.coprime_dvd_left hnum0 x.reduced) hdvd
  exact hℓ.out.one_lt.ne' h1

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum IsLocalRing in
/-- **An integral Weierstrass equation with unit discriminant is already minimal**
(PROVEN 2026-07-27). `valuation_Δ_aux` takes values in `{v // v ≤ 1}` by construction,
so an equation attaining `1` attains the maximum and no minimisation is needed. This is
the `Δ`-analogue of the project's `isMinimal_of_valuation_c₄_eq_one`
(`Fermat/FLT/Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean`) and is strictly
easier — good reduction is the one case where minimality is free. -/
theorem WeierstrassCurve.isMinimal_of_valuation_Δ_eq_one {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) [IsIntegral R W]
    (hΔ : valuation K (maximalIdeal R) W.Δ = 1) : IsMinimal R W := by
  refine ⟨⟨by simpa using ‹IsIntegral R W›, ?_⟩⟩
  intro C hC _
  simp only [one_smul, ← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral R (C • W),
    valuation_Δ_aux_eq_of_isIntegral R W, hΔ]
  simpa [← integralModel_Δ_eq R (C • W)] using valuation_le_one (maximalIdeal R) _

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum IsLocalRing in
/-- **An integral Weierstrass equation whose discriminant is a UNIT of `R` has good
reduction** (PROVEN 2026-07-27). Both fields of mathlib's `HasGoodReduction` come out of
the single hypothesis: `valuation_eq_one_iff_notMem` turns "unit of `R`" into
`valuation Δ = 1`, which is the `goodReduction` field, and minimality is then free by the
lemma above. This is the bridge that lets any explicit scaling argument — the tame one
below, and whatever the wild `q = 3` case eventually uses — hand over a
`PotentiallyGoodModel` without ever touching `IsMinimal`. -/
theorem WeierstrassCurve.hasGoodReduction_of_isUnit_Δ {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) [IsIntegral R W] {r : R} (hr : algebraMap R K r = W.Δ)
    (hu : IsUnit r) : W.HasGoodReduction R := by
  have hΔ : valuation K (maximalIdeal R) W.Δ = 1 := by
    rw [← hr]
    refine (valuation_eq_one_iff_notMem (K := K) (v := maximalIdeal R)).mpr ?_
    simpa [IsDiscreteValuationRing.maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      using hu
  exact { toIsMinimal := WeierstrassCurve.isMinimal_of_valuation_Δ_eq_one W hΔ,
          goodReduction := hΔ }

/-- **A local ring hom onto `ZMod q` identifies the residue field with `ZMod q`**
(PROVEN 2026-07-27). Injectivity is automatic (a ring hom out of a field), and
surjectivity is automatic too (`ZMod q` is generated by `1`), so `IsLocalHom` alone
upgrades `TameBaseAux.exists_tameResidueHom`'s hom into the `resEquiv` that
`PotentiallyGoodModel` asks for. Residue degree one is thereby carried across from the
`TameGoodModel` vocabulary to this one at no mathematical cost. -/
noncomputable def WeierstrassCurve.residueFieldEquivZModOfLocalHom {A : Type*} [CommRing A]
    [IsLocalRing A] {q : ℕ} [Fact q.Prime] (f : A →+* ZMod q) [IsLocalHom f] :
    IsLocalRing.ResidueField A ≃+* ZMod q := by
  have hker : ∀ a ∈ IsLocalRing.maximalIdeal A, f a = 0 := by
    intro a ha
    by_contra h
    exact (IsLocalRing.mem_maximalIdeal a).mp ha
      (isUnit_of_map_unit f a (isUnit_iff_ne_zero.mpr h))
  refine RingEquiv.ofBijective (Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) f hker)
    ⟨RingHom.injective _, ?_⟩
  intro y
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective (n := q) y
  exact ⟨(n : IsLocalRing.ResidueField A), by simp⟩

/-- **The assembly: a variable change with integral coefficients and INVERTIBLE
discriminant produces the datum** (PROVEN 2026-07-27). Everything about
`PotentiallyGoodModel` that is not arithmetic lives here, and nothing arithmetic does:
the caller supplies the number field, the DVR, the residue identification and the
variable change, and this turns them into the structure.

**THIS IS THE ENTRY POINT FOR THE WILD CASE `q = 3`.** Whoever attacks
`exists_potentiallyGoodModel_of_jIntegral_three` should aim at exactly these six
hypotheses over whatever base that case needs; no part of the `HasGoodReduction` /
`IsMinimal` bookkeeping has to be redone.

Note `Δ ∈ A` is NOT a hypothesis — it follows from the five coefficient memberships,
since `Δ` is a polynomial in them — and `Δ ≠ 0` is not either, since `C • E_K` is
elliptic whenever `E` is. Only INVERTIBILITY of `Δ` in `A` is a real condition, and it
is the whole content of "good reduction". -/
theorem WeierstrassCurve.exists_potentiallyGoodModel_of_integral
    {q : ℕ} [Fact q.Prime] (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (K : Type) [Field K] [DecidableEq K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    (A : ValuationSubring K) [IsDiscreteValuationRing A]
    (resEquiv : IsLocalRing.ResidueField A ≃+* ZMod q)
    (C : VariableChange K)
    (ha₁ : (C • E.baseChange K).a₁ ∈ A) (ha₂ : (C • E.baseChange K).a₂ ∈ A)
    (ha₃ : (C • E.baseChange K).a₃ ∈ A) (ha₄ : (C • E.baseChange K).a₄ ∈ A)
    (ha₆ : (C • E.baseChange K).a₆ ∈ A)
    (haΔinv : ((C • E.baseChange K).Δ)⁻¹ ∈ A) :
    Nonempty (E.PotentiallyGoodModel q) := by
  classical
  set V : WeierstrassCurve K := C • (E.baseChange K) with hV
  haveI : (E.baseChange K).IsElliptic :=
    inferInstanceAs (E.map (algebraMap ℚ K)).IsElliptic
  haveI hVell : V.IsElliptic := by rw [hV]; infer_instance
  have hVΔne : V.Δ ≠ 0 := V.isUnit_Δ.ne_zero
  set ι : A →+* K := SubringClass.subtype A with hι
  set VA : WeierstrassCurve A :=
    ⟨⟨V.a₁, ha₁⟩, ⟨V.a₂, ha₂⟩, ⟨V.a₃, ha₃⟩, ⟨V.a₄, ha₄⟩, ⟨V.a₆, ha₆⟩⟩ with hVA
  have hVAmap : VA.map ι = V := rfl
  have hVAΔ : (VA.Δ : K) = V.Δ := by rw [← hVAmap, map_Δ]; rfl
  have hVAΔunit : IsUnit VA.Δ := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨(V.Δ)⁻¹, haΔinv⟩, Subtype.ext ?_⟩
    show (VA.Δ : K) * (V.Δ)⁻¹ = 1
    rw [hVAΔ]
    exact mul_inv_cancel₀ hVΔne
  haveI hVint : IsIntegral A V := ⟨VA, hVAmap.symm⟩
  haveI hVgood : V.HasGoodReduction A :=
    WeierstrassCurve.hasGoodReduction_of_isUnit_Δ V (r := VA.Δ) hVAΔ hVAΔunit
  exact ⟨{ K := K
           R := A
           resEquiv := resEquiv
           V := V
           C := C
           V_eq := hV }⟩

/-- **The tame scaling** (PROVEN 2026-07-27): over a base of ramification index `12`,
a curve already in short Weierstrass form needs only the single variable change
`u = π^{v_q(Δ)}`, `r = s = t = 0`.

This is the same computation as `exists_tameGoodModel_of_isShortNF`
(`EllipticCurve/TorsionReduction.lean`) — deliberately so, and see
`PotentiallyGoodModel`'s docstring, which asks that the two structures NOT be
duplicated. What is not duplicated is the arithmetic: the base, the residue-degree-one
theorem and the two valuation inequalities are all TAKEN from
`EllipticCurve/TorsionReduction.lean`, and this file adds only the DVR upgrade and the
`HasGoodReduction` translation. Rewriting the eight-line scaling is what the
`TameGoodModel` docstring calls "the routine, but not free, translation"; the reason it
cannot be avoided is that `TameGoodModel` is stated with a `ValuationSubring` and an
abstract `IsReductionAlong`, and exposes neither the discreteness nor the
finite-dimensionality of its field, so its conclusion cannot be transported.

    v(V.a₄) = −4d + 12a ≥ 0  ⟺  3a ≥ d      (the `j`-integrality hypothesis)
    v(V.a₆) = −6d + 12b ≥ 0  ⟺  2b ≥ d      (free, by ultrametricity)
    v(V.Δ)  = −12d + 12d = 0                (always, by the CHOICE of `d`) -/
theorem WeierstrassCurve.exists_potentiallyGoodModel_of_tameBase
    {q : ℕ} [Fact q.Prime] (W : WeierstrassCurve ℚ) [W.IsElliptic] [W.IsShortNF]
    (L : Type) [Field L] [DecidableEq L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    (A : ValuationSubring L) [IsDiscreteValuationRing A]
    (resEquiv : IsLocalRing.ResidueField A ≃+* ZMod q)
    (π : L) (hπ0 : π ≠ 0)
    (hmem : ∀ (m : ℤ) {x : ℚ}, x ≠ 0 →
      (π ^ m * algebraMap ℚ L x ∈ A ↔ 0 ≤ m + 12 * padicValRat q x))
    (h4 : W.a₄ ≠ 0 → padicValRat q W.Δ ≤ 3 * padicValRat q W.a₄)
    (h6 : W.a₆ ≠ 0 → padicValRat q W.Δ ≤ 2 * padicValRat q W.a₆) :
    Nonempty (W.PotentiallyGoodModel q) := by
  classical
  have hΔ0 : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  set d : ℤ := padicValRat q W.Δ with hd
  have hπd : (π ^ d) ≠ 0 := zpow_ne_zero _ hπ0
  set u : Lˣ := Units.mk0 (π ^ d) hπd with hu
  set C : VariableChange L := ⟨u, 0, 0, 0⟩ with hC
  set V : WeierstrassCurve L := C • (W.baseChange L) with hV
  have hui : ∀ k : ℕ, ((u⁻¹ : Lˣ) : L) ^ k = π ^ (-(k : ℤ) * d) := by
    intro k
    rw [hu]
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [← zpow_natCast (π ^ d)⁻¹ k, ← zpow_neg, ← zpow_mul]
    ring_nf
  have hVa₁ : V.a₁ = 0 := by
    rw [hV, variableChange_a₁, hC]; simp [WeierstrassCurve.baseChange]
  have hVa₂ : V.a₂ = 0 := by
    rw [hV, variableChange_a₂, hC]; simp [WeierstrassCurve.baseChange]
  have hVa₃ : V.a₃ = 0 := by
    rw [hV, variableChange_a₃, hC]; simp [WeierstrassCurve.baseChange]
  have hVa₄ : V.a₄ = π ^ (-4 * d) * algebraMap ℚ L W.a₄ := by
    rw [hV, variableChange_a₄, hC]
    simp only [WeierstrassCurve.baseChange, map_a₁, map_a₂, map_a₃, map_a₄,
      W.a₁_of_isShortNF, W.a₂_of_isShortNF, W.a₃_of_isShortNF, map_zero]
    rw [hui 4]; push_cast; ring
  have hVa₆ : V.a₆ = π ^ (-6 * d) * algebraMap ℚ L W.a₆ := by
    rw [hV, variableChange_a₆, hC]
    simp only [WeierstrassCurve.baseChange, map_a₂, map_a₃, map_a₄, map_a₆]
    rw [hui 6]; push_cast; ring
  have hVΔ : V.Δ = π ^ (-12 * d) * algebraMap ℚ L W.Δ := by
    rw [hV, variableChange_Δ, hC]
    simp only [WeierstrassCurve.baseChange, map_Δ]
    rw [hui 12]; push_cast; ring
  have hzero : (0 : L) ∈ A := zero_mem _
  refine WeierstrassCurve.exists_potentiallyGoodModel_of_integral W L A resEquiv C
    ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← hV, hVa₁]; exact hzero
  · rw [← hV, hVa₂]; exact hzero
  · rw [← hV, hVa₃]; exact hzero
  · rw [← hV]
    rcases eq_or_ne W.a₄ 0 with h0 | h0
    · rw [hVa₄, h0, map_zero, mul_zero]; exact hzero
    · rw [hVa₄, hmem _ h0]; have := h4 h0; omega
  · rw [← hV]
    rcases eq_or_ne W.a₆ 0 with h0 | h0
    · rw [hVa₆, h0, map_zero, mul_zero]; exact hzero
    · rw [hVa₆, hmem _ h0]; have := h6 h0; omega
  · rw [← hV]
    have hrw : (V.Δ)⁻¹ = π ^ (12 * d) * algebraMap ℚ L (W.Δ)⁻¹ := by
      rw [hVΔ, mul_inv, ← zpow_neg, map_inv₀]; ring_nf
    rw [hrw, hmem _ (inv_ne_zero hΔ0), padicValRat.inv]
    omega

/-- **The tame case at a curve in short Weierstrass form** (PROVEN 2026-07-27), obtained
by instantiating the scaling above at the concrete base `ℚ(q^{1/12})` of
`EllipticCurve/TorsionReduction.lean`. Three obligations are discharged here and nowhere
else:

* `FiniteDimensional ℚ L` — `TameBase` does not record it and `TameGoodModel` does not
  either, which is precisely why neither can be transported into
  `PotentiallyGoodModel`. It comes from `TameBaseAux.exists_repr`: the twelve powers
  `1, π, …, π¹¹` span, so `⊤` is finitely generated. (No `PowerBasis` is used, for the
  same reason `exists_tameResidueHom` avoids one — the `Algebra ℚ` instance clash.)
* the DVR structure — `TameBaseAux.instIsDiscreteValuationRingTameSubring` above;
* residue degree one as a RING EQUIVALENCE —
  `residueFieldEquivZModOfLocalHom` applied to `TameBaseAux.exists_tameResidueHom`. -/
theorem WeierstrassCurve.exists_potentiallyGoodModel_of_isShortNF (W : WeierstrassCurve ℚ)
    [W.IsElliptic] [W.IsShortNF] {q : ℕ} [Fact q.Prime] (hq5 : 5 ≤ q)
    (hj : ¬ (q ∣ W.j.den)) : Nonempty (W.PotentiallyGoodModel q) := by
  classical
  obtain ⟨h4, h6⟩ := WeierstrassCurve.padicValRat_Δ_le_of_jIntegral W hq5 hj
  obtain ⟨res, hres⟩ := TameBaseAux.exists_tameResidueHom q
  letI : DecidableEq (AdjoinRoot (TameBaseAux.qpoly q)) := Classical.decEq _
  haveI := hres
  haveI hfin : FiniteDimensional ℚ (AdjoinRoot (TameBaseAux.qpoly q)) := by
    constructor
    have htop : (⊤ : Submodule ℚ (AdjoinRoot (TameBaseAux.qpoly q)))
        = Submodule.span ℚ (Set.range fun i : Fin 12 => TameBaseAux.unif q ^ (i : ℕ)) := by
      refine le_antisymm ?_ le_top
      intro x _
      obtain ⟨c, hc⟩ := TameBaseAux.exists_repr q x
      rw [hc]
      refine Submodule.sum_mem _ fun i hi => ?_
      have hsm : TameBaseAux.ofQ q (c i) * TameBaseAux.unif q ^ i
          = (c i) • (TameBaseAux.unif q ^ i) := by
        rw [Algebra.smul_def]
        congr 1
      rw [hsm]
      exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩)
    rw [htop]
    exact Submodule.fg_span (Set.finite_range _)
  refine WeierstrassCurve.exists_potentiallyGoodModel_of_tameBase W
    (AdjoinRoot (TameBaseAux.qpoly q)) (TameBaseAux.tameSubring q)
    (WeierstrassCurve.residueFieldEquivZModOfLocalHom res) (TameBaseAux.unif q)
    (TameBaseAux.unif_ne_zero q) ?_ h4 h6
  intro m x hx
  rw [TameBaseAux.algebraMap_eq_ofQ]
  exact TameBaseAux.tame_mem_iff q m hx

/-- **The TAME half of the arithmetic leaf: `5 ≤ q` is PROVEN** (2026-07-27). The
reduction to short Weierstrass form is `E.toShortNF` (mathlib's `toShortNF_spec`;
`Invertible 2` and `Invertible 3` are free over `ℚ`), `variableChange_j` carries
`j`-integrality across, and the two variable changes compose by `mul_smul` and
`map_variableChange` — exactly as in `exists_tameGoodModel_of_jIntegral`, but with no
`emb` field to transport, so the composition is shorter here.

`5 ≤ q` is load-bearing exactly once, inside `padicValRat_Δ_le_of_jIntegral`: a prime
`≥ 5` divides no power of `2` and no power of `3`, hence kills the valuations of `4`,
`16`, `27` and `6912 = 2⁸·3³`. That is the ONLY use, and it is also exactly what fails
at `q = 3` — see the wild leaf below. -/
theorem WeierstrassCurve.exists_potentiallyGoodModel_of_jIntegral_five_le
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {q : ℕ} [Fact q.Prime] (hq5 : 5 ≤ q)
    (hj : 0 ≤ padicValRat q E.j) : Nonempty (E.PotentiallyGoodModel q) := by
  classical
  haveI : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
  haveI : Invertible (3 : ℚ) := invertibleOfNonzero (by norm_num)
  have hj0 : ¬ (q ∣ E.j.den) := TameBaseAux.not_dvd_den_of_padicValRat_nonneg hj
  have hj' : ¬ (q ∣ (E.toShortNF • E).j.den) := by rwa [variableChange_j]
  obtain ⟨N⟩ := WeierstrassCurve.exists_potentiallyGoodModel_of_isShortNF
    (E.toShortNF • E) hq5 hj'
  refine ⟨{
    K := N.K
    R := N.R
    resEquiv := N.resEquiv
    V := N.V
    C := N.C * (E.toShortNF.map (algebraMap ℚ N.K))
    V_eq := by
      have hmv : (E.toShortNF.map (algebraMap ℚ N.K)) • (E.baseChange N.K)
          = (E.toShortNF • E).baseChange N.K := map_variableChange _ _ _
      rw [N.V_eq, mul_smul, hmv] }⟩

/-- **The WILD half of the arithmetic leaf: `q = 3`** (sorry leaf, opened 2026-07-27 when
the `5 ≤ q` half above was PROVEN). This is the genuinely missing part of
`exists_potentiallyGoodModel_of_jIntegral`, and the consumers of this file need it —
they take `q ∈ {3, 5}`, so it cannot be dodged by assuming `5 ≤ q`.

**WHY THE TAME ROUTE DOES NOT EXTEND, in three independent ways.** Each is a concrete
obstruction rather than a difficulty of degree, and each has to be dealt with:

1. *The valuation inequality is FALSE at `3`.* `padicValRat_Δ_le_of_jIntegral` proves
   `3a ≥ d` and `2b ≥ d` from `v_q(j) ≥ 0` using `v_q(27) = v_q(6912) = 0`, which needs
   `q ≥ 5`. At `q = 3`, `j = 6912·A³/(4A³ + 27B²)` gives `v₃(j) = 3 + 3a − d`, so
   `j`-integrality only says `3a ≥ d − 3`. **Explicit witness that the conclusion itself
   fails**: `y² = x³ + 3` has `A = 0`, `B = 3`, `Δ = −16·27·9`, so `d = v₃(Δ) = 5` while
   `2b = 2`; the scaled `a₆` would have valuation `−6d + 12b = −18 < 0`.
2. *Short Weierstrass form cannot reduce to a good curve of nonzero `j`.* Over `𝔽₃` a
   curve with `a₁ = a₂ = a₃ = 0` has `c₄ = −48A ≡ 0`, hence `j = c₄³/Δ = 0`. So for any
   `E/ℚ` with `j ≢ 0 (mod 3)` the good model must have `a₁` or `a₂` nonzero, i.e. the
   `r, s, t` part of the variable change is genuinely needed — unlike the tame case,
   where `u` alone suffices. (The `u`-only scaling is not merely suboptimal here; it
   cannot produce the answer.)
3. *`ℚ(3^{1/12})` is very likely NOT a large enough base.* At `q = 3` the semistability
   defect can be `3`, `6` or `12`, all divisible by `p = 3`, so the extension is WILDLY
   ramified — and wild degree-`3` extensions of `ℚ₃` are not Kummer, because `μ₃ ⊄ ℚ̆₃`
   (`ζ₃` generates the ramified `ℚ₃(√−3)`). So the Eisenstein base `X¹² − 3` of
   `TameBaseAux`, which handles every tame `e ∈ {1,2,3,4,6}` at `q ≥ 5`, has no reason to
   contain the field this case needs. The classical substitute is `ℚ(E[m])` for `m ≥ 3`
   prime to `3` (Serre–Tate), localised at a prime above `3` of residue degree `1`.
   **The check that would refute this pessimism**: exhibit, for every `E/ℚ₃` with
   `v₃(j) ≥ 0`, a variable change over `ℚ₃(3^{1/12})` with integral coefficients and unit
   discriminant. It DOES exist for `y² = x³ + 3`: with `π¹² = 3`, take
   `(u, r, s, t) = (π⁵, −π⁴, 0, π¹⁵)`, giving `(a₁,a₂,a₃,a₄,a₆) = (0, −3π⁻⁶, 2, 1, −1)`
   and reduction `y² − y = x³ + x − 1` over `𝔽₃`, which is nonsingular. So the base may
   yet be enough; what is missing is an argument, not a counterexample.

**WHAT IS ALREADY BUILT AND MUST NOT BE REBUILT.** The entire non-arithmetic half of
this leaf is proven above and is uniform in `q`:
`exists_potentiallyGoodModel_of_integral` turns *(number field, DVR, residue
equivalence, variable change, five integrality memberships, invertible `Δ`)* into the
`PotentiallyGoodModel` datum; `hasGoodReduction_of_isUnit_Δ` and
`isMinimal_of_valuation_Δ_eq_one` discharge mathlib's `IsMinimal`/`HasGoodReduction`
bookkeeping; `residueFieldEquivZModOfLocalHom` upgrades any local hom onto `ZMod 3` to
the required `resEquiv`; and `TameBaseAux.instIsDiscreteValuationRingTameSubring` shows
how to get a DVR out of a valuation subring whose value group is `ℤ` (the pattern
generalises: `exists_valuation_eq_zpow` is the only step that mentions the specific
base). So a prover here owes exactly ONE thing: a base with residue degree `1` at `3`
together with a variable change over it whose scaled equation is integral with unit
discriminant.

**THE CHECK THAT WOULD REFUTE THIS LEAF**: exhibit `E/ℚ` with `0 ≤ v₃(j(E))` acquiring
good reduction over NO finite extension of `ℚ₃` of residue degree `1`. Silverman *AEC*
VII.5.5 gives good reduction over some finite `L/ℚ₃`; dropping the unramified layer is
legitimate (`I_{L'} = I_L` for `L'/L` unramified, so Néron–Ogg–Shafarevich already gives
good reduction over `L`), so such a witness would have to break that step. -/
theorem WeierstrassCurve.exists_potentiallyGoodModel_of_jIntegral_three
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {q : ℕ} [Fact q.Prime] (hq3 : q = 3)
    (hj : 0 ≤ padicValRat q E.j) : Nonempty (E.PotentiallyGoodModel q) :=
  sorry

/-- **The ARITHMETIC half: integral `j`-invariant produces a good model over a
number field with residue degree one at `q`** (opened 2026-07-27 by
decomposing `exists_frobeniusAut_of_potentiallyGoodReduction` below;
**DECOMPOSED 2026-07-27** into its tame and wild halves, of which
`exists_potentiallyGoodModel_of_jIntegral_five_le` is PROVEN and
`exists_potentiallyGoodModel_of_jIntegral_three` is the one remaining leaf). No
Galois theory appears here; the whole content is reduction theory of Weierstrass
equations.

THE PROOF BELOW is only the case split: a prime `q ≠ 2` is either `3` or `≥ 5`
(`4` is not prime), and the two halves are separately owned. `5 ≤ q` is PROVEN
over `EllipticCurve/TorsionReduction.lean`'s base `ℚ(q^{1/12})`, upgraded to a
DVR here; `q = 3` is wildly ramified and is where all the remaining difficulty
sits — read that leaf's docstring, which records three independent reasons the
tame route does not extend and lists the machinery already built for it.

THE INFORMAL PROOF, kept for the wild half. Locally, `0 ≤ v_q(j(E))` is
equivalent to potential good reduction (Silverman *AEC* VII.5.5), so `E/ℚ_q`
acquires good reduction over some finite `L/ℚ_q`. Three further steps produce
the datum:

1. *Drop the unramified layer.* For `L'/L` unramified, `I_{L'} = I_L`, so by the
   criterion of Néron–Ogg–Shafarevich good reduction over `L'` already gives
   good reduction over `L`. Equivalently and more concretely: an unramified
   twist of a curve with good reduction has good reduction, because its
   discriminant is again a unit. This is what makes residue degree `1`
   available at all, and it is why `resEquiv` is not an extra assumption but a
   normalisation.
2. *Keep the singular point rational.* The singular point of an additive
   reduction is unique, hence fixed by the residue Galois group, hence residue
   rational — so the `r, s, t` part of the variable change costs no extension
   and only the `u` part can.
3. *Descend to a number field.* `K` is obtained from `L` by Krasner:
   a number field dense enough at `q` has completion `L`, and good reduction is
   a condition on the completion.

THE OBLIGATION THAT IS NOT UNIFORM IN `q`, STATED HONESTLY. Step 1 is the
standard statement for `q ≥ 5`, where the twisting is by `u` with
`v(u) = d/12` and `L` is the TAME Kummer extension `ℚ_q(π^{1/e})`,
`e ∈ {1, 2, 3, 4, 6}` (Silverman *ATAEC* IV.10; Kraus, Manuscripta Math. 69
(1990)). At `q = 3` the semistability defect can be `12` and `L/ℚ_q` is WILDLY
ramified. `q = 3` IS used by the consumers of this file (they take
`q ∈ {3, 5}`), so this cannot be dodged by assuming `5 ≤ q`; the wild case is
the genuinely missing ingredient and the tame case is textbook.

RELATED OPEN LEAF, DO NOT DUPLICATE: `exists_tameGoodModel_of_jIntegral`
(`EllipticCurve/TorsionReduction.lean`) is the same arithmetic in the
`TameGoodModel` vocabulary, restricted to `5 ≤ ℓ`. See
`PotentiallyGoodModel`'s docstring for the comparison.

THE CHECK THAT WOULD REFUTE THIS LEAF: exhibit `E/ℚ` and a prime `q` with
`0 ≤ v_q(j(E))` acquiring good reduction over NO finite extension of `ℚ_q` of
residue degree `1`. By step 1 that would require an example where the
unramified layer cannot be dropped, i.e. a curve with good reduction over an
unramified extension of `ℚ_q` but over no totally ramified one — which the
unit-discriminant argument of step 1 rules out for `q` odd. -/
theorem WeierstrassCurve.exists_potentiallyGoodModel_of_jIntegral
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {q : ℕ} [Fact q.Prime] (hq : q.Prime)
    (hq2 : q ≠ 2) (hj : 0 ≤ padicValRat q E.j) :
    Nonempty (E.PotentiallyGoodModel q) := by
  have h2 := hq.two_le
  rcases eq_or_lt_of_le (show 3 ≤ q by omega) with h | h
  · exact WeierstrassCurve.exists_potentiallyGoodModel_of_jIntegral_three E h.symm hj
  · have hq4 : q ≠ 4 := by rintro rfl; exact absurd hq (by decide)
    exact WeierstrassCurve.exists_potentiallyGoodModel_of_jIntegral_five_le E (by omega) hj
