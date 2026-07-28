/-
Modularity/DivisibleTorsionParam.lean — own work for the Fermat project.
-/
module

public import Fermat.FLT.EllipticCurve.Torsion
public import Mathlib.Order.KonigLemma

/-!
# `(ℚ/ℤ)²` parametrises the torsion of a group whose `n`-torsion has `n²` elements

This module supplies the whole content of `Modularity/MoretBailly.lean`'s leaf
`exists_torsionParam_of_divisible`, which is the "`E[n] ≅ (ℤ/n)²` for all `n`,
COHERENTLY in `n`" half of `exists_realWeierstrassCurveWithConjTorsion`.  It is
pure abelian group theory: no elliptic curve, no field, nothing archimedean.

## What is proven

`exists_torsionParam`: if `P` is an additive abelian group with
`Nat.card {x : P // (n : ℤ) • x = 0} = n ^ 2` for every `n ≠ 0`, then there is an
additive injection `θ : (ℚ/ℤ)² → P` whose image is exactly the torsion subgroup
of `P` (every `θ v` is torsion, and every `n`-torsion element of `P` is a value
of `θ`).

## The argument, and what it does NOT need

Two steps, and only the second is work:

1. *`P[n] ≅ (ℤ/n)²`.*  Already proven, for an abstract `AddCommGroup` and with no
   divisibility hypothesis, as `group_theory_lemma`
   (`Fermat/FLT/EllipticCurve/Torsion.lean`), which runs off the structure theorem
   for finite abelian groups.  `exists_isTorsionBasis` below is the repackaging of
   that equivalence as a PAIR `(p, q)` satisfying `IsTorsionBasis n`, an
   elementary four-clause predicate written entirely with `ℤ`-scalars so that no
   `ZMod n`-module structure has to be carried around afterwards.

2. *Compatibility of the bases across `n`.*  This is the real content.  Bases of
   `P[i !]` form an inverse system along `ℕ` — the transition
   `IsTorsionBasis.restrict` sends a basis of `P[m * d]` to the basis
   `(d • p, d • q)` of `P[m]` — and each level is NONEMPTY (step 1) and FINITE
   (the counting hypothesis makes `P[n]` finite).  Kőnig's lemma for inverse
   systems, `exists_seq_forall_proj_of_forall_finite`
   (`Mathlib/Order/KonigLemma.lean`), then produces a coherent sequence
   `(p_k, q_k)` with `(k !/i !) • p_k = p_i`.  Note this needs no SURJECTIVITY of
   the transition maps — which is fortunate, since surjectivity is the statement
   that `GL₂(ℤ/n) → GL₂(ℤ/m)` is onto, and arbitrary divisibility lifts do NOT
   give bases (over `(ℚ/ℤ)²` with `m = 1`, `d = 2`, the lift `p₁ = q₁ = (1/2, 0)`
   of `p = q = 0` is not a basis of the `2`-torsion).

The factorials are only a cofinal chain: `ℚ/ℤ = ⋃_k (1/k !)ℤ/ℤ`, so a section
over `k ↦ k !` is as good as one over the whole divisibility poset, and a chain
is what Kőnig's lemma is stated for.

`θ` itself is assembled from two copies of `qmap`, the map `ℚ → P` sending
`a / k !` to `a • r k`.  Its well-definedness (`qmap_eq`) is exactly the coherence
of the system; additivity comes from putting two rationals over the common
denominator `(den x * den y)!`; and `qmap` kills `ℤ` because `r 0` is a basis of
the `0! = 1`-torsion, hence `0`.  So `qmap` descends to `ℚ ⧸ (1 : Submodule ℤ ℚ)`
(`qquot`), and injectivity and the image description read straight off the
`indep` and `span` clauses of `IsTorsionBasis`.

## DIVISIBILITY IS NOT NEEDED, and this is a genuine finding

The leaf in `MoretBailly.lean` is stated with a divisibility hypothesis
`hdiv : ∀ n ≠ 0, ∀ y, ∃ x, n • x = y`, and its docstring reads "Divisibility is
what makes each transition map `A[nm] → A[n]` surjective, hence each fibre
nonempty".  That is a correct description of a DIFFERENT proof — the one that
builds the section by recursion out of surjective transitions — and it is not the
proof used here.  Kőnig's lemma asks for finite nonempty fibres, not surjective
ones, and `IsTorsionBasis.restrict` needs nothing but the counting hypothesis.

The statement is therefore true without `hdiv`, and visibly so: `P = (ℚ/ℤ)² ⊕ ℤ`
satisfies the counting hypothesis, is NOT divisible, and its torsion subgroup is
`(ℚ/ℤ)²`.  The leaf keeps its hypothesis (its consumer already holds it and the
name is cited elsewhere), but the binder is underscored there to make the
non-use mechanically visible.
-/

@[expose] public section

namespace GaloisRepresentation.Modularity.DivisibleTorsion

universe v

variable {P : Type v} [AddCommGroup P]

/-- `IsTorsionBasis n (p, q)` says that `p, q` is a `ℤ/n`-basis of the `n`-torsion
subgroup of `P`. -/
structure IsTorsionBasis (n : ℕ) (pq : P × P) : Prop where
  smul_fst : (n : ℤ) • pq.1 = 0
  smul_snd : (n : ℤ) • pq.2 = 0
  span : ∀ y : P, (n : ℤ) • y = 0 → ∃ a b : ℤ, a • pq.1 + b • pq.2 = y
  indep : ∀ a b : ℤ, a • pq.1 + b • pq.2 = 0 → (n : ℤ) ∣ a ∧ (n : ℤ) ∣ b

/-- Existence of a basis at every level, from the counting hypothesis alone. -/
theorem exists_isTorsionBasis
    (hcard : ∀ n : ℕ, n ≠ 0 → Nat.card {x : P // (n : ℤ) • x = 0} = n ^ 2)
    {n : ℕ} (hn : n ≠ 0) : ∃ pq : P × P, IsTorsionBasis n pq := by
  haveI : NeZero n := ⟨hn⟩
  have hcard' : ∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ P (d : ℤ)) = d ^ 2 := by
    intro d hd
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact hn (Nat.eq_zero_of_zero_dvd hd)
    rw [← hcard d hd0]
    exact Nat.card_congr (Equiv.subtypeEquivRight
      (p := fun x : P => x ∈ Submodule.torsionBy ℤ P (d : ℤ))
      (q := fun x : P => (d : ℤ) • x = 0) fun _ => Iff.rfl)
  obtain ⟨φ⟩ := group_theory_lemma (A := P) (Nat.pos_of_ne_zero hn) 2 hcard'
  set T := Submodule.torsionBy ℤ P (n : ℤ) with hT
  set P0 : T := φ.symm (Pi.single 0 1) with hP0
  set Q0 : T := φ.symm (Pi.single 1 1) with hQ0
  have key : ∀ a b : ℤ, a • (P0 : P) + b • (Q0 : P)
      = ((φ.symm (fun i : Fin 2 => if i = 0 then (a : ZMod n) else (b : ZMod n)) : T) : P) := by
    intro a b
    have h : a • P0 + b • Q0
        = φ.symm (fun i : Fin 2 => if i = 0 then (a : ZMod n) else (b : ZMod n)) := by
      rw [hP0, hQ0, ← map_zsmul, ← map_zsmul, ← map_add]
      congr 1
      funext i
      fin_cases i <;> simp [zsmul_eq_mul]
    exact congrArg Subtype.val h
  refine ⟨((P0 : P), (Q0 : P)), ?_, ?_, ?_, ?_⟩
  · exact P0.2
  · exact Q0.2
  · intro y hy
    have hyT : y ∈ T := hy
    refine ⟨(((φ ⟨y, hyT⟩) 0).val : ℤ), (((φ ⟨y, hyT⟩) 1).val : ℤ), ?_⟩
    rw [key]
    have : (fun i : Fin 2 => if i = 0 then (((((φ ⟨y, hyT⟩) 0).val : ℤ)) : ZMod n)
        else (((((φ ⟨y, hyT⟩) 1).val : ℤ)) : ZMod n)) = φ ⟨y, hyT⟩ := by
      funext i
      fin_cases i <;> simp [ZMod.natCast_val, ZMod.cast_id]
    rw [this, AddEquiv.symm_apply_apply]
  · intro a b hab
    rw [key] at hab
    have h0 : (φ.symm (fun i : Fin 2 => if i = 0 then (a : ZMod n) else (b : ZMod n)) : T) = 0 :=
      Subtype.ext hab
    have h1 : (fun i : Fin 2 => if i = 0 then (a : ZMod n) else (b : ZMod n)) = 0 := by
      have := congrArg φ h0
      simpa using this
    constructor
    · have h2 := congrFun h1 0
      simp only [Pi.zero_apply, if_pos] at h2
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd a n).mp h2
    · have h2 := congrFun h1 1
      simp only [Pi.zero_apply] at h2
      rw [if_neg (by decide : ¬((1 : Fin 2) = 0))] at h2
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd b n).mp h2

/-- Restricting a basis of the `(m * d)`-torsion to a basis of the `m`-torsion. -/
theorem IsTorsionBasis.restrict {m d : ℕ} (hm : m ≠ 0) (hd : d ≠ 0) {pq : P × P}
    (h : IsTorsionBasis (m * d) pq) :
    IsTorsionBasis m ((d : ℤ) • pq.1, (d : ℤ) • pq.2) := by
  have hmz : (m : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hm
  have hdz : (d : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hd
  have hmd : ((m * d : ℕ) : ℤ) = (m : ℤ) * (d : ℤ) := by push_cast; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (m : ℤ) • ((d : ℤ) • pq.1) = 0
    rw [smul_smul, ← hmd]
    exact h.smul_fst
  · show (m : ℤ) • ((d : ℤ) • pq.2) = 0
    rw [smul_smul, ← hmd]
    exact h.smul_snd
  · intro y hy
    have hy' : ((m * d : ℕ) : ℤ) • y = 0 := by
      rw [hmd, mul_comm, ← smul_smul, hy, smul_zero]
    obtain ⟨a, b, hab⟩ := h.span y hy'
    have hz : (m : ℤ) • (a • pq.1 + b • pq.2) = 0 := by rw [hab]; exact hy
    rw [smul_add, smul_smul, smul_smul] at hz
    obtain ⟨ha, hb⟩ := h.indep _ _ hz
    rw [hmd] at ha hb
    obtain ⟨a', ha'⟩ : (d : ℤ) ∣ a := (mul_dvd_mul_iff_left hmz).mp ha
    obtain ⟨b', hb'⟩ : (d : ℤ) ∣ b := (mul_dvd_mul_iff_left hmz).mp hb
    refine ⟨a', b', ?_⟩
    show a' • ((d : ℤ) • pq.1) + b' • ((d : ℤ) • pq.2) = y
    rw [smul_smul, smul_smul, mul_comm a' (d : ℤ), mul_comm b' (d : ℤ), ← ha', ← hb', hab]
  · intro a b hab
    have hab' : (a * (d : ℤ)) • pq.1 + (b * (d : ℤ)) • pq.2 = 0 := by
      rw [← smul_smul, ← smul_smul]
      exact hab
    obtain ⟨ha, hb⟩ := h.indep _ _ hab'
    rw [hmd] at ha hb
    exact ⟨(mul_dvd_mul_iff_right hdz).mp ha, (mul_dvd_mul_iff_right hdz).mp hb⟩

/-- `cfac i j = j ! / i !`. -/
def cfac (i j : ℕ) : ℕ := Nat.factorial j / Nat.factorial i

theorem cfac_spec {i j : ℕ} (h : i ≤ j) : Nat.factorial i * cfac i j = Nat.factorial j :=
  Nat.mul_div_cancel' (Nat.factorial_dvd_factorial h)

theorem cfac_ne_zero {i j : ℕ} (h : i ≤ j) : cfac i j ≠ 0 := by
  intro h0
  have hs := cfac_spec h
  rw [h0, mul_zero] at hs
  exact (Nat.factorial_pos j).ne hs

theorem cfac_self (i : ℕ) : cfac i i = 1 := Nat.div_self (Nat.factorial_pos i)

theorem cfac_trans {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    cfac i j * cfac j k = cfac i k := by
  refine Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos i) ?_
  rw [← mul_assoc, cfac_spec hij, cfac_spec hjk, cfac_spec (hij.trans hjk)]

/-- **A COMPATIBLE SYSTEM OF BASES.**  Kőnig's lemma applied to the inverse system
of (nonempty, finite) sets of bases of the `i !`-torsion. -/
theorem exists_compatibleBasis
    (hcard : ∀ n : ℕ, n ≠ 0 → Nat.card {x : P // (n : ℤ) • x = 0} = n ^ 2) :
    ∃ f : ℕ → P × P, (∀ i, IsTorsionBasis (Nat.factorial i) (f i)) ∧
      ∀ i j, i ≤ j → (cfac i j : ℤ) • (f j).1 = (f i).1 ∧
        (cfac i j : ℤ) • (f j).2 = (f i).2 := by
  have hne : ∀ i : ℕ, Nonempty {pq : P × P // IsTorsionBasis (Nat.factorial i) pq} := by
    intro i
    obtain ⟨pq, h⟩ := exists_isTorsionBasis hcard (Nat.factorial_ne_zero i)
    exact ⟨⟨pq, h⟩⟩
  have hfinT : ∀ n : ℕ, n ≠ 0 → Finite {x : P // (n : ℤ) • x = 0} := by
    intro n hn
    have hpos : 0 < Nat.card {x : P // (n : ℤ) • x = 0} := by
      rw [hcard n hn]
      exact pow_pos (Nat.pos_of_ne_zero hn) 2
    exact (Nat.card_pos_iff.mp hpos).2
  have hfin : ∀ i : ℕ, Finite {pq : P × P // IsTorsionBasis (Nat.factorial i) pq} := by
    intro i
    haveI := hfinT _ (Nat.factorial_ne_zero i)
    refine Finite.of_injective
      (fun x : {pq : P × P // IsTorsionBasis (Nat.factorial i) pq} =>
        ((⟨x.1.1, x.2.smul_fst⟩ : {y : P // ((Nat.factorial i : ℕ) : ℤ) • y = 0}),
         (⟨x.1.2, x.2.smul_snd⟩ : {y : P // ((Nat.factorial i : ℕ) : ℤ) • y = 0}))) ?_
    intro x y hxy
    have h1 : x.1.1 = y.1.1 := congrArg Subtype.val (congrArg Prod.fst hxy)
    have h2 : x.1.2 = y.1.2 := congrArg Subtype.val (congrArg Prod.snd hxy)
    exact Subtype.ext (Prod.ext h1 h2)
  let α : ℕ → Type v := fun i => {pq : P × P // IsTorsionBasis (Nat.factorial i) pq}
  let π : {i j : ℕ} → (hij : i ≤ j) → α j → α i := fun {i j} hij x =>
    ⟨((cfac i j : ℤ) • x.1.1, (cfac i j : ℤ) • x.1.2),
      IsTorsionBasis.restrict (Nat.factorial_ne_zero i) (cfac_ne_zero hij)
        (by rw [cfac_spec hij]; exact x.2)⟩
  obtain ⟨g, hg⟩ := @exists_seq_forall_proj_of_forall_finite α (hfin 0) hne π
    (fun i a => by
      apply Subtype.ext
      show ((cfac i i : ℤ) • a.1.1, (cfac i i : ℤ) • a.1.2) = a.1
      rw [cfac_self]
      simp)
    (fun i j k hij hjk a => by
      apply Subtype.ext
      show ((cfac i j : ℤ) • ((cfac j k : ℤ) • a.1.1), (cfac i j : ℤ) • ((cfac j k : ℤ) • a.1.2))
          = ((cfac i k : ℤ) • a.1.1, (cfac i k : ℤ) • a.1.2)
      rw [smul_smul, smul_smul, ← Nat.cast_mul, cfac_trans hij hjk])
    (fun i a => by
      haveI := hfin (i + 1)
      exact Set.toFinite _)
  refine ⟨fun i => (g i).1, fun i => (g i).2, fun i j hij => ⟨?_, ?_⟩⟩
  · exact congrArg (fun z => z.1.1) (hg hij)
  · exact congrArg (fun z => z.1.2) (hg hij)

/-- The map `ℚ → P` attached to a system `r : ℕ → P`, sending `a / k !` to `a • r k`. -/
noncomputable def qmap (r : ℕ → P) (x : ℚ) : P :=
  (x * ((Nat.factorial x.den : ℕ) : ℚ)).num • r x.den

theorem exists_num_of_dvd {x : ℚ} {N : ℕ} (h : x.den ∣ N) : ∃ a : ℤ, x * (N : ℚ) = (a : ℚ) := by
  obtain ⟨e, rfl⟩ := h
  refine ⟨x.num * e, ?_⟩
  have hd : ((x.den : ℚ)) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have hnum : (x.num : ℚ) = x * (x.den : ℚ) := (div_eq_iff hd).mp (Rat.num_div_den x)
  push_cast
  rw [hnum]
  ring

variable {r : ℕ → P}

theorem smul_r_eq_of_le (hr : ∀ i j : ℕ, i ≤ j → (cfac i j : ℤ) • r j = r i)
    {x : ℚ} {k l : ℕ} (hkl : k ≤ l) {a b : ℤ}
    (hk : x * ((Nat.factorial k : ℕ) : ℚ) = (a : ℚ))
    (hl : x * ((Nat.factorial l : ℕ) : ℚ) = (b : ℚ)) : a • r k = b • r l := by
  have hc : ((Nat.factorial k : ℕ) : ℚ) * ((cfac k l : ℕ) : ℚ) = ((Nat.factorial l : ℕ) : ℚ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) (cfac_spec hkl)
  have hb : (b : ℚ) = ((a * (cfac k l : ℤ) : ℤ) : ℚ) := by
    rw [← hl, ← hc, ← mul_assoc, hk]
    push_cast
    ring
  have hb' : b = a * (cfac k l : ℤ) := by exact_mod_cast hb
  rw [hb', mul_smul, hr k l hkl]

theorem smul_r_eq (hr : ∀ i j : ℕ, i ≤ j → (cfac i j : ℤ) • r j = r i)
    {x : ℚ} {k l : ℕ} {a b : ℤ}
    (hk : x * ((Nat.factorial k : ℕ) : ℚ) = (a : ℚ))
    (hl : x * ((Nat.factorial l : ℕ) : ℚ) = (b : ℚ)) : a • r k = b • r l := by
  rcases le_total k l with h | h
  · exact smul_r_eq_of_le hr h hk hl
  · exact (smul_r_eq_of_le hr h hl hk).symm

theorem qmap_eq (hr : ∀ i j : ℕ, i ≤ j → (cfac i j : ℤ) • r j = r i)
    {x : ℚ} {k : ℕ} {a : ℤ} (h : x * ((Nat.factorial k : ℕ) : ℚ) = (a : ℚ)) :
    qmap r x = a • r k := by
  obtain ⟨a₀, ha₀⟩ := exists_num_of_dvd (x := x) (N := Nat.factorial x.den)
    (Nat.dvd_factorial (Nat.pos_of_ne_zero x.den_ne_zero) le_rfl)
  have h1 : qmap r x = a₀ • r x.den := by
    rw [qmap, ha₀, Rat.num_intCast]
  rw [h1]
  exact smul_r_eq hr ha₀ h

theorem qmap_add (hr : ∀ i j : ℕ, i ≤ j → (cfac i j : ℤ) • r j = r i) (x y : ℚ) :
    qmap r (x + y) = qmap r x + qmap r y := by
  have hkpos : 0 < x.den * y.den :=
    Nat.mul_pos (Nat.pos_of_ne_zero x.den_ne_zero) (Nat.pos_of_ne_zero y.den_ne_zero)
  have hkfac : x.den * y.den ∣ Nat.factorial (x.den * y.den) := Nat.dvd_factorial hkpos le_rfl
  have hdx : x.den ∣ Nat.factorial (x.den * y.den) := dvd_trans ⟨y.den, rfl⟩ hkfac
  have hdy : y.den ∣ Nat.factorial (x.den * y.den) :=
    dvd_trans ⟨x.den, mul_comm x.den y.den⟩ hkfac
  obtain ⟨a, ha⟩ := exists_num_of_dvd hdx
  obtain ⟨b, hb⟩ := exists_num_of_dvd hdy
  have hxy : (x + y) * ((Nat.factorial (x.den * y.den) : ℕ) : ℚ) = ((a + b : ℤ) : ℚ) := by
    rw [add_mul, ha, hb]
    push_cast
    ring
  rw [qmap_eq hr hxy, qmap_eq hr ha, qmap_eq hr hb, add_smul]

theorem qmap_intCast (hr : ∀ i j : ℕ, i ≤ j → (cfac i j : ℤ) • r j = r i) (hr0 : r 0 = 0)
    (z : ℤ) : qmap r ((z : ℚ)) = 0 := by
  have h : ((z : ℚ)) * ((Nat.factorial 0 : ℕ) : ℚ) = ((z : ℤ) : ℚ) := by simp
  rw [qmap_eq hr h, hr0, smul_zero]

/-- The additive map `ℚ → P` attached to a compatible system. -/
noncomputable def qhom (hr : ∀ i j : ℕ, i ≤ j → (cfac i j : ℤ) • r j = r i) : ℚ →+ P :=
  AddMonoidHom.mk' (qmap r) (qmap_add hr)

/-- The induced map `ℚ/ℤ → P`. -/
noncomputable def qquot (hr : ∀ i j : ℕ, i ≤ j → (cfac i j : ℤ) • r j = r i) (hr0 : r 0 = 0) :
    (ℚ ⧸ (1 : Submodule ℤ ℚ)) →ₗ[ℤ] P :=
  Submodule.liftQ _ (qhom hr).toIntLinearMap (by
    intro x hx
    obtain ⟨z, rfl⟩ := Submodule.mem_one.mp hx
    rw [LinearMap.mem_ker]
    have hz : (algebraMap ℤ ℚ) z = ((z : ℤ) : ℚ) := by simp
    rw [hz]
    exact qmap_intCast hr hr0 z)

theorem qquot_mk (hr : ∀ i j : ℕ, i ≤ j → (cfac i j : ℤ) • r j = r i) (hr0 : r 0 = 0) (x : ℚ) :
    qquot hr hr0 (Submodule.Quotient.mk x) = qmap r x := rfl

/-- **THE STRUCTURE OF THE TORSION.**  An abelian group whose `n`-torsion has exactly
`n²` elements for every `n ≥ 1` carries an additive injection of `(ℚ/ℤ)²` whose image
is precisely the torsion subgroup.  No divisibility hypothesis is needed. -/
theorem exists_torsionParam
    (hcard : ∀ n : ℕ, n ≠ 0 → Nat.card {x : P // (n : ℤ) • x = 0} = n ^ 2) :
    ∃ θ : (Fin 2 → (ℚ ⧸ (1 : Submodule ℤ ℚ))) → P,
      (∀ v w, θ (v + w) = θ v + θ w) ∧
      Function.Injective θ ∧
      (∀ v, ∃ n : ℕ, n ≠ 0 ∧ (n : ℤ) • θ v = 0) ∧
      (∀ n : ℕ, n ≠ 0 → ∀ y : P, (n : ℤ) • y = 0 → ∃ v, θ v = y) := by
  obtain ⟨f, hbasis, hcompat⟩ := exists_compatibleBasis hcard
  have hp : ∀ i j : ℕ, i ≤ j → (cfac i j : ℤ) • (fun i => (f i).1) j = (fun i => (f i).1) i :=
    fun i j h => (hcompat i j h).1
  have hq : ∀ i j : ℕ, i ≤ j → (cfac i j : ℤ) • (fun i => (f i).2) j = (fun i => (f i).2) i :=
    fun i j h => (hcompat i j h).2
  have hp0 : (fun i => (f i).1) 0 = 0 := by
    have h := (hbasis 0).smul_fst
    simpa using h
  have hq0 : (fun i => (f i).2) 0 = 0 := by
    have h := (hbasis 0).smul_snd
    simpa using h
  set A := qquot hp hp0 with hA
  set B := qquot hq hq0 with hB
  -- every vector has a common-denominator representation
  have hrep : ∀ v : Fin 2 → (ℚ ⧸ (1 : Submodule ℤ ℚ)), ∃ (k : ℕ) (a b : ℤ),
      A (v 0) + B (v 1) = a • (f k).1 + b • (f k).2 ∧
      v 0 = Submodule.Quotient.mk ((a : ℚ) / ((Nat.factorial k : ℕ) : ℚ)) ∧
      v 1 = Submodule.Quotient.mk ((b : ℚ) / ((Nat.factorial k : ℕ) : ℚ)) := by
    intro v
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective (1 : Submodule ℤ ℚ) (v 0)
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective (1 : Submodule ℤ ℚ) (v 1)
    have hkpos : 0 < x.den * y.den :=
      Nat.mul_pos (Nat.pos_of_ne_zero x.den_ne_zero) (Nat.pos_of_ne_zero y.den_ne_zero)
    have hkfac : x.den * y.den ∣ Nat.factorial (x.den * y.den) := Nat.dvd_factorial hkpos le_rfl
    obtain ⟨a, ha⟩ := exists_num_of_dvd (dvd_trans ⟨y.den, rfl⟩ hkfac)
    obtain ⟨b, hb⟩ := exists_num_of_dvd (dvd_trans ⟨x.den, mul_comm x.den y.den⟩ hkfac)
    have hfacne : ((Nat.factorial (x.den * y.den) : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    have hxa : (a : ℚ) / ((Nat.factorial (x.den * y.den) : ℕ) : ℚ) = x := by
      rw [← ha]
      field_simp
    have hyb : (b : ℚ) / ((Nat.factorial (x.den * y.den) : ℕ) : ℚ) = y := by
      rw [← hb]
      field_simp
    refine ⟨x.den * y.den, a, b, ?_, ?_, ?_⟩
    · rw [← hx, ← hy, hA, hB, qquot_mk, qquot_mk, qmap_eq hp ha, qmap_eq hq hb]
    · rw [hxa, hx]
    · rw [hyb, hy]
  refine ⟨fun v => A (v 0) + B (v 1), ?_, ?_, ?_, ?_⟩
  · intro v w
    simp only [Pi.add_apply, map_add]
    abel
  · intro v w hvw
    have hvw' : A (v 0) + B (v 1) = A (w 0) + B (w 1) := hvw
    have hzero : A ((v - w) 0) + B ((v - w) 1) = 0 := by
      simp only [Pi.sub_apply, map_sub]
      rw [sub_add_sub_comm, hvw', sub_self]
    obtain ⟨k, a, b, hsum, h0, h1⟩ := hrep (v - w)
    rw [hsum] at hzero
    obtain ⟨hda, hdb⟩ := (hbasis k).indep a b hzero
    have hfacne : ((Nat.factorial k : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hmk : ∀ c : ℤ, ((Nat.factorial k : ℕ) : ℤ) ∣ c →
        (Submodule.Quotient.mk ((c : ℚ) / ((Nat.factorial k : ℕ) : ℚ)) :
          ℚ ⧸ (1 : Submodule ℤ ℚ)) = 0 := by
      intro c hc
      obtain ⟨c', rfl⟩ := hc
      have : ((((Nat.factorial k : ℕ) : ℤ) * c' : ℤ) : ℚ) / ((Nat.factorial k : ℕ) : ℚ)
          = ((c' : ℤ) : ℚ) := by
        push_cast
        field_simp
      rw [this, Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_one.mpr ⟨c', by simp⟩
    have hv0 : (v - w) 0 = 0 := by rw [h0]; exact hmk a hda
    have hv1 : (v - w) 1 = 0 := by rw [h1]; exact hmk b hdb
    funext i
    fin_cases i
    · have := hv0
      simp only [Pi.sub_apply] at this
      exact sub_eq_zero.mp this
    · have := hv1
      simp only [Pi.sub_apply] at this
      exact sub_eq_zero.mp this
  · intro v
    obtain ⟨k, a, b, hsum, -, -⟩ := hrep v
    refine ⟨Nat.factorial k, Nat.factorial_ne_zero k, ?_⟩
    show ((Nat.factorial k : ℕ) : ℤ) • (A (v 0) + B (v 1)) = 0
    rw [hsum, smul_add, smul_smul, smul_smul, mul_comm _ a, mul_comm _ b, ← smul_smul, ← smul_smul,
      (hbasis k).smul_fst, (hbasis k).smul_snd, smul_zero, smul_zero, add_zero]
  · intro n hn y hy
    have hnd : (n : ℤ) ∣ ((Nat.factorial n : ℕ) : ℤ) := by
      exact_mod_cast Nat.dvd_factorial (Nat.pos_of_ne_zero hn) le_rfl
    have hy' : ((Nat.factorial n : ℕ) : ℤ) • y = 0 := by
      obtain ⟨c, hc⟩ := hnd
      rw [hc, mul_comm (n : ℤ) c, ← smul_smul, hy, smul_zero]
    obtain ⟨a, b, hab⟩ := (hbasis n).span y hy'
    have hfacne : ((Nat.factorial n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    refine ⟨![Submodule.Quotient.mk ((a : ℚ) / ((Nat.factorial n : ℕ) : ℚ)),
      Submodule.Quotient.mk ((b : ℚ) / ((Nat.factorial n : ℕ) : ℚ))], ?_⟩
    have hA' : A (Submodule.Quotient.mk ((a : ℚ) / ((Nat.factorial n : ℕ) : ℚ)))
        = a • (f n).1 := by
      rw [hA, qquot_mk]
      refine qmap_eq hp ?_
      field_simp
    have hB' : B (Submodule.Quotient.mk ((b : ℚ) / ((Nat.factorial n : ℕ) : ℚ)))
        = b • (f n).2 := by
      rw [hB, qquot_mk]
      refine qmap_eq hq ?_
      field_simp
    show A (![Submodule.Quotient.mk ((a : ℚ) / ((Nat.factorial n : ℕ) : ℚ)),
        Submodule.Quotient.mk ((b : ℚ) / ((Nat.factorial n : ℕ) : ℚ))] 0)
      + B (![Submodule.Quotient.mk ((a : ℚ) / ((Nat.factorial n : ℕ) : ℚ)),
        Submodule.Quotient.mk ((b : ℚ) / ((Nat.factorial n : ℕ) : ℚ))] 1) = y
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hA', hB', hab]

end GaloisRepresentation.Modularity.DivisibleTorsion
