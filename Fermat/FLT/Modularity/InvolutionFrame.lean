/-
Modularity/InvolutionFrame.lean — own work for the Fermat project.
-/
module

public import Fermat.FLT.Modularity.DivisibleTorsionParam
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Tactic.Module

/-!
# Adapted frames for an involution of a divisible group whose `n`-torsion is `(ℤ/n)²`

This module supplies `Modularity/MoretBailly.lean`'s leaf
`exists_adaptedFrame_level`: an involution `c` of `P = (ℚ/ℤ)²` which is neither
`+1` nor `−1` on any `n`-torsion with `n ≥ 3` admits, at EVERY finite level
`n ≠ 0`, a `ℤ/n`-basis `(p, q)` of `P[n]` with

* `c p = p`,
* `c q = [ε] · p − q`,

where `ε` is read off the fixed `2`-torsion: `4` fixed points means `ε = false`
(`c ~ diag(1, −1)`) and `2` means `ε = true` (`c ~` the swap).

Everything is stated for an abstract `AddCommGroup P` that is DIVISIBLE and
satisfies `Nat.card P[n] = n²`; `(ℚ/ℤ)²` is that, and the specialisation is the
last section.

## The two cases, and why they need different arguments

The classical statement is the Diederichsen–Reiner classification of rank-two
`ℤ_p[C₂]`-lattices, read one prime at a time.  What is done here is not that: it
is an argument in the divisible group `P` itself, which avoids `M₂(Ẑ)`, avoids
lattices, and avoids the classification.

*This is not a cosmetic preference.* The level-`n` statement is FALSE for an
abstract involution of `(ℤ/n)²` satisfying the level-`n` hypotheses: over `ℤ/8`,
`c = diag(1, 3)` is an involution, is `≠ ±1` mod `4`, and fixes all of `P[2]`,
yet its `(−1)`-eigenspace `{x : 2x = 0} × {y : 4y = 0}` contains no element of
order `8`, so no adapted frame exists at level `8`.  It is excluded here because
`diag(1, 3)` is not the reduction of any involution of `(ℚ/ℤ)²` — `u² = 1` in
`ℤ₂` forces `u = ±1`.  So a proof of this leaf MUST use levels beyond `n`, or the
global group; the argument below uses divisibility of `P`, which is the same
thing said forwards.

### `ε = false` (four fixed `2`-torsion points)

`c` is then the identity on `P[2]`, so `1 − c` kills `P[2]` and therefore
FACTORS through multiplication by `2`: since `P` is divisible there is an
endomorphism `f` of `P` with `2f = 1 − c` (`exists_halfEndo`), and `f` is
idempotent because `End P` is torsion-free for divisible `P` (`4(f² − f) = (1−c)² − 2(1−c) =
0`).  So `P = ker f ⊕ im f` with `c = 1` on `ker f` and `c = −1` on `im f`, and
the two summands are again divisible.  A divisible subgroup whose `p`-torsion has
`p` elements for every prime has `n`-torsion CYCLIC of order `n` at every level
(`exists_tors_gen`), and a generator of each summand's `n`-torsion is the frame.

### `ε = true` (two fixed `2`-torsion points)

Now `1 − c` does not kill `P[2]` and no such `f` exists — indeed `ker(c−1)` and
`ker(c+1)` meet in a group of order `2` at every even level, so they never split
`P[n]`.  Instead:

* `ker(c ∓ 1)` are both divisible (`isDivisible_fixSub`, applied to `c` and to
  `−c`), the `2`-divisibility being the one interesting step: a half `x₀` of a
  fixed `y` has `(c−1)x₀` in
  `ker(c−1) ∩ P[2]`, which for `ε = true` is exactly the IMAGE of `c−1` on
  `P[2]`, so `x₀` can be corrected by a `2`-torsion element into `ker(c−1)`;
* so at ODD levels `m`, where `2` is invertible and the two kernels are
  independent, generators of `ker(c−1)[m]` and `ker(c+1)[m]` give a frame, the
  `ε = true` twist being a `½` shear of the second basis vector;
* at levels `2^k` a frame is built from ONE element: if `⟨v, c v⟩ = P[2^k]` then
  `(v + c v, v)` is a frame, and such a `v` is any lift of a `w ∈ P[2]` with
  `c w ≠ w`;
* and frames at coprime levels combine (`frame_mul_coprime`), which assembles
  `n = 2^k · m`.
-/

@[expose] public section

namespace GaloisRepresentation.Modularity.InvolutionFrame

open GaloisRepresentation.Modularity.DivisibleTorsion Finset

universe v

variable {P : Type v} [AddCommGroup P]

/-! ### The frame predicate and the `n`-torsion of a subgroup -/

/-- **AN ADAPTED FRAME AT LEVEL `n`**, spelled with `IsTorsionBasis` and two equations
rather than with `MoretBailly.lean`'s `IsAdaptedFrame`, which is declared DOWNSTREAM of
this module.  The two are the same statement field for field, and
`exists_adaptedFrame_level` there is this plus one constructor. -/
def IsFrame (ε : Bool) (c : P →+ P) (n : ℕ) (pq : P × P) : Prop :=
  IsTorsionBasis n pq ∧ c pq.1 = pq.1 ∧ c pq.2 = (if ε then pq.1 else 0) - pq.2

/-! ### The `n`-torsion of a subgroup, and its cardinality -/

/-- The `n`-torsion subgroup of a subgroup `H ≤ P`. -/
def tors (H : AddSubgroup P) (n : ℕ) : AddSubgroup P where
  carrier := {x | x ∈ H ∧ (n : ℤ) • x = 0}
  zero_mem' := ⟨H.zero_mem, smul_zero _⟩
  add_mem' := fun {_ _} ha hb => ⟨H.add_mem ha.1 hb.1, by rw [smul_add, ha.2, hb.2, add_zero]⟩
  neg_mem' := fun {_} ha => ⟨H.neg_mem ha.1, by rw [smul_neg, ha.2, neg_zero]⟩

/-- A subgroup `H` is divisible if every element of `H` is `m`-divisible INSIDE `H`. -/
def IsDivisible (H : AddSubgroup P) : Prop :=
  ∀ m : ℕ, m ≠ 0 → ∀ y ∈ H, ∃ x ∈ H, (m : ℤ) • x = y

/-- `H[1] = 0`. -/
theorem card_tors_one {H : AddSubgroup P} : Nat.card (tors H 1) = 1 := by
  have hsub : Subsingleton (tors H 1) := by
    constructor
    rintro ⟨x, -, hx⟩ ⟨y, -, hy⟩
    simp only [Nat.cast_one, one_smul] at hx hy
    exact Subtype.ext (hx.trans hy.symm)
  exact Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨0⟩⟩

/-- **MULTIPLICATIVITY OF THE TORSION COUNT** for a divisible subgroup: `H[nm]` is an
extension of `H[n]` by `H[m]`, split because `·m : H[nm] → H[n]` is surjective
(that is exactly divisibility). -/
theorem card_tors_mul {H : AddSubgroup P} (hH : IsDivisible H) (n : ℕ) {m : ℕ} (hm : m ≠ 0) :
    Nat.card (tors H (n * m)) = Nat.card (tors H m) * Nat.card (tors H n) := by
  classical
  have key : ∀ y : tors H n, ∃ x : tors H (n * m), (m : ℤ) • (x : P) = (y : P) := by
    intro y
    obtain ⟨x, hxH, hx⟩ := hH m hm (y : P) y.2.1
    refine ⟨⟨x, hxH, ?_⟩, hx⟩
    have : ((n * m : ℕ) : ℤ) • x = (n : ℤ) • ((m : ℤ) • x) := by
      rw [smul_smul]; push_cast; ring_nf
    rw [this, hx]
    exact y.2.2
  choose s hs using key
  have hmem : ∀ (k : tors H m) (y : tors H n), ((k : P) + (s y : P)) ∈ tors H (n * m) := by
    intro k y
    refine ⟨H.add_mem k.2.1 (s y).2.1, ?_⟩
    have hk : ((n * m : ℕ) : ℤ) • (k : P) = 0 := by
      have : ((n * m : ℕ) : ℤ) • (k : P) = (n : ℤ) • ((m : ℤ) • (k : P)) := by
        rw [smul_smul]; push_cast; ring_nf
      rw [this, k.2.2, smul_zero]
    rw [smul_add, hk, (s y).2.2, add_zero]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun p : tors H m × tors H n => (⟨(p.1 : P) + (s p.2 : P), hmem p.1 p.2⟩ : tors H (n * m)))
    ⟨?_, ?_⟩)).symm.trans (Nat.card_prod _ _)
  · rintro ⟨k, y⟩ ⟨k', y'⟩ hkk
    have h : (k : P) + (s y : P) = (k' : P) + (s y' : P) := congrArg Subtype.val hkk
    have hy : (y : P) = (y' : P) := by
      have := congrArg (fun z : P => (m : ℤ) • z) h
      simp only [smul_add, k.2.2, k'.2.2, hs, zero_add] at this
      exact this
    have hy' : y = y' := Subtype.ext hy
    subst hy'
    have : (k : P) = (k' : P) := by
      have := h
      rwa [add_left_inj] at this
    exact Prod.ext (Subtype.ext this) rfl
  · rintro ⟨x, hxH, hx⟩
    have hyn : ((m : ℤ) • x) ∈ tors H n := by
      refine ⟨H.zsmul_mem hxH _, ?_⟩
      have : (n : ℤ) • ((m : ℤ) • x) = ((n * m : ℕ) : ℤ) • x := by
        rw [smul_smul]; push_cast; ring_nf
      rw [this, hx]
    refine ⟨(⟨x - (s ⟨_, hyn⟩ : P), ?_, ?_⟩, ⟨_, hyn⟩), ?_⟩
    · exact H.sub_mem hxH (s ⟨_, hyn⟩).2.1
    · rw [smul_sub, hs ⟨_, hyn⟩, sub_self]
    · exact Subtype.ext (by simp)

/-- **THE TORSION COUNT OF A DIVISIBLE SUBGROUP WITH `p`-TORSION OF ORDER `p`**: it is
`n` at every level. -/
theorem card_tors_eq {H : AddSubgroup P} (hH : IsDivisible H)
    (hp : ∀ p : ℕ, p.Prime → Nat.card (tors H p) = p) :
    ∀ n : ℕ, n ≠ 0 → Nat.card (tors H n) = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hn) with h1 | h1
    · rw [← h1]; exact card_tors_one
    · obtain ⟨q, hq, k, rfl⟩ : ∃ q : ℕ, q.Prime ∧ ∃ k : ℕ, n = k * q :=
        ⟨n.minFac, Nat.minFac_prime (by omega), n / n.minFac, by
          rw [Nat.div_mul_cancel (Nat.minFac_dvd n)]⟩
      have hk0 : k ≠ 0 := by rintro rfl; simp at hn
      have hklt : k < k * q := by
        have h1 : 1 < q := hq.one_lt
        have h2 : 0 < k := Nat.pos_of_ne_zero hk0
        nlinarith
      rw [card_tors_mul hH k hq.ne_zero, hp _ hq, ih k hklt hk0]
      ring

/-- **A GENERATOR OF `H[n]`**: a divisible subgroup whose torsion counts are exactly `n`
has CYCLIC `n`-torsion, generated by an element of order exactly `n`. -/
theorem exists_tors_gen {H : AddSubgroup P} (hcard : ∀ m : ℕ, m ≠ 0 → Nat.card (tors H m) = m)
    {n : ℕ} (hn : n ≠ 0) :
    ∃ g : P, g ∈ H ∧ (n : ℤ) • g = 0 ∧
      (∀ y : P, y ∈ H → (n : ℤ) • y = 0 → ∃ a : ℤ, y = a • g) ∧
      (∀ a : ℤ, a • g = 0 → (n : ℤ) ∣ a) := by
  classical
  have hcn : Nat.card (tors H n) = n := hcard n hn
  haveI : Finite (tors H n) := Nat.finite_of_card_ne_zero (by rw [hcn]; exact hn)
  haveI : Fintype (tors H n) := Fintype.ofFinite _
  have hle : ∀ m : ℕ, 0 < m → #{a : tors H n | m • a = 0} ≤ m := by
    intro m hm
    have hcm : Nat.card (tors H m) = m := hcard m hm.ne'
    haveI : Finite (tors H m) := Nat.finite_of_card_ne_zero (by rw [hcm]; omega)
    set F : {a : tors H n // m • a = 0} → tors H m := fun a => (⟨(a.1 : P), (a.1).2.1, by
          have h0 : (m : ℕ) • ((a.1 : tors H n) : P) = 0 := by
            exact_mod_cast congrArg (fun z : tors H n => (z : P)) a.2
          rw [← natCast_zsmul] at h0
          exact h0⟩ : tors H m) with hF
    have hinj : Function.Injective F := by
      intro a b hab
      have h : ((a.1 : P)) = ((b.1 : P)) := congrArg (fun z : tors H m => (z : P)) hab
      exact Subtype.ext (Subtype.ext h)
    have h1 : Nat.card {a : tors H n // m • a = 0} ≤ Nat.card (tors H m) :=
      Nat.card_le_card_of_injective F hinj
    rw [hcm] at h1
    calc #{a : tors H n | m • a = 0} = Nat.card {a : tors H n // m • a = 0} := by
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      _ ≤ m := h1
  have hcyc : IsAddCyclic (tors H n) := isAddCyclic_of_card_nsmul_eq_zero_le hle
  obtain ⟨g, hg⟩ := hcyc.exists_zsmul_surjective
  refine ⟨(g : P), g.2.1, g.2.2, ?_, ?_⟩
  · intro y hyH hyn
    obtain ⟨a, ha⟩ := hg ⟨y, hyH, hyn⟩
    exact ⟨a, by simpa using congrArg (fun z : tors H n => (z : P)) ha.symm⟩
  · intro a ha
    have hord : addOrderOf g = n :=
      (addOrderOf_eq_card_of_forall_mem_zmultiples
        (fun x => AddSubgroup.mem_zmultiples_iff.mpr (hg x))).trans hcn
    have hz : a • g = 0 := by
      refine Subtype.ext ?_
      simpa using ha
    have hdvd : ((addOrderOf g : ℕ) : ℤ) ∣ a := (addOrderOf_dvd_iff_zsmul_eq_zero).mpr hz
    rwa [hord] at hdvd

/-! ### Two counting lemmas shared by both cases -/

/-- **SPAN PLUS THE RIGHT COUNT IS A BASIS**: if `p` and `q` are `n`-torsion and every
`n`-torsion element is an integral combination of them, they are automatically
INDEPENDENT — the `n²` combinations with coefficients in `[0, n)` already exhaust the `n²`
points of `P[n]`, so none of them can collide. -/
theorem isTorsionBasis_of_span {n : ℕ} (hn : n ≠ 0)
    (hcard : Nat.card {x : P // (n : ℤ) • x = 0} = n ^ 2)
    {p q : P} (hp : (n : ℤ) • p = 0) (hq : (n : ℤ) • q = 0)
    (hspan : ∀ y : P, (n : ℤ) • y = 0 → ∃ a b : ℤ, a • p + b • q = y) :
    IsTorsionBasis n (p, q) := by
  classical
  haveI : Finite {x : P // (n : ℤ) • x = 0} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero 2 hn)
  have hnpos : (0 : ℤ) < (n : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hred : ∀ (a : ℤ) (z : P), (n : ℤ) • z = 0 → (a % (n : ℤ)) • z = a • z := by
    intro a z hz
    rw [Int.emod_def, sub_smul, mul_comm, mul_smul, hz, smul_zero, sub_zero]
  have hmemΦ : ∀ a b : ℤ, (n : ℤ) • (a • p + b • q) = 0 := by
    intro a b
    rw [smul_add, smul_comm, hp, smul_zero, smul_comm, hq, smul_zero, add_zero]
  set Φ : Fin n × Fin n → {x : P // (n : ℤ) • x = 0} := fun ij =>
    ⟨((ij.1 : ℕ) : ℤ) • p + ((ij.2 : ℕ) : ℤ) • q, hmemΦ _ _⟩ with hΦ
  have hsurj : Function.Surjective Φ := by
    rintro ⟨y, hy⟩
    obtain ⟨a, b, hab⟩ := hspan y hy
    have ha0 : 0 ≤ a % (n : ℤ) := Int.emod_nonneg a (by omega)
    have hb0 : 0 ≤ b % (n : ℤ) := Int.emod_nonneg b (by omega)
    have han : a % (n : ℤ) < (n : ℤ) := Int.emod_lt_of_pos a hnpos
    have hbn : b % (n : ℤ) < (n : ℤ) := Int.emod_lt_of_pos b hnpos
    refine ⟨(⟨(a % (n : ℤ)).toNat, by omega⟩, ⟨(b % (n : ℤ)).toNat, by omega⟩), ?_⟩
    refine Subtype.ext ?_
    show (((a % (n : ℤ)).toNat : ℤ)) • p + (((b % (n : ℤ)).toNat : ℤ)) • q = y
    rw [Int.toNat_of_nonneg ha0, Int.toNat_of_nonneg hb0, hred a p hp, hred b q hq]
    exact hab
  have hbij : Function.Bijective Φ := by
    refine Nat.bijective_iff_surjective_and_card _ |>.mpr ⟨hsurj, ?_⟩
    rw [hcard, Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin]
    ring
  refine ⟨hp, hq, hspan, ?_⟩
  intro a b hab
  have hab' : a • p + b • q = 0 := hab
  have ha0 : 0 ≤ a % (n : ℤ) := Int.emod_nonneg a (by omega)
  have hb0 : 0 ≤ b % (n : ℤ) := Int.emod_nonneg b (by omega)
  have han : a % (n : ℤ) < (n : ℤ) := Int.emod_lt_of_pos a hnpos
  have hbn : b % (n : ℤ) < (n : ℤ) := Int.emod_lt_of_pos b hnpos
  have hzero : Φ (⟨(a % (n : ℤ)).toNat, by omega⟩, ⟨(b % (n : ℤ)).toNat, by omega⟩) =
      Φ (⟨0, Nat.pos_of_ne_zero hn⟩, ⟨0, Nat.pos_of_ne_zero hn⟩) := by
    refine Subtype.ext ?_
    show (((a % (n : ℤ)).toNat : ℤ)) • p + (((b % (n : ℤ)).toNat : ℤ)) • q
      = ((0 : ℕ) : ℤ) • p + ((0 : ℕ) : ℤ) • q
    rw [Int.toNat_of_nonneg ha0, Int.toNat_of_nonneg hb0, hred a p hp, hred b q hq, hab']
    simp
  have heq := hbij.1 hzero
  have hafin : (a % (n : ℤ)).toNat = 0 := by
    have := congrArg (fun z : Fin n × Fin n => (z.1 : ℕ)) heq
    simpa using this
  have hbfin : (b % (n : ℤ)).toNat = 0 := by
    have := congrArg (fun z : Fin n × Fin n => (z.2 : ℕ)) heq
    simpa using this
  constructor
  · refine Int.dvd_of_emod_eq_zero ?_
    omega
  · refine Int.dvd_of_emod_eq_zero ?_
    omega

/-- **A DIVISIBLE SUBGROUP WITH `p²` POINTS OF `p`-TORSION CONTAINS THE WHOLE OF
`P[p²]`**: its own `p²`-torsion then has `p⁴` points, which is all of them. -/
theorem mem_of_card_tors_prime {H : AddSubgroup P}
    (hcard : ∀ n : ℕ, n ≠ 0 → Nat.card {x : P // (n : ℤ) • x = 0} = n ^ 2)
    (hH : IsDivisible H) {p : ℕ} (hp : p.Prime) (hcardH : Nat.card (tors H p) = p ^ 2) :
    ∀ x : P, ((p ^ 2 : ℕ) : ℤ) • x = 0 → x ∈ H := by
  intro x hx
  have hp0 : p ≠ 0 := hp.ne_zero
  have hcard2 : Nat.card (tors H (p ^ 2)) = p ^ 2 * p ^ 2 := by
    rw [show p ^ 2 = p * p by ring, card_tors_mul hH p hp0, hcardH]; ring
  have hcardP : Nat.card {y : P // ((p ^ 2 : ℕ) : ℤ) • y = 0} = (p ^ 2) ^ 2 :=
    hcard _ (pow_ne_zero 2 hp0)
  haveI : Finite {y : P // ((p ^ 2 : ℕ) : ℤ) • y = 0} :=
    Nat.finite_of_card_ne_zero (by rw [hcardP]; exact pow_ne_zero 2 (pow_ne_zero 2 hp0))
  haveI : Finite (tors H (p ^ 2)) :=
    Nat.finite_of_card_ne_zero (by
      rw [hcard2]; exact Nat.mul_ne_zero (pow_ne_zero 2 hp0) (pow_ne_zero 2 hp0))
  have hbij : Function.Bijective
      (fun y : tors H (p ^ 2) => (⟨(y : P), y.2.2⟩ : {z : P // ((p ^ 2 : ℕ) : ℤ) • z = 0})) := by
    refine Nat.bijective_iff_injective_and_card _ |>.mpr ⟨?_, ?_⟩
    · intro y z hyz
      have hv : ((y : P)) = ((z : P)) :=
        congrArg (fun w : {t : P // ((p ^ 2 : ℕ) : ℤ) • t = 0} => (w : P)) hyz
      exact Subtype.ext hv
    · rw [hcard2, hcardP]; ring
  obtain ⟨y, hy⟩ := hbij.2 ⟨x, hx⟩
  have hval : (y : P) = x := congrArg Subtype.val hy
  rw [← hval]
  exact y.2.1

/-- **THE `p`-TORSION COUNT OF EACH SIDE OF A `±1`-SPLITTING IS EXACTLY `p`**: the count
divides `p²`, and the two extreme values say precisely that `c = 1` (resp. `c = −1`) on
`P[p²]`, which `hne_id` (resp. `hne_neg`) read at `p² ≥ 3` forbids. -/
theorem card_tors_prime_eq_of_split {A B : AddSubgroup P} {c : P →+ P}
    (hcard : ∀ n : ℕ, n ≠ 0 → Nat.card {x : P // (n : ℤ) • x = 0} = n ^ 2)
    (hne_id : ∀ n : ℕ, 3 ≤ n → ∃ x : P, (n : ℤ) • x = 0 ∧ c x ≠ x)
    (hne_neg : ∀ n : ℕ, 3 ≤ n → ∃ x : P, (n : ℤ) • x = 0 ∧ c x ≠ -x)
    (hdivA : IsDivisible A) (hdivB : IsDivisible B)
    (hcA : ∀ x ∈ A, c x = x) (hcB : ∀ x ∈ B, c x = -x)
    {p : ℕ} (hp : p.Prime) (hmul : Nat.card (tors A p) * Nat.card (tors B p) = p ^ 2) :
    Nat.card (tors A p) = p := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hdvd : Nat.card (tors A p) ∣ p ^ 2 := ⟨Nat.card (tors B p), hmul.symm⟩
  obtain ⟨i, hi, hval⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hsq : (3 : ℕ) ≤ p ^ 2 := by
    have h2 := hp.two_le
    calc (3 : ℕ) ≤ 2 ^ 2 := by norm_num
    _ ≤ p ^ 2 := Nat.pow_le_pow_left h2 2
  interval_cases i
  · exfalso
    have hB2 : Nat.card (tors B p) = p ^ 2 := by
      rw [hval] at hmul; simpa using hmul
    obtain ⟨x, hx, hxne⟩ := hne_neg (p ^ 2) hsq
    exact hxne (hcB x (mem_of_card_tors_prime hcard hdivB hp hB2 x hx))
  · simpa using hval
  · exfalso
    have hA2 : Nat.card (tors A p) = p ^ 2 := by rw [hval]
    obtain ⟨x, hx, hxne⟩ := hne_id (p ^ 2) hsq
    exact hxne (hcA x (mem_of_card_tors_prime hcard hdivA hp hA2 x hx))

/-! ### `ε = false`: the involution is `1 − 2f` for an idempotent `f` -/

/-- **HALVING `1 − c`** (`ε = false`): if the involution `c` FIXES the `2`-torsion then
`1 − c` kills it, hence factors through multiplication by `2` — divisibility of `P`
turns that into an endomorphism `f` with `2f = 1 − c`.  `f` is IDEMPOTENT: `4(f² − f)`
vanishes identically by a two-line computation with `c² = 1`, and `End P` is
torsion-free because every `x` is `4u`. -/
theorem exists_halfEndo (hdiv : ∀ m : ℕ, m ≠ 0 → ∀ y : P, ∃ x : P, (m : ℤ) • x = y)
    (c : P →+ P) (hc : ∀ x, c (c x) = x) (hfix : ∀ x : P, (2 : ℤ) • x = 0 → c x = x) :
    ∃ f : P →+ P, (∀ x, (2 : ℤ) • f x = x - c x) ∧ (∀ x, f (f x) = f x) := by
  classical
  have h2 : (2 : ℕ) ≠ 0 := two_ne_zero
  choose hf hhf0 using fun y : P => hdiv 2 h2 y
  have hhf : ∀ y : P, (2 : ℤ) • hf y = y := by
    intro y; have := hhf0 y; push_cast at this; exact this
  have hspec : ∀ x x₀ : P, (2 : ℤ) • x₀ = x → hf x - c (hf x) = x₀ - c x₀ := by
    intro x x₀ hx₀
    have hdiff : (2 : ℤ) • (hf x - x₀) = 0 := by
      rw [smul_sub, hhf x, hx₀, sub_self]
    have h' : c (hf x) - c x₀ = hf x - x₀ := by
      have := hfix _ hdiff
      rwa [map_sub] at this
    have e : (hf x - c (hf x)) - (x₀ - c x₀) = (hf x - x₀) - (c (hf x) - c x₀) := by abel
    have e0 : (hf x - c (hf x)) - (x₀ - c x₀) = 0 := by rw [e, h', sub_self]
    exact sub_eq_zero.mp e0
  have hadd : ∀ x y : P,
      hf (x + y) - c (hf (x + y)) = (hf x - c (hf x)) + (hf y - c (hf y)) := by
    intro x y
    rw [hspec (x + y) (hf x + hf y) (by rw [smul_add, hhf, hhf]), map_add]
    abel
  refine ⟨AddMonoidHom.mk' (fun x => hf x - c (hf x)) hadd, ?_, ?_⟩
  · intro x
    show (2 : ℤ) • (hf x - c (hf x)) = x - c x
    rw [smul_sub, hhf, ← map_zsmul, hhf]
  · intro x
    set f : P →+ P := AddMonoidHom.mk' (fun x => hf x - c (hf x)) hadd with hfdef
    have h2f : ∀ y : P, (2 : ℤ) • f y = y - c y := by
      intro y
      show (2 : ℤ) • (hf y - c (hf y)) = y - c y
      rw [smul_sub, hhf, ← map_zsmul, hhf]
    have h4 : ∀ y : P, (4 : ℤ) • f (f y) = (4 : ℤ) • f y := by
      intro y
      have e4 : ∀ z : P, (4 : ℤ) • z = (2 : ℤ) • ((2 : ℤ) • z) := by
        intro z; rw [smul_smul]; norm_num
      rw [e4, e4, h2f, smul_sub, h2f, ← map_zsmul, h2f, map_sub, hc]
      abel
    obtain ⟨u, hu0⟩ := hdiv 4 (by norm_num) x
    have hu : (4 : ℤ) • u = x := by push_cast at hu0; exact hu0
    have hx : f (f x) = (4 : ℤ) • f (f u) := by
      rw [← hu, map_zsmul, map_zsmul]
    have hx' : f x = (4 : ℤ) • f u := by rw [← hu, map_zsmul]
    rw [hx, hx', h4]

/-- **THE `ε = false` FRAME**: an involution fixing the whole `2`-torsion splits `P` as
`ker f ⊕ im f` with `c = ±1` on the two summands, and a generator of each summand's
`n`-torsion is an adapted frame with `ε = false`. -/
theorem exists_frame_false
    (hdiv : ∀ m : ℕ, m ≠ 0 → ∀ y : P, ∃ x : P, (m : ℤ) • x = y)
    (hcard : ∀ n : ℕ, n ≠ 0 → Nat.card {x : P // (n : ℤ) • x = 0} = n ^ 2)
    (c : P →+ P) (hc : ∀ x, c (c x) = x)
    (hne_id : ∀ n : ℕ, 3 ≤ n → ∃ x : P, (n : ℤ) • x = 0 ∧ c x ≠ x)
    (hne_neg : ∀ n : ℕ, 3 ≤ n → ∃ x : P, (n : ℤ) • x = 0 ∧ c x ≠ -x)
    (hfix : ∀ x : P, (2 : ℤ) • x = 0 → c x = x)
    (n : ℕ) (hn : n ≠ 0) :
    ∃ pq : P × P, IsFrame false c n pq := by
  classical
  obtain ⟨f, h2f, hff⟩ := exists_halfEndo hdiv c hc hfix
  -- `c = 1 − 2f`
  have hcf : ∀ x : P, c x = x - (2 : ℤ) • f x := by
    intro x; rw [h2f]; abel
  set A : AddSubgroup P := f.ker with hA
  set B : AddSubgroup P := f.range with hB
  have hmemA : ∀ x : P, x ∈ A ↔ f x = 0 := fun _ => AddMonoidHom.mem_ker
  have hmemB : ∀ x : P, x ∈ B ↔ ∃ y, f y = x := fun _ => AddMonoidHom.mem_range
  have hcA : ∀ x : P, x ∈ A → c x = x := by
    intro x hx
    rw [hcf, (hmemA x).mp hx, smul_zero, sub_zero]
  have hcB : ∀ x : P, x ∈ B → c x = -x := by
    intro x hx
    obtain ⟨y, hy⟩ := (hmemB x).mp hx
    have hfx : f x = x := by rw [← hy, hff]
    rw [hcf, hfx]
    have : (2 : ℤ) • x = x + x := by rw [two_smul]
    rw [this]; abel
  have hsplit : ∀ x : P, (x - f x) ∈ A ∧ f x ∈ B ∧ (x - f x) + f x = x := by
    intro x
    refine ⟨?_, (hmemB _).mpr ⟨x, rfl⟩, by abel⟩
    rw [hmemA, map_sub, hff, sub_self]
  have hinter : ∀ x : P, x ∈ A → x ∈ B → x = 0 := by
    intro x hxA hxB
    obtain ⟨y, hy⟩ := (hmemB x).mp hxB
    have : f x = x := by rw [← hy, hff]
    rw [← this]
    exact (hmemA x).mp hxA
  -- divisibility of the two summands
  have hdivA : IsDivisible A := by
    intro m hm y hy
    obtain ⟨w, hw⟩ := hdiv m hm y
    refine ⟨w - f w, by rw [hmemA, map_sub, hff, sub_self], ?_⟩
    rw [smul_sub, hw, ← map_zsmul, hw, (hmemA y).mp hy, sub_zero]
  have hdivB : IsDivisible B := by
    intro m hm y hy
    obtain ⟨z, hz⟩ := (hmemB y).mp hy
    obtain ⟨w, hw⟩ := hdiv m hm z
    refine ⟨f w, (hmemB _).mpr ⟨w, rfl⟩, ?_⟩
    rw [← map_zsmul, hw, hz]
  -- the two torsion counts multiply to `n²`
  have hcardAB : ∀ m : ℕ, m ≠ 0 →
      Nat.card (tors A m) * Nat.card (tors B m) = m ^ 2 := by
    intro m hm
    rw [← hcard m hm]
    refine (Nat.card_prod _ _).symm.trans (Nat.card_congr (Equiv.ofBijective
      (fun p : tors A m × tors B m =>
        (⟨(p.1 : P) + (p.2 : P), by
          rw [smul_add, p.1.2.2, p.2.2.2, add_zero]⟩ : {x : P // (m : ℤ) • x = 0}))
      ⟨?_, ?_⟩))
    · rintro ⟨⟨a, haA, ha⟩, ⟨b, hbB, hb⟩⟩ ⟨⟨a', ha'A, ha'⟩, ⟨b', hb'B, hb'⟩⟩ hab
      have h : a + b = a' + b' := congrArg Subtype.val hab
      have hd : a - a' = b' - b := by
        have : a - a' - (b' - b) = 0 := by
          have e : a - a' - (b' - b) = (a + b) - (a' + b') := by abel
          rw [e, h, sub_self]
        exact sub_eq_zero.mp this
      have hdA : (a - a') ∈ A := A.sub_mem haA ha'A
      have hdB : (a - a') ∈ B := by rw [hd]; exact B.sub_mem hb'B hbB
      have hzero := hinter _ hdA hdB
      have haa : a = a' := by
        have := sub_eq_zero.mp hzero
        exact this
      subst haa
      have hbb : b = b' := by
        have : b = b' := by
          have := h
          rwa [add_right_inj] at this
        exact this
      subst hbb
      rfl
    · rintro ⟨x, hx⟩
      obtain ⟨hxA, hxB, hxsum⟩ := hsplit x
      refine ⟨(⟨x - f x, hxA, ?_⟩, ⟨f x, hxB, ?_⟩), Subtype.ext hxsum⟩
      · rw [smul_sub, hx, ← map_zsmul, hx, map_zero, sub_zero]
      · rw [← map_zsmul, hx, map_zero]
  -- at every prime both summands have exactly `p` points of `p`-torsion
  have hprimeA : ∀ p : ℕ, p.Prime → Nat.card (tors A p) = p := fun p hp =>
    card_tors_prime_eq_of_split hcard hne_id hne_neg hdivA hdivB hcA hcB hp (hcardAB p hp.ne_zero)
  have hprimeB : ∀ p : ℕ, p.Prime → Nat.card (tors B p) = p := by
    intro p hp
    have hmul := hcardAB p hp.ne_zero
    rw [hprimeA p hp] at hmul
    have hp0 : 0 < p := hp.pos
    have : p * Nat.card (tors B p) = p * p := by rw [hmul]; ring
    exact Nat.eq_of_mul_eq_mul_left hp0 this
  -- generators
  obtain ⟨p, hpA, hpn, hpspan, hpord⟩ :=
    exists_tors_gen (card_tors_eq hdivA hprimeA) hn
  obtain ⟨q, hqB, hqn, hqspan, hqord⟩ :=
    exists_tors_gen (card_tors_eq hdivB hprimeB) hn
  refine ⟨(p, q), ⟨⟨hpn, hqn, ?_, ?_⟩, hcA p hpA, ?_⟩⟩
  · intro y hy
    obtain ⟨hyA, hyB, hysum⟩ := hsplit y
    obtain ⟨a, ha⟩ := hpspan (y - f y) hyA
      (by rw [smul_sub, hy, ← map_zsmul, hy, map_zero, sub_zero])
    obtain ⟨b, hb⟩ := hqspan (f y) hyB (by rw [← map_zsmul, hy, map_zero])
    exact ⟨a, b, by rw [← ha, ← hb]; exact hysum⟩
  · intro a b hab
    have h1 : a • p = -(b • q) := by
      have h0 : a • p + b • q = 0 := hab
      have := congrArg (fun z : P => z - b • q) h0
      simpa using this
    have hA' : a • p ∈ A := A.zsmul_mem hpA a
    have hB' : a • p ∈ B := by rw [h1]; exact B.neg_mem (B.zsmul_mem hqB b)
    have hz := hinter _ hA' hB'
    refine ⟨hpord a hz, hqord b ?_⟩
    have : b • q = 0 := by
      have : -(b • q) = 0 := by rw [← h1]; exact hz
      simpa using this
    exact this
  · simpa using hcB q hqB

/-! ### `ε = true`: both eigen-subgroups are divisible -/

/-- Divisibility follows from divisibility by every prime. -/
theorem isDivisible_of_primes {H : AddSubgroup P}
    (h : ∀ p : ℕ, p.Prime → ∀ y ∈ H, ∃ x ∈ H, (p : ℤ) • x = y) : IsDivisible H := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm y hy
    rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr hm) with h1 | h1
    · exact ⟨y, hy, by rw [← h1]; simp⟩
    · obtain ⟨q, hq, k, rfl⟩ : ∃ q : ℕ, q.Prime ∧ ∃ k : ℕ, m = k * q :=
        ⟨m.minFac, Nat.minFac_prime (by omega), m / m.minFac, by
          rw [Nat.div_mul_cancel (Nat.minFac_dvd m)]⟩
      have hk0 : k ≠ 0 := by rintro rfl; simp at hm
      have hklt : k < k * q := by
        have h1' : 1 < q := hq.one_lt
        have h2' : 0 < k := Nat.pos_of_ne_zero hk0
        nlinarith
      obtain ⟨z, hz, hzy⟩ := h q hq y hy
      obtain ⟨x, hx, hxz⟩ := ih k hklt hk0 z hz
      refine ⟨x, hx, ?_⟩
      have hsm : ((k * q : ℕ) : ℤ) • x = (q : ℤ) • ((k : ℤ) • x) := by
        rw [smul_smul]; push_cast; ring_nf
      rw [hsm, hxz, hzy]

/-- In a two-element type everything is one of two distinct given elements. -/
theorem eq_or_eq_of_card_eq_two {α : Type*} [Finite α] (h : Nat.card α = 2) {a b : α}
    (hab : a ≠ b) (x : α) : x = a ∨ x = b := by
  classical
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective (fun i : Fin 3 => ![a, b, x] i) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [hab.symm, hcon.1, hcon.2, Ne.symm hcon.1, Ne.symm hcon.2]
  have h3 : Nat.card (Fin 3) ≤ Nat.card α := Nat.card_le_card_of_injective _ hinj
  rw [h, Nat.card_eq_fintype_card, Fintype.card_fin] at h3
  omega

/-- The fixed subgroup of an endomorphism. -/
def fixSub (c : P →+ P) : AddSubgroup P where
  carrier := {x | c x = x}
  zero_mem' := map_zero c
  add_mem' := fun {a b} ha hb => by
    show c (a + b) = a + b
    rw [map_add, show c a = a from ha, show c b = b from hb]
  neg_mem' := fun {a} ha => by
    show c (-a) = -a
    rw [map_neg, show c a = a from ha]

theorem mem_fixSub_neg {c : P →+ P} {x : P} : x ∈ fixSub (-c) ↔ c x = -x := by
  show (-c) x = x ↔ c x = -x
  rw [AddMonoidHom.neg_apply, neg_eq_iff_eq_neg]

theorem involutive_neg {c : P →+ P} (hc : ∀ x, c (c x) = x) : ∀ x, (-c) ((-c) x) = x := by
  intro x
  show -(c (-(c x))) = x
  rw [map_neg, hc]
  abel

/-- **THE `ε = true` `2`-TORSION PICTURE**: if only `2` of the `4` points of `P[2]` are fixed
then `c − 1` maps `P[2]` ONTO the fixed part of `P[2]` — the fixed part is `{0, cw − w}`
for any unfixed `w`, and both are visibly of the form `c t − t`. -/
theorem exists_sub_eq_of_card_fix_two {c : P →+ P} (hc : ∀ x, c (c x) = x)
    (hcard2 : Nat.card {x : P // (2 : ℤ) • x = 0} = 4)
    (hfix2 : Nat.card {x : P // (2 : ℤ) • x = 0 ∧ c x = x} = 2) :
    ∀ u : P, (2 : ℤ) • u = 0 → c u = u → ∃ t : P, (2 : ℤ) • t = 0 ∧ c t - t = u := by
  classical
  haveI hfinS : Finite {x : P // (2 : ℤ) • x = 0 ∧ c x = x} :=
    Nat.finite_of_card_ne_zero (by rw [hfix2]; omega)
  have hex : ∃ w : P, (2 : ℤ) • w = 0 ∧ c w ≠ w := by
    by_contra hcon
    push Not at hcon
    haveI : Finite {x : P // (2 : ℤ) • x = 0} :=
      Nat.finite_of_card_ne_zero (by rw [hcard2]; omega)
    have hinj : Function.Injective (fun x : {x : P // (2 : ℤ) • x = 0} =>
        (⟨(x : P), x.2, hcon (x : P) x.2⟩ : {x : P // (2 : ℤ) • x = 0 ∧ c x = x})) := by
      intro x y hxy
      exact Subtype.ext
        (congrArg (fun z : {x : P // (2 : ℤ) • x = 0 ∧ c x = x} => (z : P)) hxy)
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [hcard2, hfix2] at hle
    omega
  obtain ⟨w, hw2, hwne⟩ := hex
  intro u hu2 hufix
  set z := c w - w with hzdef
  have hz2 : (2 : ℤ) • z = 0 := by
    rw [hzdef, smul_sub, ← map_zsmul, hw2, map_zero, sub_self]
  have hznz : z = -z := by
    have h2 : z + z = 0 := by rw [← two_smul ℤ z]; exact hz2
    exact add_eq_zero_iff_eq_neg.mp h2
  have hzfix : c z = z := by
    have h1 : c z = -z := by
      rw [hzdef, map_sub, hc]
      abel
    rw [h1, ← hznz]
  have hzne : z ≠ 0 := by
    rw [hzdef]
    exact sub_ne_zero.mpr hwne
  have hne : (⟨0, by simp, by simp⟩ : {x : P // (2 : ℤ) • x = 0 ∧ c x = x}) ≠
      ⟨z, hz2, hzfix⟩ := by
    intro hh
    exact hzne (congrArg (fun t : {x : P // (2 : ℤ) • x = 0 ∧ c x = x} => (t : P)) hh).symm
  rcases eq_or_eq_of_card_eq_two hfix2 hne ⟨u, hu2, hufix⟩ with hcase | hcase
  · refine ⟨0, by simp, ?_⟩
    have : u = 0 := congrArg (fun t : {x : P // (2 : ℤ) • x = 0 ∧ c x = x} => (t : P)) hcase
    rw [this, map_zero, sub_zero]
  · refine ⟨w, hw2, ?_⟩
    have : u = z := congrArg (fun t : {x : P // (2 : ℤ) • x = 0 ∧ c x = x} => (t : P)) hcase
    rw [this, hzdef]

/-- **DIVISIBILITY OF THE FIXED SUBGROUP** (`ε = true`).  Dividing a fixed `y` by an ODD
prime is a shear by `(p+1)/2` times the error `c x₀ − x₀`; dividing by `2` is where the
`ε = true` hypothesis enters, through `himg`. -/
theorem isDivisible_fixSub (hdiv : ∀ m : ℕ, m ≠ 0 → ∀ y : P, ∃ x : P, (m : ℤ) • x = y)
    {c : P →+ P} (hc : ∀ x, c (c x) = x)
    (himg : ∀ u : P, (2 : ℤ) • u = 0 → c u = u → ∃ t : P, (2 : ℤ) • t = 0 ∧ c t - t = u) :
    IsDivisible (fixSub c) := by
  refine isDivisible_of_primes ?_
  intro p hp y hy
  have hyfix : c y = y := hy
  obtain ⟨x₀, hx₀⟩ := hdiv p hp.ne_zero y
  set u := c x₀ - x₀ with hudef
  have hup : (p : ℤ) • u = 0 := by
    rw [hudef, smul_sub, ← map_zsmul, hx₀, hyfix, sub_self]
  have hcx : c x₀ = x₀ + u := by rw [hudef]; abel
  have hcu : c u = -u := by
    rw [hudef, map_sub, hc]
    abel
  rcases hp.eq_two_or_odd' with rfl | hodd
  · have hu2 : (2 : ℤ) • u = 0 := by have h := hup; push_cast at h; exact h
    have hufix : c u = u := by
      rw [hcu]
      have h2 : u + u = 0 := by rw [← two_smul ℤ u]; exact hu2
      exact (add_eq_zero_iff_eq_neg.mp h2).symm
    obtain ⟨t, ht2, htu⟩ := himg u hu2 hufix
    have hx₀' : (2 : ℤ) • x₀ = y := by have h := hx₀; push_cast at h; exact h
    refine ⟨x₀ - t, ?_, ?_⟩
    · show c (x₀ - t) = x₀ - t
      rw [map_sub]
      have e : c x₀ - c t - (x₀ - t) = (c x₀ - x₀) - (c t - t) := by abel
      have e0 : c x₀ - c t - (x₀ - t) = 0 := by rw [e, ← hudef, htu, sub_self]
      exact sub_eq_zero.mp e0
    · have : ((2 : ℕ) : ℤ) • (x₀ - t) = (2 : ℤ) • (x₀ - t) := by norm_num
      rw [this, smul_sub, hx₀', ht2, sub_zero]
  · obtain ⟨k, hk⟩ := hodd
    have hpu : (2 * (k : ℤ) + 1) • u = 0 := by
      rw [show (2 * (k : ℤ) + 1) = ((p : ℕ) : ℤ) by rw [hk]; push_cast; ring]
      exact hup
    have key : ((k : ℤ) + 1) • u + ((k : ℤ) + 1) • u = u := by
      rw [← add_smul, show ((k : ℤ) + 1) + ((k : ℤ) + 1) = (2 * (k : ℤ) + 1) + 1 by ring,
        add_smul, hpu, one_smul, zero_add]
    refine ⟨x₀ + ((k : ℤ) + 1) • u, ?_, ?_⟩
    · show c (x₀ + ((k : ℤ) + 1) • u) = x₀ + ((k : ℤ) + 1) • u
      rw [map_add, map_zsmul, hcu, hcx, smul_neg]
      have e : (x₀ + u + -(((k : ℤ) + 1) • u)) - (x₀ + ((k : ℤ) + 1) • u)
          = u - (((k : ℤ) + 1) • u + ((k : ℤ) + 1) • u) := by abel
      have e0 : (x₀ + u + -(((k : ℤ) + 1) • u)) - (x₀ + ((k : ℤ) + 1) • u) = 0 := by
        rw [e, key, sub_self]
      exact sub_eq_zero.mp e0
    · rw [smul_add, hx₀, smul_comm, hup, smul_zero, add_zero]

/-! ### `ε = true`: the frame at odd levels and at `2`-power levels -/

/-- For `m` ODD, multiplication by `m` is the identity on the `2`-torsion, so a `2`-torsion
`m`-torsion element vanishes: the two eigen-subgroups are INDEPENDENT at odd levels. -/
theorem eq_zero_of_fix_and_neg {c : P →+ P} {m : ℕ} (hm : Odd m) {x : P}
    (hfix : c x = x) (hneg : c x = -x) (hmx : (m : ℤ) • x = 0) : x = 0 := by
  obtain ⟨k, hk⟩ := hm
  have h2 : (2 : ℤ) • x = 0 := by
    have hxx : x = -x := hfix.symm.trans hneg
    have hsum : x + x = 0 := by nth_rewrite 1 [hxx]; abel
    rw [two_smul]; exact hsum
  have hmid : (m : ℤ) • x = x := by
    rw [show ((m : ℕ) : ℤ) = (k : ℤ) * 2 + 1 by rw [hk]; push_cast; ring, add_smul, mul_smul, h2,
      smul_zero, one_smul, zero_add]
  rw [← hmid]; exact hmx

/-- At an ODD level the `±1`-eigen-subgroups SPAN: `x = j(x + cx) + j(x − cx)` with `2j ≡ 1`. -/
theorem exists_split_odd {c : P →+ P} (hc : ∀ x, c (c x) = x) {m : ℕ} {j : ℤ}
    (hj : (2 * j - 1 : ℤ) = (m : ℕ)) (y : P) (hy : (m : ℤ) • y = 0) :
    ∃ a b : P, c a = a ∧ c b = -b ∧ (m : ℤ) • a = 0 ∧ (m : ℤ) • b = 0 ∧ a + b = y := by
  refine ⟨j • (y + c y), j • (y - c y), ?_, ?_, ?_, ?_, ?_⟩
  · have e : c y + y = y + c y := by abel
    rw [map_zsmul, map_add, hc, e]
  · rw [map_zsmul, map_sub, hc, smul_sub, smul_sub, neg_sub]
  · rw [smul_comm, smul_add, hy, ← map_zsmul, hy, map_zero, add_zero, smul_zero]
  · rw [smul_comm, smul_sub, hy, ← map_zsmul, hy, map_zero, sub_zero, smul_zero]
  · rw [← smul_add]
    have e : (y + c y) + (y - c y) = (2 : ℤ) • y := by rw [two_smul]; abel
    rw [e, smul_smul]
    have e2 : j * 2 = (m : ℤ) + 1 := by rw [← hj]; ring
    rw [e2, add_smul, hy, one_smul, zero_add]

/-- **THE `ε = true` FRAME AT AN ODD LEVEL**: generators of the two eigen-subgroups, the
second sheared by `½` so that `c q = p − q`. -/
theorem exists_frame_odd {c : P →+ P} (hc : ∀ x, c (c x) = x)
    (hcard : ∀ n : ℕ, n ≠ 0 → Nat.card {x : P // (n : ℤ) • x = 0} = n ^ 2)
    (hcardF : ∀ n : ℕ, n ≠ 0 → Nat.card (tors (fixSub c) n) = n)
    (hcardG : ∀ n : ℕ, n ≠ 0 → Nat.card (tors (fixSub (-c)) n) = n)
    {m : ℕ} (hm0 : m ≠ 0) (hm : Odd m) :
    ∃ pq : P × P, IsFrame true c m pq := by
  obtain ⟨k, hk⟩ := hm
  obtain ⟨j, hj⟩ : ∃ j : ℤ, (2 * j - 1 : ℤ) = (m : ℕ) :=
    ⟨(k : ℤ) + 1, by rw [hk]; push_cast; ring⟩
  obtain ⟨p, hpF, hpn, hpspan, hpord⟩ := exists_tors_gen hcardF hm0
  obtain ⟨g, hgG, hgn, hgspan, hgord⟩ := exists_tors_gen hcardG hm0
  have hcp : c p = p := hpF
  have hcg : c g = -g := mem_fixSub_neg.mp hgG
  refine ⟨(p, j • p + g), ?_, hcp, ?_⟩
  · refine isTorsionBasis_of_span hm0 (hcard m hm0) hpn ?_ ?_
    · rw [smul_add, smul_comm, hpn, smul_zero, hgn, add_zero]
    · intro y hy
      obtain ⟨a, b, hafix, hbneg, han, hbn, hsum⟩ := exists_split_odd hc hj y hy
      obtain ⟨α, hα⟩ := hpspan a hafix han
      obtain ⟨β, hβ⟩ := hgspan b (mem_fixSub_neg.mpr hbneg) hbn
      refine ⟨α - β * j, β, ?_⟩
      rw [sub_smul, smul_add, mul_comm, mul_smul]
      have e : α • p - j • (β • p) + (β • (j • p) + β • g) = α • p + β • g := by
        rw [smul_comm j β p]
        abel
      rw [e, ← hα, ← hβ, hsum]
  · show c (j • p + g) = (if true then p else 0) - (j • p + g)
    rw [if_pos rfl, map_add, map_zsmul, hcp, hcg]
    have h2j : (j + j) • p = p := by
      rw [show (j + j : ℤ) = ((m : ℕ) : ℤ) + 1 by rw [← hj]; ring, add_smul, hpn, one_smul,
        zero_add]
    have e : (j • p + -g) - (p - (j • p + g)) = (j + j) • p - p := by
      rw [add_smul]
      abel
    have e0 : (j • p + -g) - (p - (j • p + g)) = 0 := by rw [e, h2j, sub_self]
    exact sub_eq_zero.mp e0

/-- Some `2`-torsion element is not fixed, when only `2` of the `4` are. -/
theorem exists_unfixed_two_torsion {c : P →+ P}
    (hcard2 : Nat.card {x : P // (2 : ℤ) • x = 0} = 4)
    (hfix2 : Nat.card {x : P // (2 : ℤ) • x = 0 ∧ c x = x} = 2) :
    ∃ w : P, (2 : ℤ) • w = 0 ∧ c w ≠ w := by
  classical
  by_contra hcon
  push Not at hcon
  haveI : Finite {x : P // (2 : ℤ) • x = 0 ∧ c x = x} :=
    Nat.finite_of_card_ne_zero (by rw [hfix2]; omega)
  have hinj : Function.Injective (fun x : {x : P // (2 : ℤ) • x = 0} =>
      (⟨(x : P), x.2, hcon (x : P) x.2⟩ : {x : P // (2 : ℤ) • x = 0 ∧ c x = x})) := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : {x : P // (2 : ℤ) • x = 0 ∧ c x = x} => (z : P)) hxy)
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [hcard2, hfix2] at hle
  omega

/-- In a four-element type everything is one of four distinct given elements. -/
theorem eq_or_of_card_eq_four {α : Type*} [Finite α] (h : Nat.card α = 4) {a b c d : α}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (x : α) : x = a ∨ x = b ∨ x = c ∨ x = d := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hxa, hxb, hxc, hxd⟩ := hcon
  have hinj : Function.Injective (fun i : Fin 5 => ![a, b, c, d, x] i) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have h5 : Nat.card (Fin 5) ≤ Nat.card α := Nat.card_le_card_of_injective _ hinj
  rw [h, Nat.card_eq_fintype_card, Fintype.card_fin] at h5
  omega

/-- **`w` AND `c w` SPAN THE `2`-TORSION** when `c w ≠ w`: the four elements `0, w, cw, w + cw`
are distinct, hence all of `P[2]`. -/
theorem span_two_torsion {c : P →+ P} (hc : ∀ x, c (c x) = x)
    (hcard2 : Nat.card {x : P // (2 : ℤ) • x = 0} = 4)
    {w : P} (hw2 : (2 : ℤ) • w = 0) (hwne : c w ≠ w) :
    ∀ x : P, (2 : ℤ) • x = 0 → ∃ a b : ℤ, a • w + b • (c w) = x := by
  classical
  haveI : Finite {x : P // (2 : ℤ) • x = 0} :=
    Nat.finite_of_card_ne_zero (by rw [hcard2]; omega)
  have hcw2 : (2 : ℤ) • c w = 0 := by rw [← map_zsmul, hw2, map_zero]
  have hwnz : w ≠ 0 := by
    intro h
    rw [h, map_zero] at hwne
    exact hwne rfl
  have hcwnz : c w ≠ 0 := by
    intro h
    have : w = 0 := by rw [← hc w, h, map_zero]
    exact hwnz this
  have hsumnz : w + c w ≠ 0 := by
    intro h
    have h1 : c w = -w := by
      have := h
      rw [add_comm] at this
      exact add_eq_zero_iff_eq_neg.mp this
    have h2 : -w = w := by
      have : w + w = 0 := by rw [← two_smul ℤ w]; exact hw2
      exact (add_eq_zero_iff_eq_neg.mp this).symm
    rw [h1, h2] at hwne
    exact hwne rfl
  intro x hx
  have hmem : ∀ (a b : ℤ), (2 : ℤ) • (a • w + b • c w) = 0 := by
    intro a b
    rw [smul_add, smul_comm, hw2, smul_zero, smul_comm, hcw2, smul_zero, add_zero]
  have hne1 : (⟨0, by simp⟩ : {x : P // (2 : ℤ) • x = 0}) ≠ ⟨w, hw2⟩ := by
    intro hh
    exact hwnz (congrArg (fun t : {x : P // (2 : ℤ) • x = 0} => (t : P)) hh).symm
  have hne2 : (⟨0, by simp⟩ : {x : P // (2 : ℤ) • x = 0}) ≠ ⟨c w, hcw2⟩ := by
    intro hh
    exact hcwnz (congrArg (fun t : {x : P // (2 : ℤ) • x = 0} => (t : P)) hh).symm
  have hne3 : (⟨0, by simp⟩ : {x : P // (2 : ℤ) • x = 0}) ≠ ⟨w + c w, by
      have := hmem 1 1; simpa using this⟩ := by
    intro hh
    exact hsumnz (congrArg (fun t : {x : P // (2 : ℤ) • x = 0} => (t : P)) hh).symm
  have hne4 : (⟨w, hw2⟩ : {x : P // (2 : ℤ) • x = 0}) ≠ ⟨c w, hcw2⟩ := by
    intro hh
    exact hwne (congrArg (fun t : {x : P // (2 : ℤ) • x = 0} => (t : P)) hh).symm
  have hne5 : (⟨w, hw2⟩ : {x : P // (2 : ℤ) • x = 0}) ≠ ⟨w + c w, by
      have := hmem 1 1; simpa using this⟩ := by
    intro hh
    have := congrArg (fun t : {x : P // (2 : ℤ) • x = 0} => (t : P)) hh
    simp only at this
    exact hcwnz (by
      have e : w + c w - w = c w := by abel
      rw [← e, ← this, sub_self])
  have hne6 : (⟨c w, hcw2⟩ : {x : P // (2 : ℤ) • x = 0}) ≠ ⟨w + c w, by
      have := hmem 1 1; simpa using this⟩ := by
    intro hh
    have := congrArg (fun t : {x : P // (2 : ℤ) • x = 0} => (t : P)) hh
    simp only at this
    exact hwnz (by
      have e : w + c w - c w = w := by abel
      rw [← e, ← this, sub_self])
  rcases eq_or_of_card_eq_four hcard2 hne1 hne2 hne3 hne4 hne5 hne6 ⟨x, hx⟩ with
    h | h | h | h
  · exact ⟨0, 0, by
      have : x = 0 := congrArg (fun t : {x : P // (2 : ℤ) • x = 0} => (t : P)) h
      rw [this]; simp⟩
  · exact ⟨1, 0, by
      have : x = w := congrArg (fun t : {x : P // (2 : ℤ) • x = 0} => (t : P)) h
      rw [this]; simp⟩
  · exact ⟨0, 1, by
      have : x = c w := congrArg (fun t : {x : P // (2 : ℤ) • x = 0} => (t : P)) h
      rw [this]; simp⟩
  · exact ⟨1, 1, by
      have : x = w + c w := congrArg (fun t : {x : P // (2 : ℤ) • x = 0} => (t : P)) h
      rw [this]; simp⟩

/-- The trivial frame at level `1`. -/
theorem frame_one (ε : Bool) (c : P →+ P) : IsFrame ε c 1 ((0 : P), (0 : P)) := by
  refine ⟨⟨by simp, by simp, ?_, ?_⟩, by simp, ?_⟩
  · intro y hy
    refine ⟨0, 0, ?_⟩
    simp only [smul_zero, add_zero]
    simpa using hy.symm
  · intro a b _
    exact ⟨by simp, by simp⟩
  · show c 0 = (if ε then (0 : P) else 0) - 0
    cases ε <;> simp

/-- Scaling by congruent coefficients agrees on `n`-torsion. -/
theorem zsmul_eq_of_dvd_sub {n : ℕ} {x : P} (hx : ((n : ℕ) : ℤ) • x = 0) {A α : ℤ}
    (h : ((n : ℕ) : ℤ) ∣ A - α) : A • x = α • x := by
  obtain ⟨z, hz⟩ := h
  have hA : A = α + (n : ℤ) * z := by linarith [hz]
  rw [hA, add_smul, mul_comm, mul_smul, hx, smul_zero, add_zero]

/-- **THE `ε = true` FRAME AT A `2`-POWER LEVEL**: lift an unfixed `w ∈ P[2]` to `v` with
`2^{k−1} v = w`.  Then `v` and `c v` GENERATE `P[2^k]` — modulo `2` they are `w` and `c w`,
which span `P[2]`, and the error can be halved again and again until it dies — and
`(v + c v, v)` is a frame with `c q = p − q`. -/
theorem exists_frame_two_pow (hdiv : ∀ m : ℕ, m ≠ 0 → ∀ y : P, ∃ x : P, (m : ℤ) • x = y)
    {c : P →+ P} (hc : ∀ x, c (c x) = x)
    (hcard : ∀ n : ℕ, n ≠ 0 → Nat.card {x : P // (n : ℤ) • x = 0} = n ^ 2)
    (hcard2 : Nat.card {x : P // (2 : ℤ) • x = 0} = 4)
    (hfix2 : Nat.card {x : P // (2 : ℤ) • x = 0 ∧ c x = x} = 2) (k : ℕ) :
    ∃ pq : P × P, IsFrame true c (2 ^ k) pq := by
  obtain ⟨w, hw2, hwne⟩ := exists_unfixed_two_torsion hcard2 hfix2
  rcases k with _ | k
  · exact ⟨((0 : P), (0 : P)), by simpa using frame_one true c⟩
  · have hK0 : (2 ^ (k + 1) : ℕ) ≠ 0 := by positivity
    obtain ⟨v, hv0⟩ := hdiv (2 ^ k) (by positivity) w
    have hv : ((2 ^ k : ℕ) : ℤ) • v = w := hv0
    have hcv : ((2 ^ k : ℕ) : ℤ) • (c v) = c w := by rw [← map_zsmul, hv]
    have hpow : ((2 ^ (k + 1) : ℕ) : ℤ) = (2 : ℤ) * ((2 ^ k : ℕ) : ℤ) := by push_cast; ring
    have hvK : ((2 ^ (k + 1) : ℕ) : ℤ) • v = 0 := by
      rw [hpow, mul_smul, hv, hw2]
    have hcvK : ((2 ^ (k + 1) : ℕ) : ℤ) • (c v) = 0 := by
      rw [← map_zsmul, hvK, map_zero]
    -- halving an element killed by `2^k` inside `P[2^{k+1}]`
    have hhalf : ∀ z : P, ((2 ^ k : ℕ) : ℤ) • z = 0 →
        ∃ y : P, ((2 ^ (k + 1) : ℕ) : ℤ) • y = 0 ∧ (2 : ℤ) • y = z := by
      intro z hz
      obtain ⟨y, hy0⟩ := hdiv 2 two_ne_zero z
      have hy : (2 : ℤ) • y = z := by have h := hy0; push_cast at h; exact h
      refine ⟨y, ?_, hy⟩
      rw [hpow, mul_comm, mul_smul, hy, hz]
    -- one halving step of the approximation
    have hstep : ∀ x : P, ((2 ^ (k + 1) : ℕ) : ℤ) • x = 0 →
        ∃ (a b : ℤ) (y : P), ((2 ^ (k + 1) : ℕ) : ℤ) • y = 0 ∧
          x = a • v + b • (c v) + (2 : ℤ) • y := by
      intro x hx
      have hx2 : (2 : ℤ) • (((2 ^ k : ℕ) : ℤ) • x) = 0 := by rw [← mul_smul, ← hpow]; exact hx
      obtain ⟨a, b, hab⟩ := span_two_torsion hc hcard2 hw2 hwne _ hx2
      have hz : ((2 ^ k : ℕ) : ℤ) • (x - (a • v + b • (c v))) = 0 := by
        rw [smul_sub, smul_add, smul_comm _ a, hv, smul_comm _ b, hcv, hab, sub_self]
      obtain ⟨y, hyK, hy2⟩ := hhalf _ hz
      refine ⟨a, b, y, hyK, ?_⟩
      rw [hy2]
      abel
    -- iterate the step: the error is divisible by `2^i` for every `i`
    have hiter : ∀ i : ℕ, ∀ x : P, ((2 ^ (k + 1) : ℕ) : ℤ) • x = 0 →
        ∃ (a b : ℤ) (y : P), ((2 ^ (k + 1) : ℕ) : ℤ) • y = 0 ∧
          x = a • v + b • (c v) + ((2 ^ i : ℕ) : ℤ) • y := by
      intro i
      induction i with
      | zero => intro x hx; exact ⟨0, 0, x, hx, by simp⟩
      | succ i ih =>
        intro x hx
        obtain ⟨a, b, y, hyK, hxy⟩ := ih x hx
        obtain ⟨a', b', y', hy'K, hyy⟩ := hstep y hyK
        refine ⟨a + ((2 ^ i : ℕ) : ℤ) * a', b + ((2 ^ i : ℕ) : ℤ) * b', y', hy'K, ?_⟩
        rw [hxy, hyy, show ((2 ^ (i + 1) : ℕ) : ℤ) = ((2 ^ i : ℕ) : ℤ) * 2 by push_cast; ring]
        module
    have hspan : ∀ x : P, ((2 ^ (k + 1) : ℕ) : ℤ) • x = 0 →
        ∃ a b : ℤ, a • v + b • (c v) = x := by
      intro x hx
      obtain ⟨a, b, y, hyK, hxy⟩ := hiter (k + 1) x hx
      exact ⟨a, b, by rw [hxy, hyK, add_zero]⟩
    refine ⟨(v + c v, v), ?_, ?_, ?_⟩
    · refine isTorsionBasis_of_span hK0 (hcard _ hK0) ?_ hvK ?_
      · show ((2 ^ (k + 1) : ℕ) : ℤ) • (v + c v) = 0
        rw [smul_add, hvK, hcvK, add_zero]
      · intro y hy
        obtain ⟨a, b, hab⟩ := hspan y hy
        refine ⟨b, a - b, ?_⟩
        show b • (v + c v) + (a - b) • v = y
        rw [← hab]
        module
    · show c (v + c v) = v + c v
      rw [map_add, hc]
      abel
    · show c v = (if true then v + c v else 0) - v
      rw [if_pos rfl]
      abel

/-! ### Frames at coprime levels combine -/

/-- **FRAMES AT COPRIME LEVELS ADD**: `(p₁ + p₂, q₁ + q₂)` is a frame at level `ab`.  The
two intertwining equations are additive; spanning is Bézout plus the explicit Chinese
remainder coefficients `A = αs + γt`, `s = vb`, `t = ua`, `s + t = 1`. -/
theorem frame_mul_coprime {ε : Bool} {c : P →+ P}
    (hcard : ∀ n : ℕ, n ≠ 0 → Nat.card {x : P // (n : ℤ) • x = 0} = n ^ 2)
    {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : Nat.Coprime a b)
    {p₁ q₁ p₂ q₂ : P} (h₁ : IsFrame ε c a (p₁, q₁)) (h₂ : IsFrame ε c b (p₂, q₂)) :
    IsFrame ε c (a * b) (p₁ + p₂, q₁ + q₂) := by
  obtain ⟨⟨hp₁, hq₁, hspan₁, -⟩, hfix₁, htw₁⟩ := h₁
  obtain ⟨⟨hp₂, hq₂, hspan₂, -⟩, hfix₂, htw₂⟩ := h₂
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * (a : ℤ) + v * (b : ℤ) = 1 :=
    Nat.isCoprime_iff_coprime.mpr hab
  have hab0 : a * b ≠ 0 := Nat.mul_ne_zero ha hb
  have hcast : ((a * b : ℕ) : ℤ) = ((a : ℕ) : ℤ) * ((b : ℕ) : ℤ) := by push_cast; ring
  have hkill₁ : ∀ x : P, ((a : ℕ) : ℤ) • x = 0 → ((a * b : ℕ) : ℤ) • x = 0 := by
    intro x hx; rw [hcast, mul_comm, mul_smul, hx, smul_zero]
  have hkill₂ : ∀ x : P, ((b : ℕ) : ℤ) • x = 0 → ((a * b : ℕ) : ℤ) • x = 0 := by
    intro x hx; rw [hcast, mul_smul, hx, smul_zero]
  refine ⟨?_, ?_, ?_⟩
  · refine isTorsionBasis_of_span hab0 (hcard _ hab0) ?_ ?_ ?_
    · show ((a * b : ℕ) : ℤ) • (p₁ + p₂) = 0
      rw [smul_add, hkill₁ _ hp₁, hkill₂ _ hp₂, add_zero]
    · show ((a * b : ℕ) : ℤ) • (q₁ + q₂) = 0
      rw [smul_add, hkill₁ _ hq₁, hkill₂ _ hq₂, add_zero]
    · intro y hy
      have hsy : ((a : ℕ) : ℤ) • ((v * (b : ℤ)) • y) = 0 := by
        rw [smul_smul,
          show ((a : ℕ) : ℤ) * (v * (b : ℤ)) = v * ((a * b : ℕ) : ℤ) by rw [hcast]; ring,
          mul_smul, hy, smul_zero]
      have hty : ((b : ℕ) : ℤ) • ((u * (a : ℤ)) • y) = 0 := by
        rw [smul_smul,
          show ((b : ℕ) : ℤ) * (u * (a : ℤ)) = u * ((a * b : ℕ) : ℤ) by rw [hcast]; ring,
          mul_smul, hy, smul_zero]
      obtain ⟨α, β, hαβ⟩ := hspan₁ _ hsy
      obtain ⟨γ, δ, hγδ⟩ := hspan₂ _ hty
      have hs1 : ((a : ℕ) : ℤ) ∣ (v * (b : ℤ) - 1) := ⟨-u, by linear_combination huv⟩
      have hat : ((a : ℕ) : ℤ) ∣ (u * (a : ℤ)) := ⟨u, by ring⟩
      have ht1 : ((b : ℕ) : ℤ) ∣ (u * (a : ℤ) - 1) := ⟨-v, by linear_combination huv⟩
      have hbs : ((b : ℕ) : ℤ) ∣ (v * (b : ℤ)) := ⟨v, by ring⟩
      obtain ⟨z₁, hz₁⟩ := hs1
      obtain ⟨z₂, hz₂⟩ := hat
      obtain ⟨z₃, hz₃⟩ := ht1
      obtain ⟨z₄, hz₄⟩ := hbs
      refine ⟨α * (v * (b : ℤ)) + γ * (u * (a : ℤ)),
        β * (v * (b : ℤ)) + δ * (u * (a : ℤ)), ?_⟩
      have hA₁ : (α * (v * (b : ℤ)) + γ * (u * (a : ℤ))) • p₁ = α • p₁ :=
        zsmul_eq_of_dvd_sub hp₁ ⟨α * z₁ + γ * z₂, by linear_combination α * hz₁ + γ * hz₂⟩
      have hA₂ : (α * (v * (b : ℤ)) + γ * (u * (a : ℤ))) • p₂ = γ • p₂ :=
        zsmul_eq_of_dvd_sub hp₂ ⟨α * z₄ + γ * z₃, by linear_combination α * hz₄ + γ * hz₃⟩
      have hB₁ : (β * (v * (b : ℤ)) + δ * (u * (a : ℤ))) • q₁ = β • q₁ :=
        zsmul_eq_of_dvd_sub hq₁ ⟨β * z₁ + δ * z₂, by linear_combination β * hz₁ + δ * hz₂⟩
      have hB₂ : (β * (v * (b : ℤ)) + δ * (u * (a : ℤ))) • q₂ = δ • q₂ :=
        zsmul_eq_of_dvd_sub hq₂ ⟨β * z₄ + δ * z₃, by linear_combination β * hz₄ + δ * hz₃⟩
      show (α * (v * (b : ℤ)) + γ * (u * (a : ℤ))) • (p₁ + p₂)
        + (β * (v * (b : ℤ)) + δ * (u * (a : ℤ))) • (q₁ + q₂) = y
      rw [smul_add, smul_add, hA₁, hA₂, hB₁, hB₂]
      have hy' : (v * (b : ℤ)) • y + (u * (a : ℤ)) • y = y := by
        rw [← add_smul, show (v * (b : ℤ)) + (u * (a : ℤ)) = 1 by linear_combination huv, one_smul]
      have e : α • p₁ + γ • p₂ + (β • q₁ + δ • q₂)
          = (α • p₁ + β • q₁) + (γ • p₂ + δ • q₂) := by abel
      rw [e]
      show (α • (p₁, q₁).1 + β • (p₁, q₁).2) + (γ • (p₂, q₂).1 + δ • (p₂, q₂).2) = y
      rw [hαβ, hγδ]
      exact hy'
  · show c (p₁ + p₂) = p₁ + p₂
    rw [map_add, hfix₁, hfix₂]
  · show c (q₁ + q₂) = (if ε then p₁ + p₂ else 0) - (q₁ + q₂)
    rw [map_add]
    have h1 : c q₁ = (if ε then p₁ else 0) - q₁ := htw₁
    have h2 : c q₂ = (if ε then p₂ else 0) - q₂ := htw₂
    rw [h1, h2]
    cases ε <;> simp only [if_true, if_false, Bool.false_eq_true] <;> abel

/-- `−x = x` on `2`-torsion. -/
theorem neg_eq_self_of_two_smul {x : P} (h : (2 : ℤ) • x = 0) : -x = x := by
  have hs : x + x = 0 := by rw [← two_smul ℤ x]; exact h
  exact (add_eq_zero_iff_eq_neg.mp hs).symm

/-- **THE `ε = true` FRAME AT EVERY LEVEL**: the odd part and the `2`-part are built
separately and combined, the odd part out of generators of the two eigen-subgroups (whose
torsion counts are `n` because they are divisible, which is where `hfix2` is used a second
time), and the `2`-part out of a single lifted unfixed `2`-torsion element. -/
theorem exists_frame_true (hdiv : ∀ m : ℕ, m ≠ 0 → ∀ y : P, ∃ x : P, (m : ℤ) • x = y)
    (hcard : ∀ n : ℕ, n ≠ 0 → Nat.card {x : P // (n : ℤ) • x = 0} = n ^ 2)
    {c : P →+ P} (hc : ∀ x, c (c x) = x)
    (hne_id : ∀ n : ℕ, 3 ≤ n → ∃ x : P, (n : ℤ) • x = 0 ∧ c x ≠ x)
    (hne_neg : ∀ n : ℕ, 3 ≤ n → ∃ x : P, (n : ℤ) • x = 0 ∧ c x ≠ -x)
    (hfix2 : Nat.card {x : P // (2 : ℤ) • x = 0 ∧ c x = x} = 2)
    (n : ℕ) (hn : n ≠ 0) :
    ∃ pq : P × P, IsFrame true c n pq := by
  classical
  have hcard2 : Nat.card {x : P // (2 : ℤ) • x = 0} = 4 := by
    have h := hcard 2 two_ne_zero
    refine Eq.trans (Nat.card_congr (Equiv.subtypeEquivRight (p := fun x : P => (2 : ℤ) • x = 0)
      (q := fun x : P => ((2 : ℕ) : ℤ) • x = 0) (fun x => by norm_num))) ?_
    rw [h]
    norm_num
  have himg := exists_sub_eq_of_card_fix_two hc hcard2 hfix2
  have hdivF : IsDivisible (fixSub c) := isDivisible_fixSub hdiv hc himg
  have hdivG : IsDivisible (fixSub (-c)) := by
    refine isDivisible_fixSub hdiv (involutive_neg hc) ?_
    intro u hu2 hufix
    have hcu : c u = u := by
      have h1 : -(c u) = u := hufix
      have h2 : c u = -u := neg_eq_iff_eq_neg.mp h1
      rw [h2, neg_eq_self_of_two_smul hu2]
    obtain ⟨t, ht2, htu⟩ := himg u hu2 hcu
    refine ⟨t, ht2, ?_⟩
    show -(c t) - t = u
    have hsum : t + t = 0 := by rw [← two_smul ℤ t]; exact ht2
    have e : -(c t) - t = -(c t - t) := by
      have e1 : (-(c t) - t) - (-(c t - t)) = -(t + t) := by abel
      have e0 : (-(c t) - t) - (-(c t - t)) = 0 := by rw [e1, hsum, neg_zero]
      exact sub_eq_zero.mp e0
    rw [e, htu]
    exact neg_eq_self_of_two_smul hu2
  -- the two eigen-subgroups split the odd levels
  have hmulFG : ∀ m : ℕ, m ≠ 0 → Odd m →
      Nat.card (tors (fixSub c) m) * Nat.card (tors (fixSub (-c)) m) = m ^ 2 := by
    intro m hm0 hodd
    obtain ⟨kk, hkk⟩ := hodd
    obtain ⟨j, hj⟩ : ∃ j : ℤ, (2 * j - 1 : ℤ) = (m : ℕ) :=
      ⟨(kk : ℤ) + 1, by rw [hkk]; push_cast; ring⟩
    rw [← hcard m hm0]
    refine (Nat.card_prod _ _).symm.trans (Nat.card_congr (Equiv.ofBijective
      (fun x : tors (fixSub c) m × tors (fixSub (-c)) m =>
        (⟨(x.1 : P) + (x.2 : P), by rw [smul_add, x.1.2.2, x.2.2.2, add_zero]⟩ :
          {z : P // ((m : ℕ) : ℤ) • z = 0})) ⟨?_, ?_⟩))
    · rintro ⟨⟨A, hAF, hA⟩, ⟨B, hBG, hB⟩⟩ ⟨⟨A', hA'F, hA'⟩, ⟨B', hB'G, hB'⟩⟩ hh
      have h : A + B = A' + B' := congrArg Subtype.val hh
      have hd : A - A' = B' - B := by
        have e : A - A' - (B' - B) = (A + B) - (A' + B') := by abel
        have e0 : A - A' - (B' - B) = 0 := by rw [e, h, sub_self]
        exact sub_eq_zero.mp e0
      have hfixd : c (A - A') = A - A' := by
        rw [map_sub, show c A = A from hAF, show c A' = A' from hA'F]
      have hnegd : c (A - A') = -(A - A') := by
        rw [hd, map_sub, show c B' = -B' from mem_fixSub_neg.mp hB'G,
          show c B = -B from mem_fixSub_neg.mp hBG]
        abel
      have hmd : ((m : ℕ) : ℤ) • (A - A') = 0 := by rw [smul_sub, hA, hA', sub_self]
      have hzero := eq_zero_of_fix_and_neg ⟨kk, hkk⟩ hfixd hnegd hmd
      have hAA : A = A' := sub_eq_zero.mp hzero
      subst hAA
      have hBB : B = B' := by
        have := h
        rwa [add_right_inj] at this
      subst hBB
      rfl
    · rintro ⟨y, hy⟩
      obtain ⟨A, B, hAfix, hBneg, hAm, hBm, hsum⟩ := exists_split_odd hc hj y hy
      exact ⟨(⟨A, hAfix, hAm⟩, ⟨B, mem_fixSub_neg.mpr hBneg, hBm⟩), Subtype.ext hsum⟩
  -- the `p`-torsion counts of the two eigen-subgroups
  have hF2 : Nat.card (tors (fixSub c) 2) = 2 := by
    refine Eq.trans (Nat.card_congr (Equiv.ofBijective
      (fun x : tors (fixSub c) 2 => (⟨(x : P), by
        have h := x.2.2; push_cast at h; exact h, x.2.1⟩ :
        {z : P // (2 : ℤ) • z = 0 ∧ c z = z})) ⟨?_, ?_⟩)) hfix2
    · intro x y hxy
      exact Subtype.ext (congrArg (fun z : {z : P // (2 : ℤ) • z = 0 ∧ c z = z} => (z : P)) hxy)
    · rintro ⟨z, hz2, hzf⟩
      exact ⟨⟨z, hzf, by push_cast; exact hz2⟩, rfl⟩
  have hG2 : Nat.card (tors (fixSub (-c)) 2) = 2 := by
    refine Eq.trans (Nat.card_congr (Equiv.ofBijective
      (fun x : tors (fixSub (-c)) 2 => (⟨(x : P), by
        have h := x.2.2; push_cast at h; exact h, by
        have h := x.2.2; push_cast at h
        have hneg : c (x : P) = -(x : P) := mem_fixSub_neg.mp x.2.1
        rw [hneg, neg_eq_self_of_two_smul h]⟩ :
        {z : P // (2 : ℤ) • z = 0 ∧ c z = z})) ⟨?_, ?_⟩)) hfix2
    · intro x y hxy
      exact Subtype.ext (congrArg (fun z : {z : P // (2 : ℤ) • z = 0 ∧ c z = z} => (z : P)) hxy)
    · rintro ⟨z, hz2, hzf⟩
      refine ⟨⟨z, mem_fixSub_neg.mpr ?_, by push_cast; exact hz2⟩, rfl⟩
      rw [hzf]
      exact (neg_eq_self_of_two_smul hz2).symm
  have hprimeF : ∀ p : ℕ, p.Prime → Nat.card (tors (fixSub c) p) = p := by
    intro p hp
    rcases hp.eq_two_or_odd' with rfl | hodd
    · exact hF2
    · exact card_tors_prime_eq_of_split hcard hne_id hne_neg hdivF hdivG (fun x hx => hx)
        (fun x hx => mem_fixSub_neg.mp hx) hp (hmulFG p hp.ne_zero hodd)
  have hprimeG : ∀ p : ℕ, p.Prime → Nat.card (tors (fixSub (-c)) p) = p := by
    intro p hp
    rcases hp.eq_two_or_odd' with rfl | hodd
    · exact hG2
    · have hmul := hmulFG p hp.ne_zero hodd
      rw [hprimeF p hp] at hmul
      have hpp : p * Nat.card (tors (fixSub (-c)) p) = p * p := by rw [hmul]; ring
      exact Nat.eq_of_mul_eq_mul_left hp.pos hpp
  have hcardF := card_tors_eq hdivF hprimeF
  have hcardG := card_tors_eq hdivG hprimeG
  -- split `n` into its `2`-part and its odd part
  obtain ⟨k, m, hmodd, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [Nat.mul_zero] at hnm
    exact hn hnm
  have hnd : ¬ (2 ∣ m) := by
    intro hdvd
    rcases hmodd with ⟨r, hr⟩
    omega
  have hcop : Nat.Coprime (2 ^ k) m :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hnd)
  obtain ⟨⟨p₂, q₂⟩, h₂⟩ := exists_frame_two_pow hdiv hc hcard hcard2 hfix2 k
  obtain ⟨⟨pm, qm⟩, hmfr⟩ := exists_frame_odd hc hcard hcardF hcardG hm0 hmodd
  rw [hnm]
  exact ⟨_, frame_mul_coprime hcard (by positivity) hm0 hcop h₂ hmfr⟩

/-! ### The frame, both cases -/

/-- **THE ADAPTED FRAME AT EVERY LEVEL**, for a divisible group whose `n`-torsion has `n²`
points and an involution which is neither `±1` on any `n`-torsion with `n ≥ 3`: the value of
`ε` is read off the fixed `2`-torsion, `4` points meaning that `c` fixes `P[2]` and `2` that
it does not. -/
theorem exists_frame (hdiv : ∀ m : ℕ, m ≠ 0 → ∀ y : P, ∃ x : P, (m : ℤ) • x = y)
    (hcard : ∀ n : ℕ, n ≠ 0 → Nat.card {x : P // (n : ℤ) • x = 0} = n ^ 2)
    (ε : Bool) {c : P →+ P} (hc : ∀ x, c (c x) = x)
    (hne_id : ∀ n : ℕ, 3 ≤ n → ∃ x : P, (n : ℤ) • x = 0 ∧ c x ≠ x)
    (hne_neg : ∀ n : ℕ, 3 ≤ n → ∃ x : P, (n : ℤ) • x = 0 ∧ c x ≠ -x)
    (hfix2 : Nat.card {x : P // (2 : ℤ) • x = 0 ∧ c x = x} = if ε then 2 else 4)
    (n : ℕ) (hn : n ≠ 0) :
    ∃ pq : P × P, IsFrame ε c n pq := by
  classical
  have hcard2 : Nat.card {x : P // (2 : ℤ) • x = 0} = 4 := by
    have h := hcard 2 two_ne_zero
    refine Eq.trans (Nat.card_congr (Equiv.subtypeEquivRight (p := fun x : P => (2 : ℤ) • x = 0)
      (q := fun x : P => ((2 : ℕ) : ℤ) • x = 0) (fun x => by norm_num))) ?_
    rw [h]
    norm_num
  cases ε with
  | true => exact exists_frame_true hdiv hcard hc hne_id hne_neg (by simpa using hfix2) n hn
  | false =>
    have hfix4 : Nat.card {x : P // (2 : ℤ) • x = 0 ∧ c x = x} = 4 := by simpa using hfix2
    haveI : Finite {x : P // (2 : ℤ) • x = 0} :=
      Nat.finite_of_card_ne_zero (by rw [hcard2]; omega)
    have hbij : Function.Bijective
        (fun x : {x : P // (2 : ℤ) • x = 0 ∧ c x = x} =>
          (⟨(x : P), x.2.1⟩ : {x : P // (2 : ℤ) • x = 0})) := by
      refine Nat.bijective_iff_injective_and_card _ |>.mpr ⟨?_, ?_⟩
      · intro x y hxy
        exact Subtype.ext (congrArg (fun z : {x : P // (2 : ℤ) • x = 0} => (z : P)) hxy)
      · rw [hfix4, hcard2]
    have hfix : ∀ x : P, (2 : ℤ) • x = 0 → c x = x := by
      intro x hx
      obtain ⟨y, hy⟩ := hbij.2 ⟨x, hx⟩
      have hval : (y : P) = x := congrArg Subtype.val hy
      rw [← hval]
      exact y.2.2
    exact exists_frame_false hdiv hcard c hc hne_id hne_neg hfix n hn

/-! ### The specialisation to `(ℚ/ℤ)²`

`ℚ/ℤ` is divisible with `n`-torsion `ℤ/n`, so `(ℚ/ℤ)²` satisfies both hypotheses of
`exists_frame`.  (`MoretBailly.lean`'s `DivisibleTorsion.finite_ratQuot_torsion` is the
finiteness-only shadow of `card_ratQuot_torsion` below, which computes the count.) -/

/-- Every `n`-torsion element of `ℚ/ℤ` is `a/n` for an integer `a`. -/
theorem exists_intDiv_ratQuot {n : ℕ} (hn : n ≠ 0)
    {x : ℚ ⧸ (1 : Submodule ℤ ℚ)} (hx : (n : ℤ) • x = 0) :
    ∃ a : ℤ, x = Submodule.Quotient.mk ((a : ℚ) / (n : ℚ)) := by
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective (1 : Submodule ℤ ℚ) x
  have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h0 : (Submodule.Quotient.mk ((n : ℚ) * r) : ℚ ⧸ (1 : Submodule ℤ ℚ)) = 0 := by
    rw [show ((n : ℚ) * r) = ((n : ℤ) • r) by rw [zsmul_eq_mul]; push_cast; ring]
    exact hx
  obtain ⟨a, ha⟩ := Submodule.mem_one.mp (Submodule.Quotient.mk_eq_zero _ |>.mp h0)
  refine ⟨a, ?_⟩
  have ha' : (a : ℚ) = (n : ℚ) * r := by rw [← ha]; simp
  rw [ha']
  congr 1
  field_simp

/-- **THE `n`-TORSION OF `ℚ/ℤ` HAS `n` POINTS**: `a ↦ a/n` is a bijection from `ℤ/n`. -/
theorem card_ratQuot_torsion {n : ℕ} (hn : n ≠ 0) :
    Nat.card {x : ℚ ⧸ (1 : Submodule ℤ ℚ) // (n : ℤ) • x = 0} = n := by
  haveI : NeZero n := ⟨hn⟩
  have hnq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hmem : ∀ a : ℤ, (n : ℤ) •
      (Submodule.Quotient.mk ((a : ℚ) / (n : ℚ)) : ℚ ⧸ (1 : Submodule ℤ ℚ)) = 0 := by
    intro a
    show (Submodule.Quotient.mk ((n : ℤ) • ((a : ℚ) / (n : ℚ))) : ℚ ⧸ (1 : Submodule ℤ ℚ)) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    refine Submodule.mem_one.mpr ⟨a, ?_⟩
    have halg : (algebraMap ℤ ℚ) a = (a : ℚ) := by simp
    rw [halg, zsmul_eq_mul]
    push_cast
    field_simp
  have hbij : Function.Bijective (fun a : ZMod n =>
      (⟨Submodule.Quotient.mk (((a.val : ℤ) : ℚ) / (n : ℚ)), hmem (a.val : ℤ)⟩ :
        {x : ℚ ⧸ (1 : Submodule ℤ ℚ) // (n : ℤ) • x = 0})) := by
    constructor
    · intro a b hab
      have h : (Submodule.Quotient.mk (((a.val : ℤ) : ℚ) / (n : ℚ)) : ℚ ⧸ (1 : Submodule ℤ ℚ))
          = Submodule.Quotient.mk (((b.val : ℤ) : ℚ) / (n : ℚ)) := congrArg Subtype.val hab
      rw [Submodule.Quotient.eq] at h
      obtain ⟨e, he⟩ := Submodule.mem_one.mp h
      have halg : (algebraMap ℤ ℚ) e = (e : ℚ) := by simp
      rw [halg] at he
      have hz : ((a.val : ℤ) : ℚ) - ((b.val : ℤ) : ℚ) = (n : ℚ) * (e : ℚ) := by
        field_simp at he
        linarith [he]
      have hdvd : ((n : ℕ) : ℤ) ∣ ((a.val : ℤ) - (b.val : ℤ)) := ⟨e, by exact_mod_cast hz⟩
      have hzero := (ZMod.intCast_zmod_eq_zero_iff_dvd ((a.val : ℤ) - (b.val : ℤ)) n).mpr hdvd
      push_cast [ZMod.natCast_val, ZMod.cast_id] at hzero
      exact sub_eq_zero.mp hzero
    · rintro ⟨x, hx⟩
      obtain ⟨a, rfl⟩ := exists_intDiv_ratQuot hn hx
      refine ⟨(a : ZMod n), Subtype.ext ?_⟩
      have hdvd : (n : ℤ) ∣ ((((a : ZMod n).val : ℤ)) - a) := by
        have h := (ZMod.intCast_zmod_eq_zero_iff_dvd ((((a : ZMod n).val : ℤ)) - a) n).mp (by
          push_cast [ZMod.natCast_val, ZMod.intCast_cast, ZMod.cast_id]
          ring)
        exact h
      obtain ⟨e, he⟩ := hdvd
      show (Submodule.Quotient.mk ((((a : ZMod n).val : ℤ) : ℚ) / (n : ℚ)) :
        ℚ ⧸ (1 : Submodule ℤ ℚ)) = Submodule.Quotient.mk ((a : ℚ) / (n : ℚ))
      rw [Submodule.Quotient.eq]
      refine Submodule.mem_one.mpr ⟨e, ?_⟩
      have hz : ((((a : ZMod n).val : ℤ) : ℚ)) - (a : ℚ) = ((n : ℚ)) * (e : ℚ) := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) he
      show ((e : ℤ) : ℚ) = ((((a : ZMod n).val : ℤ) : ℚ) / (n : ℚ)) - ((a : ℚ) / (n : ℚ))
      field_simp
      linarith [hz]
  have hcc := Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [← hcc]
  simp [Nat.card_eq_fintype_card]

/-- The `n`-torsion of `(ℚ/ℤ)²` has `n²` points. -/
theorem card_ratQuotSq_torsion {n : ℕ} (hn : n ≠ 0) :
    Nat.card {x : Fin 2 → (ℚ ⧸ (1 : Submodule ℤ ℚ)) // (n : ℤ) • x = 0} = n ^ 2 := by
  have h1 := card_ratQuot_torsion hn
  have hbij : Function.Bijective
      (fun x : {x : Fin 2 → (ℚ ⧸ (1 : Submodule ℤ ℚ)) // (n : ℤ) • x = 0} =>
        ((⟨x.1 0, by simpa using congrFun x.2 0⟩ :
            {y : ℚ ⧸ (1 : Submodule ℤ ℚ) // (n : ℤ) • y = 0}),
         (⟨x.1 1, by simpa using congrFun x.2 1⟩ :
            {y : ℚ ⧸ (1 : Submodule ℤ ℚ) // (n : ℤ) • y = 0}))) := by
    constructor
    · intro x y hxy
      have h0 : x.1 0 = y.1 0 := congrArg Subtype.val (congrArg Prod.fst hxy)
      have hh1 : x.1 1 = y.1 1 := congrArg Subtype.val (congrArg Prod.snd hxy)
      refine Subtype.ext (funext fun i => ?_)
      fin_cases i
      · exact h0
      · exact hh1
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      refine ⟨⟨![a, b], ?_⟩, ?_⟩
      · funext i
        fin_cases i
        · simpa using ha
        · simpa using hb
      · rfl
  have hcc := Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [hcc, Nat.card_prod, h1]
  ring

/-- `(ℚ/ℤ)²` is divisible. -/
theorem ratQuotSq_divisible (m : ℕ) (hm : m ≠ 0) (y : Fin 2 → (ℚ ⧸ (1 : Submodule ℤ ℚ))) :
    ∃ x : Fin 2 → (ℚ ⧸ (1 : Submodule ℤ ℚ)), (m : ℤ) • x = y := by
  classical
  have hone : ∀ z : ℚ ⧸ (1 : Submodule ℤ ℚ), ∃ w : ℚ ⧸ (1 : Submodule ℤ ℚ), (m : ℤ) • w = z := by
    intro z
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective (1 : Submodule ℤ ℚ) z
    have hmq : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    refine ⟨Submodule.Quotient.mk (r / (m : ℚ)), ?_⟩
    show (Submodule.Quotient.mk ((m : ℤ) • (r / (m : ℚ))) : ℚ ⧸ (1 : Submodule ℤ ℚ))
      = Submodule.Quotient.mk r
    congr 1
    rw [zsmul_eq_mul]
    push_cast
    field_simp
  choose w hw using hone
  exact ⟨fun i => w (y i), funext fun i => hw (y i)⟩

/-- **THE LEAF, FOR `(ℚ/ℤ)²`**: this is `MoretBailly.lean`'s `exists_adaptedFrame_level`,
modulo repackaging `IsFrame` as `IsAdaptedFrame`. -/
theorem exists_frame_ratQuotSq (ε : Bool)
    {c : (Fin 2 → (ℚ ⧸ (1 : Submodule ℤ ℚ))) →+ (Fin 2 → (ℚ ⧸ (1 : Submodule ℤ ℚ)))}
    (hc : ∀ x, c (c x) = x)
    (hne_id : ∀ n : ℕ, 3 ≤ n → ∃ x, (n : ℤ) • x = 0 ∧ c x ≠ x)
    (hne_neg : ∀ n : ℕ, 3 ≤ n → ∃ x, (n : ℤ) • x = 0 ∧ c x ≠ -x)
    (hfix2 : Nat.card {x : (Fin 2 → (ℚ ⧸ (1 : Submodule ℤ ℚ))) //
      (2 : ℤ) • x = 0 ∧ c x = x} = if ε then 2 else 4)
    (n : ℕ) (hn : n ≠ 0) :
    ∃ pq : (Fin 2 → (ℚ ⧸ (1 : Submodule ℤ ℚ))) × (Fin 2 → (ℚ ⧸ (1 : Submodule ℤ ℚ))),
      IsFrame ε c n pq :=
  exists_frame ratQuotSq_divisible (fun _ h => card_ratQuotSq_torsion h) ε hc hne_id hne_neg
    hfix2 n hn

end GaloisRepresentation.Modularity.InvolutionFrame
