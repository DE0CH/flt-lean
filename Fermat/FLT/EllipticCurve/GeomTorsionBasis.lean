/-
Copyright (c) 2026 Deyao Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Fermat.FLT.EllipticCurve.TorsionCharP

/-!
# A `Fin n × Fin n`-basis of the `n`-torsion forces `n` invertible

Three declarations HOISTED out of `Fermat/FLT/ModularCurve/X1.lean` on
2026-07-31, unchanged line for line, so that `X0.lean` — which `X1.lean`
imports, and which therefore cannot import it back — can use them.

`X0.lean`'s `natCast_ne_zero_of_geomBasis` is the fibre-level statement of
`natCast_ne_zero_of_geomBasis_point` below: `X0.lean` already proves
`exists_weierstrassModel_geomFibreAddEquiv_of_geomPoint`, which reads the
geometric fibre of an abelian scheme of relative dimension one as the point
group of an elliptic curve, so the ONLY thing it was missing was the
arithmetic proved here.  It was missing it because the arithmetic lived
DOWNSTREAM — see the `Missing machinery may be DOWNSTREAM` note in
`CLAUDE.md`.

Nothing here mentions a scheme; the whole file is `WeierstrassCurve` over a
field plus one abstract `AddCommGroup` transport lemma.  `X1.lean` keeps
using all three under their unchanged names, inherited through
`X0.lean`'s `public import` of this module.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine

namespace Fermat

/-- **A `ℤ`-multiple of an `n`-torsion element is a `ℕ`-multiple below `n`**
(PROVEN 2026-07-30) — Euclidean division of the coefficient by `n`, the
quotient part being killed by `n • z = 0`.  Bookkeeping for
`natCast_ne_zero_of_indep_point` below and for
`natCast_ne_zero_of_geomBasis_point` far below, both of whose one appeal to
the literature (`TorsionCharP.exists_zsmul_eq_of_charP`) returns a
`ℤ`-multiple while the basis property speaks of `Fin n`-coefficients. -/
theorem exists_lt_nsmul_eq_zsmul {G : Type*} [AddCommGroup G] {n : ℕ} (hn : n ≠ 0)
    {z : G} (hz : n • z = 0) (a : ℤ) : ∃ r : ℕ, r < n ∧ a • z = r • z := by
  have hnpos : (0 : ℤ) < (n : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  refine ⟨(a % (n : ℤ)).toNat, ?_, ?_⟩
  · have h1 : a % (n : ℤ) < (n : ℤ) := Int.emod_lt_of_pos a hnpos
    have h2 : (0 : ℤ) ≤ a % (n : ℤ) := Int.emod_nonneg a (by omega)
    omega
  · have hz' : ((n : ℤ)) • z = 0 := by rw [natCast_zsmul]; exact hz
    have hsplit : a = (n : ℤ) * (a / (n : ℤ)) + a % (n : ℤ) :=
      (Int.mul_ediv_add_emod a (n : ℤ)).symm
    have h2 : (0 : ℤ) ≤ a % (n : ℤ) := Int.emod_nonneg a (by omega)
    calc a • z = ((n : ℤ) * (a / (n : ℤ)) + a % (n : ℤ)) • z := by rw [← hsplit]
      _ = (a / (n : ℤ)) • ((n : ℤ) • z) + (a % (n : ℤ)) • z := by
          rw [add_zsmul, mul_comm, mul_zsmul]
      _ = (a % (n : ℤ)) • z := by rw [hz', smul_zero, zero_add]
      _ = ((a % (n : ℤ)).toNat : ℤ) • z := by rw [Int.toNat_of_nonneg h2]
      _ = (a % (n : ℤ)).toNat • z := natCast_zsmul _ _

/-- **A `Fin n × Fin n`-BASIS OF THE `n`-TORSION OF AN ELLIPTIC CURVE FORCES
`n` INVERTIBLE** (PROVEN 2026-07-30) — the arithmetic heart of the count
recorded in the FALSITY AUDIT of
`isOpenImmersion_equalizer_of_abelianFullLevelStructure` below, and the
single place where the `Γ₁` leaf recovers, from its full level structure,
the invertibility of `n` that the `Γ₀` leaf receives outright from a
`ℚ`-base.

## The statement

`y, z` are two `n`-torsion points of `E(K)` such that EVERY `n`-torsion
point has exactly one expression `a·y + b·z` with `(a, b) ∈ Fin n × Fin n`
— i.e. `E(K)[n] ≅ (ℤ/n)²`.  Then `n` is invertible in `K`.

## The proof

Suppose `(n : K) = 0`.  Then `p := ringChar K` is a prime dividing `n`
(`ringChar.spec`, and `CharP.char_is_prime_or_zero` with `p ≠ 0` because
`n ≠ 0`).  Write `n = p·m` with `1 ≤ m < n` and set `P := m·y`, `Q := m·z`;
both are `p`-torsion, since `p·(m·y) = n·y = 0`.

`Q ≠ 0`: were `m·z = 0`, the point `0` would have the two coordinate pairs
`(0, m)` and `(0, 0)`, and uniqueness would force `m ≡ 0 (mod n)` against
`0 < m < n`.

`TorsionCharP.exists_zsmul_eq_of_charP` — the geometric `p`-torsion in
characteristic `p` is CYCLIC, PROVEN 2026-07-25 from the inseparability of
`[p]` — then produces `k : ℤ` with `P = k·Q`.  Reducing `k·m` modulo `n`
(`exists_lt_nsmul_eq_zsmul`) gives `r < n` with `m·y = r·z`, so the point
`m·y` has the two coordinate pairs `(m, 0)` and `(0, r)`; uniqueness forces
`m ≡ 0 (mod n)`, the same contradiction.

## Faithfulness

The conclusion is exactly the classical dichotomy: for `p ∣ n` in
characteristic `p` the group `E(K)[n]` is a proper subgroup of `(ℤ/n)²`
— `E[p^a]` is cyclic or trivial — so the `∃!` hypothesis is unsatisfiable
there.  `hn` is used only through `n ≠ 0` (at `n = 0` the hypothesis is
satisfiable and `(0 : K) = 0` holds, so SOME positivity is needed);
`IsAlgClosed K` is what `TorsionCharP.exists_zsmul_eq_of_charP` consumes. -/
theorem natCast_ne_zero_of_geomBasis_point {K : Type} [Field K] [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic] (n : ℕ) (hn : 3 ≤ n)
    (y z : (W⁄K).Point) (hy : n • y = 0) (hz : n • z = 0)
    (hb : ∀ x : (W⁄K).Point, n • x = 0 ↔
      ∃! c : Fin n × Fin n, x = (c.1 : ℕ) • y + (c.2 : ℕ) • z) :
    (n : K) ≠ 0 := by
  intro hchar
  have hn0 : n ≠ 0 := by omega
  haveI : NeZero n := ⟨hn0⟩
  set p := ringChar K
  have hpdvd : p ∣ n := (ringChar.spec K n).mp hchar
  have hp0 : p ≠ 0 := by
    rintro h
    rw [h] at hpdvd
    exact hn0 (Nat.eq_zero_of_zero_dvd hpdvd)
  have hp : p.Prime := by
    haveI := ringChar.charP K
    rcases CharP.char_is_prime_or_zero K p with h | h
    · exact h
    · exact absurd h hp0
  have hcharp : (p : K) = 0 := ringChar.Nat.cast_ringChar
  obtain ⟨m, hm⟩ := hpdvd
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm; exact hn0 hm
  have hmlt : m < n := by
    have h2 := hp.two_le
    have : 1 * m < p * m :=
      Nat.mul_lt_mul_of_lt_of_le (by omega) (le_refl m) (Nat.pos_of_ne_zero hm0)
    omega
  set P : (W⁄K).Point := m • y with hPdef
  set Q : (W⁄K).Point := m • z with hQdef
  have hPtor : ((p : ℕ) : ℤ) • P = 0 := by
    rw [natCast_zsmul, hPdef, smul_smul, ← hm]; exact hy
  have hQtor : ((p : ℕ) : ℤ) • Q = 0 := by
    rw [natCast_zsmul, hQdef, smul_smul, ← hm]; exact hz
  obtain ⟨c0, -, huniq0⟩ := (hb 0).mp (by simp)
  have hQ0 : Q ≠ 0 := by
    intro h
    have e1 : (0 : (W⁄K).Point)
        = ((((0 : Fin n), (⟨m, hmlt⟩ : Fin n)) : Fin n × Fin n).1 : ℕ) • y
          + (((((0 : Fin n), (⟨m, hmlt⟩ : Fin n))) : Fin n × Fin n).2 : ℕ) • z := by
      simpa using h.symm
    have e2 : (0 : (W⁄K).Point)
        = ((((0 : Fin n), (0 : Fin n)) : Fin n × Fin n).1 : ℕ) • y
          + (((((0 : Fin n), (0 : Fin n))) : Fin n × Fin n).2 : ℕ) • z := by simp
    have hmz : (⟨m, hmlt⟩ : Fin n) = (0 : Fin n) :=
      congrArg Prod.snd ((huniq0 _ e1).trans (huniq0 _ e2).symm)
    exact hm0 (by simpa using congrArg Fin.val hmz)
  obtain ⟨kk, hkk⟩ := TorsionCharP.exists_zsmul_eq_of_charP W hp hcharp P Q hPtor hQtor hQ0
  obtain ⟨r, hrlt, hr⟩ := exists_lt_nsmul_eq_zsmul hn0 hz (kk * (m : ℤ))
  have hPr : P = r • z := by
    rw [hkk, hQdef, ← natCast_zsmul z m, ← mul_zsmul, hr]
  have hPtorn : n • P = 0 := by
    rw [hPdef, smul_comm]; rw [hy, smul_zero]
  obtain ⟨c, -, huniq⟩ := (hb P).mp hPtorn
  have e1 : P = ((((⟨m, hmlt⟩ : Fin n), (0 : Fin n)) : Fin n × Fin n).1 : ℕ) • y
      + (((((⟨m, hmlt⟩ : Fin n), (0 : Fin n))) : Fin n × Fin n).2 : ℕ) • z := by
    simp [hPdef]
  have e2 : P = ((((0 : Fin n), (⟨r, hrlt⟩ : Fin n)) : Fin n × Fin n).1 : ℕ) • y
      + (((((0 : Fin n), (⟨r, hrlt⟩ : Fin n))) : Fin n × Fin n).2 : ℕ) • z := by
    simpa using hPr
  have hmz : (⟨m, hmlt⟩ : Fin n) = (0 : Fin n) :=
    congrArg Prod.fst ((huniq _ e1).trans (huniq _ e2).symm)
  exact hm0 (by simpa using congrArg Fin.val hmz)

/-- **A `Fin n × Fin n`-basis of the `n`-torsion transports along an
`AddEquiv`** (PROVEN 2026-07-30) — pure bookkeeping, and the bridge between
`AbelianFullLevelStructure.geom_basis` (stated on `RelPoint f t`) and
`natCast_ne_zero_of_geomBasis_point` (stated on `(W⁄K).Point`). -/
theorem geomBasis_addEquiv {G H : Type*} [AddCommGroup G] [AddCommGroup H] (φ : G ≃+ H)
    {n : ℕ} {y z : G}
    (hb : ∀ x : G, n • x = 0 ↔ ∃! c : Fin n × Fin n, x = (c.1 : ℕ) • y + (c.2 : ℕ) • z) :
    ∀ x : H, n • x = 0 ↔
      ∃! c : Fin n × Fin n, x = (c.1 : ℕ) • φ y + (c.2 : ℕ) • φ z := by
  intro x
  have htor : n • x = 0 ↔ n • φ.symm x = 0 := by
    constructor
    · intro h
      apply φ.injective
      rw [map_nsmul, φ.apply_symm_apply, h, map_zero]
    · intro h
      rw [← φ.apply_symm_apply x, ← map_nsmul, h, map_zero]
  rw [htor, hb]
  refine existsUnique_congr (fun c => ?_)
  constructor
  · intro h
    rw [← φ.apply_symm_apply x, h, map_add, map_nsmul, map_nsmul]
  · intro h
    apply φ.injective
    rw [φ.apply_symm_apply, h, map_add, map_nsmul, map_nsmul]

end Fermat
