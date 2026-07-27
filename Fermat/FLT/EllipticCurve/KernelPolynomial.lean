/-
KernelPolynomial.lean — own work for the Fermat project (not vendored).

**The kernel-polynomial criterion for a rational cyclic isogeny**, cut
2026-07-27 out of the sorry leaf
`MazurIsogenyPrimeJ.exists_isogenyCurve_of_genusOneJTable` in
`Fermat/FLT/FreyCurve/MazurTorsion.lean`, which asks for six explicit elliptic
curves over `ℚ` with prescribed `j`-invariant, each carrying a Galois-stable
cyclic subgroup of prime order `p ∈ {11, 17, 19}`.

## What this file does

It converts the EXISTENCE of a rational cyclic `p`-isogeny — a statement about
the Galois module `E[p]`, which is what the consumer needs — into a purely
POLYNOMIAL certificate over the base field: a monic `f` of degree `(p−1)/2`
dividing the `p`-division polynomial and stable under the `x`-coordinate of
multiplication by a primitive root mod `p`.  Nothing about Galois theory, group
schemes or moduli survives the reduction: what is left is divisibility of
polynomials in `F[X]`.

## The criterion

`IsKernelPolynomial E p f m` packages, for `E` over a field `F`:

* `f` monic of degree `(p−1)/2`, dividing `ΨSq p` (so every root of `f` is the
  abscissa of a `p`-torsion point);
* `m` invertible mod `p` and generating `(ℤ/p) ∖ 0` up to sign (a primitive
  root is the intended witness);
* `f ∣ ∑ i, C (f.coeff i) ⬝ Φₘ^i ⬝ ΨSqₘ^(d−i)`, i.e. the root set of `f` is
  stable under `x(P) ↦ x(m ⬝ P)`, written multiplied-out so that no rational
  function appears.

`exists_point_of_isKernelPolynomial` then produces, over any algebraically
closed extension `L`, a point `g` of exact order `p` whose `ℤ`-span is stable
under every `F`-automorphism of `L`.

## Why the last hypothesis is the whole content

`f ∣ ΨSq p` alone does NOT give a subgroup: the roots of an arbitrary such `f`
are the abscissae of `(p−1)/2` pairs `±P` scattered across `E[p] ∖ 0`, and a
Galois-stable SET of that size is not a Galois-stable SUBGROUP.  What the
stability divisibility buys is that starting from one root `α = x(P)` the
iterates `x(m^i ⬝ P)` are again roots, and because `m` generates modulo `±1`
those iterates run through all of `x(⟨P⟩ ∖ 0)`.  A degree count — the map
`Q ↦ x(Q)` on `⟨P⟩ ∖ 0` is at most `2`-to-`1`, so its image has at least
`(p−1)/2` elements, while `f` has at most `deg f = (p−1)/2` roots — forces the
root set of `f` to be EXACTLY `x(⟨P⟩ ∖ 0)`.  Galois permutes the roots of the
rational `f`, hence permutes `x(⟨P⟩ ∖ 0)`, hence maps `⟨P⟩` into itself.

Note the argument needs only the "at most `2`-to-`1`" half of the fibre count,
which is the `x`-collision dichotomy `TorsionCard.eq_or_add_eq_zero_of_X_eq`;
the sharper "exactly `2`-to-`1`" statement (which would need `Q ≠ −Q`, i.e. `p`
odd used a second time) is not required, and no separability hypothesis on `f`
is needed either.

## Reference

Kohel, *Endomorphism rings of elliptic curves over finite fields* (thesis,
1996), §2.4; Washington, *Elliptic Curves*, ch. 12.  The classical name for `f`
is the "kernel polynomial" of the isogeny; Vélu's formulas (already in this
project, `Fermat/FLT/EllipticCurve/Velu.lean`) run the other way, from the
subgroup to the quotient curve.
-/
module

public import Fermat.FLT.EllipticCurve.TorsionCard
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace WeierstrassCurve

universe u v

/-! ### Two elementary congruence facts

Both are used only to turn the `x`-collision dichotomy into a bound on the
fibres of the abscissa map on `{1, …, p−1}`. -/

/-- **Residues below `p` are determined by their class** (PROVEN): if
`p ∣ k − l` as integers and `k, l < p`, then `k = l`. -/
theorem eq_of_intCast_sub_dvd {p k l : ℕ} (hk : k < p) (hl : l < p)
    (h : (p : ℤ) ∣ (k : ℤ) - (l : ℤ)) : k = l := by
  haveI : NeZero p := ⟨by omega⟩
  have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd ((k : ℤ) - (l : ℤ)) p).mpr h
  push_cast at h0
  rw [sub_eq_zero] at h0
  have := congrArg ZMod.val h0
  rwa [ZMod.val_natCast_of_lt hk, ZMod.val_natCast_of_lt hl] at this

/-- **A sum of two residues in `[1, p)` divisible by `p` equals `p`** (PROVEN). -/
theorem add_eq_of_dvd_add {p k l : ℕ} (hk1 : 1 ≤ k) (hk : k < p) (hl1 : 1 ≤ l) (hl : l < p)
    (h : p ∣ k + l) : k + l = p := by
  obtain ⟨t, ht⟩ := h
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with rfl | h'
    · omega
    · exact h'
  have ht2 : t < 2 := by
    by_contra hc
    have hc2 : 2 ≤ t := Nat.not_lt.mp hc
    have : p * 2 ≤ p * t := Nat.mul_le_mul_left p hc2
    omega
  have htt : t = 1 := by omega
  subst htt
  omega

/-- **The abscissa of an affine point**, with the junk value `0` at the point
at infinity.

The junk value is harmless everywhere it is used below: every statement about
`pointAbscissa` is guarded by the point being nonzero. -/
def pointAbscissa {R : Type*} [CommRing R] {W : WeierstrassCurve.Affine R} :
    W.Point → R
  | .zero => 0
  | .some x _ _ => x

@[simp]
lemma pointAbscissa_some {R : Type*} [CommRing R] {W : WeierstrassCurve.Affine R}
    {x y : R} (h : W.Nonsingular x y) :
    pointAbscissa (Affine.Point.some x y h) = x :=
  rfl

/-- **The kernel-polynomial certificate for a cyclic `p`-isogeny.**

See the module docstring for what each field is doing.  The intended witness
for `m` is a primitive root modulo `p`; `generates` asks only that the powers of
`m` cover `(ℤ/p) ∖ 0` up to sign, which is what the abscissae see. -/
structure IsKernelPolynomial {F : Type u} [Field F] (E : WeierstrassCurve F)
    (p : ℕ) (f : F[X]) (m : ℕ) : Prop where
  /-- `f` is monic. -/
  monic : f.Monic
  /-- `f` has the degree of a kernel polynomial at level `p`. -/
  natDegree_eq : f.natDegree = (p - 1) / 2
  /-- Every root of `f` is the abscissa of a `p`-torsion point. -/
  dvd_ΨSq : f ∣ E.ΨSq (p : ℤ)
  /-- The multiplier `m` is invertible modulo `p`. -/
  mult_ne_zero : (m : ZMod p) ≠ 0
  /-- The powers of `m` cover `(ℤ/p) ∖ 0` up to sign. -/
  generates : ∀ k : ZMod p, k ≠ 0 → ∃ i : ℕ, (m : ZMod p) ^ i = k ∨ (m : ZMod p) ^ i = -k
  /-- The root set of `f` is stable under `x(P) ↦ x(m ⬝ P)`, written as a
  polynomial divisibility so that no rational function appears: this is
  `f ∣ ΨSqₘ^d ⬝ f(Φₘ / ΨSqₘ)` cleared of denominators. -/
  dvd_multComp : f ∣ ∑ i ∈ Finset.range (f.natDegree + 1),
      C (f.coeff i) * E.Φ (m : ℤ) ^ i * E.ΨSq (m : ℤ) ^ (f.natDegree - i)

/-- **The kernel-polynomial criterion** (PROVEN 2026-07-27): a kernel-polynomial
certificate over `F` produces, over any algebraically closed extension `L`, a
point of exact order `p` whose `ℤ`-span is stable under every `F`-automorphism
of `L` — i.e. a rational cyclic `p`-isogeny on `E`.

The proof is the degree count described in the module docstring. -/
theorem exists_point_of_isKernelPolynomial {F : Type u} [Field F] {L : Type v} [Field L]
    [Algebra F L] [IsAlgClosed L] [DecidableEq L] {E : WeierstrassCurve F} [E.IsElliptic]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {f : F[X]} {m : ℕ}
    (hf : E.IsKernelPolynomial p f m) :
    ∃ g : (E⁄L).Point, addOrderOf g = p ∧
      ∀ σ : L ≃ₐ[F] L, ∀ x ∈ AddSubgroup.zmultiples g,
        Affine.Point.map σ.toAlgHom x ∈ AddSubgroup.zmultiples g := by
  haveI : (E⁄L).IsElliptic := inferInstanceAs ((E.map (algebraMap F L)).IsElliptic)
  set fL : L[X] := f.map (algebraMap F L) with hfLdef
  -- ## numerology
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by
    rcases hpodd with ⟨t, ht⟩
    have := hp.two_le
    omega
  have hdd : 2 * f.natDegree = p - 1 := by
    rw [hf.natDegree_eq]
    rcases hpodd with ⟨t, ht⟩
    omega
  have hdpos : 0 < f.natDegree := by omega
  -- ## the mapped polynomial
  have hfLmonic : fL.Monic := hf.monic.map _
  have hfL0 : fL ≠ 0 := hfLmonic.ne_zero
  have hfLdeg : fL.natDegree = f.natDegree := hf.monic.natDegree_map _
  -- ## division polynomials after base change
  have hΨmap : ∀ n : ℤ, (E⁄L).ΨSq n = (E.ΨSq n).map (algebraMap F L) := by
    intro n; rw [← WeierstrassCurve.map_ΨSq]; rfl
  have hΦmap : ∀ n : ℤ, (E⁄L).Φ n = (E.Φ n).map (algebraMap F L) := by
    intro n; rw [← WeierstrassCurve.map_Φ]; rfl
  -- ## a root of `fL`
  have hfLdegne : fL.degree ≠ 0 :=
    (Polynomial.natDegree_pos_iff_degree_pos.mp (by omega)).ne'
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root fL hfLdegne
  have hαroot : fL.eval α = 0 := hα
  -- ## `α` is the abscissa of a `p`-torsion point
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hΨα : ((E⁄L).ΨSq (p : ℤ)).eval α = 0 := by
    have hdvdL : fL ∣ (E⁄L).ΨSq (p : ℤ) := by
      rw [hΨmap, hfLdef]; exact Polynomial.map_dvd _ hf.dvd_ΨSq
    obtain ⟨q, hq⟩ := hdvdL
    rw [hq, Polynomial.eval_mul, hαroot, zero_mul]
  obtain ⟨y₀, hy₀⟩ : ∃ y : L, (E⁄L).toAffine.Nonsingular α y := by
    have hdeg : (TorsionCard.yQuad (E⁄L) α).degree ≠ 0 :=
      (Polynomial.natDegree_pos_iff_degree_pos.mp
        (by rw [TorsionCard.yQuad_natDegree]; norm_num)).ne'
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg
    exact ⟨y, Affine.equation_iff_nonsingular.mp
      ((TorsionCard.eval_yQuad_eq_zero_iff_equation (E⁄L) α y).mp hy)⟩
  set P : (E⁄L).Point := Affine.Point.some α y₀ hy₀ with hPdef
  have hPne : P ≠ 0 := by
    rw [hPdef]; exact Affine.Point.some_ne_zero hy₀
  have hPtors : (p : ℤ) • P = 0 :=
    (TorsionCard.smul_some_eq_zero_iff (E⁄L) hpZ hy₀ :
      ((p : ℤ) • (Affine.Point.some α y₀ hy₀ : (E⁄L).Point) = 0) ↔
        ((E⁄L).ΨSq (p : ℤ)).eval α = 0).mpr hΨα
  have hord : addOrderOf P = p := by
    have hdvd : addOrderOf P ∣ p := by
      rw [← addOrderOf_dvd_iff_zsmul_eq_zero] at hPtors
      exact_mod_cast hPtors
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp _ hdvd) with h1 | h1
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) hPne
    · exact h1
  -- ## `n • P = 0` exactly when `p ∣ n`
  have hzero_iff : ∀ n : ℤ, n • P = 0 ↔ (p : ℤ) ∣ n := by
    intro n
    rw [← addOrderOf_dvd_iff_zsmul_eq_zero, hord]
  -- ## a nonzero point is affine
  have hsome : ∀ Q : (E⁄L).Point, Q ≠ 0 →
      ∃ (x y : L) (h : (E⁄L).toAffine.Nonsingular x y), Q = Affine.Point.some x y h := by
    rintro (_ | ⟨x, y, h⟩) hQ
    · exact absurd rfl hQ
    · exact ⟨x, y, h, rfl⟩
  -- ## the abscissa is insensitive to negation
  have hnegabs : ∀ Q : (E⁄L).Point, pointAbscissa (-Q) = pointAbscissa Q := by
    rintro (_ | ⟨x, y, h⟩)
    · rfl
    · rw [Affine.Point.neg_some]; rfl
  -- ## `p ∤ m`
  have hpm : ¬ ((p : ℤ) ∣ (m : ℤ)) := by
    intro hc
    apply hf.mult_ne_zero
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (m : ℤ) p).mpr hc
    push_cast at h0
    exact h0
  have hmZ : (m : ℤ) ≠ 0 := fun hc => hpm (hc ▸ dvd_zero _)
  have hpmnat : ¬ (p ∣ m) := fun hc => hpm (Int.natCast_dvd_natCast.mpr hc)
  -- ## the one step of the iteration
  have step : ∀ Q : (E⁄L).Point, Q ≠ 0 → (m : ℤ) • Q ≠ 0 →
      fL.eval (pointAbscissa Q) = 0 →
      fL.eval (pointAbscissa ((m : ℤ) • Q)) = 0 := by
    rintro (_ | ⟨x, y, h⟩) hQ0 hmQ0 hroot
    · exact absurd rfl hQ0
    · rw [pointAbscissa_some] at hroot
      have hΨne : ((E⁄L).ΨSq (m : ℤ)).eval x ≠ 0 := fun hc =>
        hmQ0 ((TorsionCard.smul_some_eq_zero_iff (E⁄L) hmZ h :
          ((m : ℤ) • (Affine.Point.some x y h : (E⁄L).Point) = 0) ↔
            ((E⁄L).ΨSq (m : ℤ)).eval x = 0).mpr hc)
      obtain ⟨x', y', h', heq, hx'⟩ :
          ∃ (x' y' : L) (h' : (E⁄L).toAffine.Nonsingular x' y'),
            (m : ℤ) • (Affine.Point.some x y h : (E⁄L).Point) =
              Affine.Point.some x' y' h' ∧
            x' * ((E⁄L).ΨSq (m : ℤ)).eval x = ((E⁄L).Φ (m : ℤ)).eval x :=
        TorsionCard.exists_smul_some_eq (E⁄L) hmZ h hΨne
      rw [heq, pointAbscissa_some]
      -- the stability divisibility, mapped to `L` and evaluated at `x`
      have hGeval : (∑ i ∈ Finset.range (f.natDegree + 1),
          fL.coeff i * (((E⁄L).Φ (m : ℤ)).eval x) ^ i *
            (((E⁄L).ΨSq (m : ℤ)).eval x) ^ (f.natDegree - i)) = 0 := by
        obtain ⟨q, hq⟩ := hf.dvd_multComp
        have hmapped : (∑ i ∈ Finset.range (f.natDegree + 1),
            C (fL.coeff i) * ((E⁄L).Φ (m : ℤ)) ^ i *
              ((E⁄L).ΨSq (m : ℤ)) ^ (f.natDegree - i)) = fL * q.map (algebraMap F L) := by
          have hmq := congrArg (Polynomial.map (algebraMap F L)) hq
          rw [Polynomial.map_mul, Polynomial.map_sum] at hmq
          rw [← hmq]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_pow,
            Polynomial.map_pow, Polynomial.map_C, hΨmap, hΦmap, hfLdef,
            Polynomial.coeff_map]
        have hev := congrArg (Polynomial.eval x) hmapped
        rw [Polynomial.eval_mul, hroot, zero_mul, Polynomial.eval_finsetSum] at hev
        rw [← hev]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_pow, Polynomial.eval_C]
      have hΦx : ((E⁄L).Φ (m : ℤ)).eval x = x' * ((E⁄L).ΨSq (m : ℤ)).eval x := hx'.symm
      have hfac : (((E⁄L).ΨSq (m : ℤ)).eval x) ^ f.natDegree * fL.eval x' = 0 := by
        have hrw : (((E⁄L).ΨSq (m : ℤ)).eval x) ^ f.natDegree * fL.eval x' =
            ∑ i ∈ Finset.range (f.natDegree + 1),
              fL.coeff i * (((E⁄L).Φ (m : ℤ)).eval x) ^ i *
                (((E⁄L).ΨSq (m : ℤ)).eval x) ^ (f.natDegree - i) := by
          rw [Polynomial.eval_eq_sum_range' (n := f.natDegree + 1) (by omega) x',
            Finset.mul_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Finset.mem_range] at hi
          rw [hΦx, mul_pow]
          have hss : (((E⁄L).ΨSq (m : ℤ)).eval x) ^ i *
              (((E⁄L).ΨSq (m : ℤ)).eval x) ^ (f.natDegree - i) =
              (((E⁄L).ΨSq (m : ℤ)).eval x) ^ f.natDegree := by
            rw [← pow_add]; congr 1; omega
          calc (((E⁄L).ΨSq (m : ℤ)).eval x) ^ f.natDegree * (fL.coeff i * x' ^ i)
              = fL.coeff i * x' ^ i *
                ((((E⁄L).ΨSq (m : ℤ)).eval x) ^ i *
                  (((E⁄L).ΨSq (m : ℤ)).eval x) ^ (f.natDegree - i)) := by rw [hss]; ring
            _ = fL.coeff i * (x' ^ i * (((E⁄L).ΨSq (m : ℤ)).eval x) ^ i) *
                  (((E⁄L).ΨSq (m : ℤ)).eval x) ^ (f.natDegree - i) := by ring
        rw [hrw, hGeval]
      rcases mul_eq_zero.mp hfac with hc | hc
      · exact absurd (pow_eq_zero_iff (by omega) |>.mp hc) hΨne
      · exact hc
  -- ## the iterates `m^i • P`
  have hmpow : ∀ i : ℕ, ¬ ((p : ℤ) ∣ (m : ℤ) ^ i) := by
    intro i hc
    have h1 : (p : ℤ) ∣ ((m ^ i : ℕ) : ℤ) := by push_cast; exact hc
    have h2 : p ∣ m ^ i := Int.natCast_dvd_natCast.mp h1
    exact hpmnat (hp.dvd_of_dvd_pow h2)
  have hiter : ∀ i : ℕ, fL.eval (pointAbscissa (((m : ℤ) ^ i) • P)) = 0 := by
    intro i
    induction i with
    | zero => rw [pow_zero, one_zsmul, hPdef, pointAbscissa_some]; exact hαroot
    | succ i ih =>
        have h1 : ((m : ℤ) ^ (i + 1)) • P = (m : ℤ) • (((m : ℤ) ^ i) • P) := by
          rw [pow_succ, mul_comm, mul_smul]
        rw [h1]
        refine step _ (fun hc => hmpow i ((hzero_iff _).mp hc)) (fun hc => ?_) ih
        rw [← h1] at hc
        exact hmpow (i + 1) ((hzero_iff _).mp hc)
  -- ## every nonzero multiple of `P` has abscissa a root of `fL`
  have hcong : ∀ a b : ℤ, (p : ℤ) ∣ a - b → a • P = b • P := by
    intro a b hab
    have h0 : (a - b) • P = 0 := (hzero_iff _).mpr hab
    rwa [sub_smul, sub_eq_zero] at h0
  have hkey : ∀ n : ℤ, ¬ ((p : ℤ) ∣ n) → fL.eval (pointAbscissa (n • P)) = 0 := by
    intro n hn
    have hnz : ((n : ZMod p)) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hn
    obtain ⟨i, hi⟩ := hf.generates (n : ZMod p) hnz
    rcases hi with hi | hi
    · have hdv : (p : ℤ) ∣ (m : ℤ) ^ i - n := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [hi, sub_self]
      rw [← hcong _ _ hdv]
      exact hiter i
    · have hdv : (p : ℤ) ∣ (m : ℤ) ^ i - (-n) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [hi, sub_neg_eq_add, neg_add_cancel]
      have h2 := hcong _ _ hdv
      have h3 : pointAbscissa (n • P) = pointAbscissa (((m : ℤ) ^ i) • P) := by
        rw [h2, neg_smul, hnegabs]
      rw [h3]
      exact hiter i
  -- ## the abscissa set of `⟨P⟩ ∖ 0`
  have hkndvd : ∀ k ∈ Finset.Ico 1 p, ¬ ((p : ℤ) ∣ (k : ℤ)) := by
    intro k hk hc
    rw [Finset.mem_Ico] at hk
    have h1 : (p : ℕ) ∣ k := Int.natCast_dvd_natCast.mp hc
    have := Nat.le_of_dvd (by omega) h1
    omega
  set X : Finset L := (Finset.Ico 1 p).image (fun k : ℕ => pointAbscissa ((k : ℤ) • P))
    with hXdef
  have hXsub : X ⊆ fL.roots.toFinset := by
    intro a ha
    rw [hXdef, Finset.mem_image] at ha
    obtain ⟨k, hk, rfl⟩ := ha
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hfL0]
    exact hkey _ (hkndvd k hk)
  have hrootscard : fL.roots.toFinset.card ≤ f.natDegree := by
    rw [← hfLdeg]
    exact le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' fL)
  -- ## the abscissa map is at most `2`-to-`1` on `{1, …, p−1}`
  have hfib : ∀ a ∈ X,
      ((Finset.Ico 1 p).filter (fun k : ℕ => pointAbscissa ((k : ℤ) • P) = a)).card ≤ 2 := by
    intro a _
    rcases Finset.eq_empty_or_nonempty
        ((Finset.Ico 1 p).filter (fun k : ℕ => pointAbscissa ((k : ℤ) • P) = a)) with
      he | ⟨k₀, hk₀⟩
    · rw [he]; simp
    · rw [Finset.mem_filter] at hk₀
      refine le_trans (Finset.card_le_card (?_ : _ ⊆ ({k₀, p - k₀} : Finset ℕ)))
        ((Finset.card_insert_le _ _).trans (by simp))
      intro k hk
      rw [Finset.mem_filter] at hk
      obtain ⟨x₁, y₁, h₁, he₁⟩ := hsome ((k : ℤ) • P)
        (fun hc => hkndvd k hk.1 ((hzero_iff _).mp hc))
      obtain ⟨x₂, y₂, h₂, he₂⟩ := hsome ((k₀ : ℤ) • P)
        (fun hc => hkndvd k₀ hk₀.1 ((hzero_iff _).mp hc))
      have hxx : x₁ = x₂ := by
        have e1 : pointAbscissa ((k : ℤ) • P) = x₁ := by rw [he₁, pointAbscissa_some]
        have e2 : pointAbscissa ((k₀ : ℤ) • P) = x₂ := by rw [he₂, pointAbscissa_some]
        rw [← e1, ← e2, hk.2, hk₀.2]
      rw [Finset.mem_Ico] at hk hk₀
      rcases (TorsionCard.eq_or_add_eq_zero_of_X_eq (E⁄L) h₁ h₂ hxx :
          (Affine.Point.some x₁ y₁ h₁ : (E⁄L).Point) = Affine.Point.some x₂ y₂ h₂ ∨
            (Affine.Point.some x₁ y₁ h₁ : (E⁄L).Point) +
              Affine.Point.some x₂ y₂ h₂ = 0) with hc | hc
      · have hpe : (k : ℤ) • P = (k₀ : ℤ) • P := by rw [he₁, he₂]; exact hc
        have h0 : ((k : ℤ) - (k₀ : ℤ)) • P = 0 := by rw [sub_smul, hpe, sub_self]
        have := eq_of_intCast_sub_dvd (p := p) hk.1.2 hk₀.1.2 ((hzero_iff _).mp h0)
        simp [this]
      · have h0 : ((k : ℤ) + (k₀ : ℤ)) • P = 0 := by
          rw [add_smul, he₁, he₂]; exact hc
        have hdv := (hzero_iff _).mp h0
        have hdn : p ∣ k + k₀ := by
          have : (p : ℤ) ∣ ((k + k₀ : ℕ) : ℤ) := by push_cast; exact hdv
          exact Int.natCast_dvd_natCast.mp this
        have := add_eq_of_dvd_add hk.1.1 hk.1.2 hk₀.1.1 hk₀.1.2 hdn
        have hkk : k = p - k₀ := by omega
        simp [hkk]
  have hcard1 : p - 1 ≤ 2 * X.card := by
    have h0 := Finset.card_le_mul_card_image (Finset.Ico 1 p) 2 hfib
    rwa [Nat.card_Ico] at h0
  have hXeq : X = fL.roots.toFinset :=
    Finset.eq_of_subset_of_card_le hXsub (by
      have h0 := Finset.card_le_card hXsub
      omega)
  -- ## Galois stability
  refine ⟨P, hord, ?_⟩
  have hσP : ∀ σ : L ≃ₐ[F] L,
      Affine.Point.map σ.toAlgHom P ∈ AddSubgroup.zmultiples P := by
    intro σ
    obtain ⟨h', hmapP⟩ :
        ∃ h' : (E⁄L).toAffine.Nonsingular (σ α) (σ y₀),
          Affine.Point.map (σ.toAlgHom) P = Affine.Point.some (σ α) (σ y₀) h' :=
      ⟨_, by rw [hPdef]; exact Affine.Point.map_some _ hy₀⟩
    have hσroot : fL.eval (σ α) = 0 := by
      have hev : fL.eval (σ α) = σ (fL.eval α) := by
        rw [hfLdef]
        simp [Polynomial.eval_map, ← Polynomial.aeval_def, Polynomial.aeval_algHom_apply]
      rw [hev, hαroot, map_zero]
    have hmem : σ α ∈ X := by
      rw [hXeq, Multiset.mem_toFinset, Polynomial.mem_roots hfL0]
      exact hσroot
    rw [hXdef, Finset.mem_image] at hmem
    obtain ⟨k, hk, hkeq⟩ := hmem
    obtain ⟨x₂, y₂, h₂, he₂⟩ := hsome ((k : ℤ) • P)
      (fun hc => hkndvd k hk ((hzero_iff _).mp hc))
    have hxx : σ α = x₂ := by rw [← hkeq, he₂, pointAbscissa_some]
    rw [hmapP]
    rcases (TorsionCard.eq_or_add_eq_zero_of_X_eq (E⁄L) h' h₂ hxx :
        (Affine.Point.some (σ α) (σ y₀) h' : (E⁄L).Point) = Affine.Point.some x₂ y₂ h₂ ∨
          (Affine.Point.some (σ α) (σ y₀) h' : (E⁄L).Point) +
            Affine.Point.some x₂ y₂ h₂ = 0) with hc | hc
    · have hpos : (Affine.Point.some (σ α) (σ y₀) h' : (E⁄L).Point) = (k : ℤ) • P := by
        rw [he₂]; exact hc
      rw [hpos]
      exact AddSubgroup.zsmul_mem_zmultiples _ _
    · have hneg : (Affine.Point.some (σ α) (σ y₀) h' : (E⁄L).Point) = -((k : ℤ) • P) := by
        rw [he₂]; exact (neg_eq_of_add_eq_zero_left hc).symm
      rw [hneg, ← neg_smul]
      exact AddSubgroup.zsmul_mem_zmultiples _ _
  intro σ Q hQ
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hQ
  rw [map_zsmul]
  exact AddSubgroup.zsmul_mem _ (hσP σ) n

end WeierstrassCurve
