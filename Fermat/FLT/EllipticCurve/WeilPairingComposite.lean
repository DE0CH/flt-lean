/-
WeilPairingComposite.lean — own work for the Fermat project (not vendored from
the FLT project).

# The Weil pairing at COMPOSITE level, and `det(F | E[N]) = q`

This module holds the composite-level Weil-pairing determinant

  `det_frobeniusTorsionEnd_of_coprime` :
      `LinearMap.det (WeilPairing.frobeniusTorsionEnd q Wbar N) = (q : ZMod N)`
      for every `N` coprime to `q`,

together with the rank-two linear algebra over a commutative ring that it rests
on and the single arithmetic leaf `exists_weilPairing_mu_nondeg_of_coprime`.

## Why it is HERE, and what moved

Every declaration below was written in `FreyCurve/IsogenySignature.lean` on
2026-07-27/28 and is MOVED HERE VERBATIM (2026-07-31), with no edit to any
statement or proof.  The reason is import direction, not content:
`EllipticCurve/HasseBound.lean` needs `det_frobeniusTorsionEnd_of_coprime` for
the `ℓ`-adic half of `natCard_ker_degreeFormEnd_abs`, and
`IsogenySignature.lean` is strictly DOWNSTREAM of `HasseBound.lean` (it cites
`HasseBound.sq_frobeniusTrace_le`), so the statement was unreachable from the
one place that needs it.  `WeilPairing.det_frobeniusTorsionEnd` is available at
PRIME level only, which decides `ℓ ∤ #ker ψ` for `ℓ ∤ d` and cannot see the
`ℓ`-adic VALUATION; the composite level is what the Smith-normal-form count on
`E[d²]` needs.

The NAMESPACE is deliberately unchanged (these declarations sit at the root, as
they did in `IsogenySignature.lean`), so every existing reference — in
`IsogenySignature.lean` itself, and the `MazurTorsion.*`/`MoretBailly.*`
cross-references in docstrings — still resolves after the move.

`frobAlgHom_apply` and `exists_algebraMap_eq_of_pow_card_eq` come along because
they are the only two `IsogenySignature.lean`-local names the block uses; a
comment-stripped token scan of the moved range found no others, and no
`HasseBound.` reference at all.  Note that
`HasseBound.exists_algebraMap_eq_of_pow_card_eq` is a DIFFERENT declaration
(same statement, inside `namespace HasseBound`); the two do not collide and
neither is deleted here.

## What is still open

`exists_weilPairing_mu_nondeg_of_coprime` — the `μ_N`-valued Weil pairing at
composite level — is a leaf and is SEPARATELY OWNED.  It was open before this
move and is open after it; nothing about the frontier changes.  Everything
between it and `det_frobeniusTorsionEnd_of_coprime` (the rank-two linear algebra
over a commutative ring, the discrete logarithm, and freeness of `Wbar[N]`) is
proven.

## Faithfulness

No statement is altered by the move, so every faithfulness audit written on
these declarations in `IsogenySignature.lean` transfers verbatim.  The audits
themselves travel with the docstrings.
-/
module

public import Fermat.FLT.EllipticCurve.WeilPairing
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.RootsOfUnity.Basic

@[expose] public section

open WeierstrassCurve WeierstrassCurve.Affine

/-- The `q`-power Frobenius of `𝔽̄_q`, as an algebra map, is `x ↦ x^q`. -/
theorem frobAlgHom_apply (q : ℕ) [Fact q.Prime] (x : AlgebraicClosure (ZMod q)) :
    WeilPairing.frobAlgHom q x = x ^ q := rfl

open Polynomial in
/-- **The fixed field of the `q`-power Frobenius on `𝔽̄_q` is `𝔽_q`**
(PROVEN 2026-07-27): if `x^q = x` then `x` is in the image of
`algebraMap (ZMod q) (AlgebraicClosure (ZMod q))`.

Counting: `X^q − X` has degree `q`, hence at most `q` roots; the `q` elements
of the image of `ZMod q` are all roots (Fermat's little theorem, `ZMod.pow_card`)
and are distinct (the algebra map is injective). So the root set IS the image.

This is the descent step of `exists_twist_curve` below. Note that
`EllipticCurve/FrobeniusFixedField.lean` develops the same fixed fields
`frobFixed q n` at every level `n`; that module is *not* in this file's import
cone, and reproving the `n = 1` case here in 25 lines is cheaper than importing
it. -/
theorem exists_algebraMap_eq_of_pow_card_eq (q : ℕ) [Fact q.Prime]
    {x : AlgebraicClosure (ZMod q)} (hx : x ^ q = x) :
    ∃ y : ZMod q, algebraMap (ZMod q) (AlgebraicClosure (ZMod q)) y = x := by
  classical
  have hq1 : 1 < q := (Fact.out : q.Prime).one_lt
  set f := algebraMap (ZMod q) (AlgebraicClosure (ZMod q)) with hf
  have hfinj : Function.Injective f := f.injective
  set p : (AlgebraicClosure (ZMod q))[X] := X ^ q - X with hp
  have hp0 : p ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero _ hq1
  have hpdeg : p.natDegree = q := FiniteField.X_pow_card_sub_X_natDegree_eq _ hq1
  have hroot : ∀ z : AlgebraicClosure (ZMod q), p.IsRoot z ↔ z ^ q = z := by
    intro z
    simp [hp, IsRoot.def, sub_eq_zero]
  set S : Finset (AlgebraicClosure (ZMod q)) := Finset.image f Finset.univ with hS
  have hScard : S.card = q := by
    rw [hS, Finset.card_image_of_injective _ hfinj, Finset.card_univ, ZMod.card]
  have hsub : S ⊆ p.roots.toFinset := by
    intro z hz
    rw [hS, Finset.mem_image] at hz
    obtain ⟨y, -, rfl⟩ := hz
    rw [Multiset.mem_toFinset, mem_roots hp0, hroot]
    rw [← map_pow, ZMod.pow_card]
  have hle : p.roots.toFinset.card ≤ S.card := by
    rw [hScard]
    exact le_trans p.roots.toFinset_card_le (le_trans (Polynomial.card_roots' p) hpdeg.le)
  have heq : S = p.roots.toFinset := Finset.eq_of_subset_of_card_le hsub hle
  have hxmem : x ∈ p.roots.toFinset := by
    rw [Multiset.mem_toFinset, mem_roots hp0, hroot]
    exact hx
  rw [← heq, hS, Finset.mem_image] at hxmem
  obtain ⟨y, -, hy⟩ := hxmem
  exact ⟨y, hy⟩

/-- **Rank-two linear algebra: `det (1 − f) = 1 − tr f + det f`** (PROVEN
2026-07-27). Over an arbitrary commutative ring, for a module with a basis
indexed by `Fin 2`. Pass to matrices (`LinearMap.det_toMatrix`,
`LinearMap.trace_eq_matrix_trace`, `LinearMap.toMatrix_one`) and expand with
`Matrix.det_fin_two` / `Matrix.trace_fin_two`.

This is what lets `trace_frobeniusTorsionEnd_eq_natCard` below be assembled
from a DETERMINANT statement — the Lefschetz congruence
`#Wbar(𝔽_q) ≡ det(1 − F)` — together with `det F = q`. Stating the Lefschetz
half as a determinant rather than as a trace is what makes it the shape a
degree theory actually produces. -/
theorem det_one_sub_fin_two {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis (Fin 2) R M) (f : Module.End R M) :
    LinearMap.det ((1 : Module.End R M) - f)
      = 1 - LinearMap.trace R M f + LinearMap.det f := by
  haveI : Module.Finite R M := Module.Finite.of_basis b
  haveI : Module.Free R M := Module.Free.of_basis b
  -- The matrix identity, isolated so that no ambient `simp` lemma can fold
  -- `(toMatrix b b g).det` back into `LinearMap.det g` (which is what a bare
  -- `simp` does here, leaving the goal unprovable by `ring`).
  have hmat : ∀ A : Matrix (Fin 2) (Fin 2) R,
      ((1 : Matrix (Fin 2) (Fin 2) R) - A).det = 1 - A.trace + A.det := by
    intro A
    have h00 : (1 : Matrix (Fin 2) (Fin 2) R) 0 0 = 1 := Matrix.one_apply_eq 0
    have h11 : (1 : Matrix (Fin 2) (Fin 2) R) 1 1 = 1 := Matrix.one_apply_eq 1
    have h01 : (1 : Matrix (Fin 2) (Fin 2) R) 0 1 = 0 :=
      Matrix.one_apply_ne (by decide)
    have h10 : (1 : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 :=
      Matrix.one_apply_ne (by decide)
    simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.sub_apply,
      h00, h11, h01, h10]
    ring
  rw [← LinearMap.det_toMatrix b, ← LinearMap.det_toMatrix b f,
    LinearMap.trace_eq_matrix_trace R b f, map_sub, LinearMap.toMatrix_one, hmat]

/-- **`Wbar[N]` is free of rank two over `ZMod N` when `N` is coprime to `q`**
(PROVEN 2026-07-27). This is exactly what coprimality buys, and it is the
hypothesis whose failure at `N = q^k`, `k ≥ 2`, made the predecessor of
`hasseWeil_trace_frobeniusTorsionEnd` FALSE (see its falsity audit below).

From `WeierstrassCurve.n_torsion_dimension` (`EllipticCurve/Torsion.lean`),
which needs `(N : 𝔽̄_q) ≠ 0`; the algebraic closure has characteristic `q`, so
that is `¬ q ∣ N`, which is `Nat.Coprime N q` for prime `q`. The additive
equivalence is made `ZMod N`-linear by `ZMod.map_smul`, exactly as in
`WeierstrassCurve.p_torsion_rank`. -/
theorem nonempty_basis_nTorsion (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] (N : ℕ)
    (hNq : Nat.Coprime N q) :
    Nonempty (Module.Basis (Fin 2) (ZMod N)
      ((Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))).nTorsion N)) := by
  haveI : CharP (AlgebraicClosure (ZMod q)) q :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod q) (AlgebraicClosure (ZMod q))).injective q
  have hqN : ¬ (q ∣ N) :=
    (Nat.Prime.coprime_iff_not_dvd (Fact.out : q.Prime)).mp hNq.symm
  have hNk : ((N : ℕ) : AlgebraicClosure (ZMod q)) ≠ 0 := fun hz =>
    hqN ((CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod q)) q N).mp hz)
  obtain ⟨φ⟩ := WeierstrassCurve.n_torsion_dimension
    (Wbar.map (algebraMap (ZMod q) (AlgebraicClosure (ZMod q)))) hNk
  let ψ : ((Wbar.map (algebraMap (ZMod q)
      (AlgebraicClosure (ZMod q)))).nTorsion N) ≃ₗ[ZMod N] (ZMod N × ZMod N) :=
    { φ with map_smul' := ZMod.map_smul φ.toAddMonoidHom }
  exact ⟨(Module.Basis.finTwoProd (ZMod N)).map ψ.symm⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Rank-two pairing transformation over a COMMUTATIVE RING** (PROVEN
2026-07-27): for a module with a basis indexed by `Fin 2` over any commutative
ring `R`, an alternating bilinear form `e` transforms under any endomorphism
`f` by the determinant, `e (f x) (f y) = det f * e x y`.

This is `WeilPairing.pairing_map_eq_det_smul` (`EllipticCurve/WeilPairing.lean`,
PROVEN) with its `[Field F]` + `Module.rank F V = 2` hypotheses replaced by
`[CommRing R]` + a given `Fin 2` basis. Nothing in that proof used division:
it passes to matrices in the basis and expands `Matrix.det_fin_two`. The only
step that genuinely needed a field was manufacturing the basis out of the rank
hypothesis, and here the basis is supplied by the caller
(`nonempty_basis_nTorsion` above, whenever `N` is coprime to `q`).

This is what makes the Weil-pairing determinant argument available at
COMPOSITE level `N`, where `ZMod N` is not a field. -/
lemma pairing_map_eq_det_smul_of_basis_fin_two {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (b : Module.Basis (Fin 2) R M)
    (e : M →ₗ[R] M →ₗ[R] R) (halt : ∀ v, e v v = 0)
    (f : M →ₗ[R] M) (x y : M) :
    e (f x) (f y) = LinearMap.det f * e x y := by
  classical
  haveI : Module.Finite R M := Module.Finite.of_basis b
  haveI : Module.Free R M := Module.Free.of_basis b
  -- skew-symmetry from the alternating property
  have hskew : ∀ v w : M, e w v = -e v w := by
    intro v w
    have h := halt (v + w)
    simp only [map_add, LinearMap.add_apply, halt v, halt w, zero_add,
      add_zero] at h
    linear_combination h
  -- the matrix of `f` in the basis `b`
  have hfb : ∀ j, f (b j) =
      LinearMap.toMatrix b b f 0 j • b 0 + LinearMap.toMatrix b b f 1 j • b 1 := by
    intro j
    have hsum := b.sum_repr (f (b j))
    rw [Fin.sum_univ_two] at hsum
    rw [← hsum]
    congr 1 <;> rw [LinearMap.toMatrix_apply]
  have hdet : LinearMap.det f =
      LinearMap.toMatrix b b f 0 0 * LinearMap.toMatrix b b f 1 1 -
      LinearMap.toMatrix b b f 0 1 * LinearMap.toMatrix b b f 1 0 := by
    rw [← LinearMap.det_toMatrix b f, Matrix.det_fin_two]
  -- both sides are bilinear; compare on basis pairs
  suffices hb : ∀ i j, e (f (b i)) (f (b j)) = LinearMap.det f * e (b i) (b j) by
    have hBB : e.compl₁₂ f f = LinearMap.det f • e := by
      refine b.ext fun i => b.ext fun j => ?_
      simpa [LinearMap.compl₁₂_apply, LinearMap.smul_apply] using hb i j
    have happ := congrArg (fun B : M →ₗ[R] M →ₗ[R] R => B x y) hBB
    simpa [LinearMap.compl₁₂_apply, LinearMap.smul_apply] using happ
  intro i j
  fin_cases i <;> fin_cases j <;>
    · simp only [Fin.mk_zero, Fin.mk_one, hfb, hdet, map_add, map_smul,
        LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, halt,
        hskew (b 0) (b 1)]
      ring

set_option backward.isDefEq.respectTransparency false in
/-- **Rank-two determinant from a UNIMODULAR alternating form** (PROVEN
2026-07-27): over a commutative ring, on a module with a `Fin 2` basis, an
endomorphism scaling an alternating form by `c` has determinant `c` — provided
the form takes at least one value that is a UNIT.

`WeilPairing.det_eq_of_conj` is this over a field, where `e x y ≠ 0` suffices
because a nonzero element of a field is cancellable. **Over `ZMod N` with `N`
composite, `e x y ≠ 0` is NOT enough** — `2 ∈ ZMod 4` is a nonzero
non-cancellable value, and `det f * 2 = c * 2` does not pin `det f`. That is
exactly why the composite-level input leaf below has to assert SURJECTIVITY of
the Weil pairing onto `μ_N` (equivalently: some value is a primitive `N`-th
root of unity) rather than merely its nondegeneracy. -/
lemma det_eq_of_conj_of_basis_fin_two {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (b : Module.Basis (Fin 2) R M)
    (e : M →ₗ[R] M →ₗ[R] R) (halt : ∀ v, e v v = 0)
    (hnd : ∃ x y, IsUnit (e x y))
    {f : M →ₗ[R] M} {c : R} (hc : ∀ x y, e (f x) (f y) = c * e x y) :
    LinearMap.det f = c := by
  obtain ⟨x, y, hxy⟩ := hnd
  have h1 := pairing_map_eq_det_smul_of_basis_fin_two b e halt f x y
  exact hxy.mul_right_cancel (h1.symm.trans (hc x y))

/-- **Surjectivity of a rank-two nondegenerate alternating pairing at
COMPOSITE level** (PROVEN 2026-07-27): on a module carrying a `Fin 2` basis
over `ZMod N`, a multiplicatively bilinear alternating pairing that is killed
by `N` and NONDEGENERATE takes a PRIMITIVE `N`-th root of unity as a value —
namely at the reference basis pair `(b 0, b 1)`.

This is Silverman *AEC* III.8.1(d) ("the Weil pairing is surjective onto
`μ_N`") in its purely linear-algebraic form, and it is what converts the
prime-level shape of the Weil-pairing statement (nondegeneracy,
`∀ x ≠ 0, ∃ y, e x y ≠ 1`) into the shape the composite-level determinant
argument actually consumes (`∃ x y, IsPrimitiveRoot (e x y) N`; see
`det_eq_of_conj_of_basis_fin_two` above for why a unit value, not merely a
nonzero one, is required over `ZMod N`).

The argument is Silverman's, with the cyclicity of `μ_N` replaced by the
rank-two structure, which makes it work verbatim over a non-field: writing
`y = c • b 0 + d • b 1`, bilinearity and alternation give
`e (b 0) y = e (b 0) (b 1) ^ d.val`, so EVERY value against `b 0` is a power
of the single reference value `ζ := e (b 0) (b 1)`. Hence if `ζ ^ l = 1` then
`e (l • b 0) y = e (b 0) y ^ l = 1` for every `y`, so nondegeneracy forces
`l • b 0 = 0`, and reading off the first coordinate of the basis gives
`(l : ZMod N) = 0`, i.e. `N ∣ l`. That is exactly `IsPrimitiveRoot ζ N`.

Note this needs NO cyclic-group theory and no root-of-unity existence input:
the primitive value is produced, not found. -/
lemma isPrimitiveRoot_pairing_of_nondegenerate_basis_fin_two
    {N : ℕ} [NeZero N] {M : Type*} [AddCommGroup M] [Module (ZMod N) M]
    (b : Module.Basis (Fin 2) (ZMod N) M)
    {G : Type*} [CommGroup G] (e : M → M → G)
    (hl : ∀ x y z, e (x + y) z = e x z * e y z)
    (hr : ∀ x y z, e x (y + z) = e x y * e x z)
    (halt : ∀ x, e x x = 1)
    (hnd : ∀ x, x ≠ 0 → ∃ y, e x y ≠ 1)
    (hpow : ∀ x y, e x y ^ N = 1) :
    IsPrimitiveRoot (e (b 0) (b 1)) N := by
  classical
  -- zero laws by cancellation
  have hzl : ∀ y, e 0 y = 1 := fun y => by
    have h := hl 0 0 y
    rw [add_zero] at h
    have h2 : e 0 y * e 0 y = e 0 y * 1 := by rw [mul_one, ← h]
    exact mul_left_cancel h2
  have hzr : ∀ u, e u 0 = 1 := fun u => by
    have h := hr u 0 0
    rw [add_zero] at h
    have h2 : e u 0 * e u 0 = e u 0 * 1 := by rw [mul_one, ← h]
    exact mul_left_cancel h2
  -- ℕ-power laws
  have hnl : ∀ (n : ℕ) (u v : M), e (n • u) v = e u v ^ n := by
    intro n u v
    induction n with
    | zero => rw [zero_nsmul, pow_zero]; exact hzl v
    | succ n ih => rw [succ_nsmul, hl, ih, pow_succ]
  have hnr : ∀ (n : ℕ) (u v : M), e u (n • v) = e u v ^ n := by
    intro n u v
    induction n with
    | zero => rw [zero_nsmul, pow_zero]; exact hzr u
    | succ n ih => rw [succ_nsmul, hr, ih, pow_succ]
  -- `ZMod N`-scalars through their ℕ-lift
  have hcast : ∀ (c : ZMod N) (u : M), c • u = c.val • u := by
    intro c u
    have h1 : ((c.val : ℕ) : ZMod N) = c := by
      rw [ZMod.natCast_val, ZMod.cast_id]
    conv_lhs => rw [← h1]
    exact Nat.cast_smul_eq_nsmul _ _ _
  -- every value against `b 0` is a power of the reference value
  have hpowval : ∀ y : M, ∃ k : ℕ, e (b 0) y = e (b 0) (b 1) ^ k := by
    intro y
    have hy : b.repr y 0 • b 0 + b.repr y 1 • b 1 = y := by
      have h := b.sum_repr y
      rwa [Fin.sum_univ_two] at h
    refine ⟨(b.repr y 1).val, ?_⟩
    conv_lhs => rw [← hy]
    rw [hr, hcast, hcast, hnr, hnr, halt, one_pow, one_mul]
  refine ⟨hpow _ _, ?_⟩
  intro l hl1
  -- `l • b 0` pairs trivially with everything, hence vanishes
  have hkill : ∀ y, e (l • b 0) y = 1 := by
    intro y
    obtain ⟨k, hk⟩ := hpowval y
    rw [hnl, hk, ← pow_mul, mul_comm, pow_mul, hl1, one_pow]
  have hzero : l • (b 0) = 0 := by
    by_contra hne
    obtain ⟨y, hy⟩ := hnd _ hne
    exact hy (hkill y)
  -- read off the first coordinate
  have hzero' : ((l : ZMod N)) • (b 0) = 0 :=
    (Nat.cast_smul_eq_nsmul (ZMod N) l (b 0)).trans hzero
  have hc : (l : ZMod N) = 0 := by
    have h := congrArg (fun z => b.repr z 0) hzero'
    simpa using h
  exact (ZMod.natCast_eq_zero_iff l N).mp hc

/-- **The `μ_N`-valued Weil pairing over `𝔽_q` at COMPOSITE level, in
NONDEGENERATE form** (sorry leaf, opened 2026-07-27 by decomposing
`exists_weilPairing_mu_of_coprime` below): on the `N`-torsion of an elliptic
curve over `𝔽_q`, `N` coprime to `q`, there is a multiplicatively bilinear
alternating pairing valued in the `N`-th roots of unity of `𝔽̄_q`,
NONDEGENERATE, and natural for the `q`-power Frobenius:
`e(Fx, Fy) = F(e(x, y))`.

THIS IS THE VERBATIM LEVEL-`N` ANALOGUE of `WeilPairing.exists_weilPairing_mu`
(`EllipticCurve/WeilPairing.lean`, PROVEN) — clause for clause, with the
prime `p` replaced by `N` and the hypothesis `hqp : q ≠ p` replaced by
`Nat.Coprime N q` (for prime `p` the two say the same thing). Nothing else
differs. The surjectivity clause that the determinant argument needs is
DERIVED from this one — see `exists_weilPairing_mu_of_coprime` immediately
below and `isPrimitiveRoot_pairing_of_nondegenerate_basis_fin_two` above — so
this leaf is now the ONLY composite-level arithmetic input, and it is a pure
"re-run the existing construction at level `N`" task.

WHAT THE RE-RUN COSTS, from an audit of the prime-level file (2026-07-27).
The divisor-theoretic construction is level-generic: `N·(P) − N·(O)` is
principal for every `P ∈ E[N]`, and the Miller-generator / Weil-reciprocity
argument never uses primality. Concretely, in `WeilPairing.lean`:

* `weilValueProp` (the admissible-setup predicate that IS the pairing's
  definition) and `weilValueProp_frobenius_transport` already take a BARE
  `(p : ℕ)` with no `[Fact p.Prime]` — they are level-generic today.
* `exists_weilValueSetup_avoiding` and `translationChar_setup_value` carry
  `[Fact p.Prime]` and `_hqp : q ≠ p`, but the coprimality hypothesis is
  UNUSED (it is underscore-named in both).
* `weilValueProp_translationChar_witness`, `weilValue_of_translationChar` and
  `weilValueProp_all_one_torsion_trivial` use primality only to produce
  `((p : 𝔽̄_q) : _) ≠ 0` (via `CharP.cast_ne_zero_of_ne_of_prime`) and
  `p ≠ 0` — both of which follow at composite level from `Nat.Coprime N q`
  exactly as in `nonempty_basis_nTorsion` above.
* `weilValueProp_self_of_two` is the `p = 2` branch of alternation; at level
  `N` the branch condition becomes `2 ∣ N` and the same `2`-torsion geometry
  applies.
* `pairing_trivial_of_radical` is the ONE genuinely field-dependent node (it
  builds a spanning pair by DIVIDING coordinates). It is not needed here:
  `nonempty_basis_nTorsion` supplies the basis directly, and the surjectivity
  consumer above replaces the radical argument entirely.

So the remaining work is confined to `EllipticCurve/WeilPairing.lean` and is
a mechanical `p := N` generalization of that file's Weil-pairing chain, NOT
new mathematics. It was deliberately not attempted here because that file has
a separate owner.

WHY IT CANNOT BE REDUCED TO THE PRIME CASE BY CRT: the prime case covers
`N = p`, not `N = p^k`, and every `N` divisible by a square needs the
prime-power level. -/
theorem exists_weilPairing_mu_nondeg_of_coprime (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] (N : ℕ)
    (hNq : Nat.Coprime N q) :
    ∃ e : ((Wbar.map (algebraMap (ZMod q)
        (AlgebraicClosure (ZMod q)))).nTorsion N) →
        ((Wbar.map (algebraMap (ZMod q)
          (AlgebraicClosure (ZMod q)))).nTorsion N) →
        (AlgebraicClosure (ZMod q))ˣ,
      (∀ x y z, e (x + y) z = e x z * e y z) ∧
      (∀ x y z, e x (y + z) = e x y * e x z) ∧
      (∀ x, e x x = 1) ∧
      (∀ x, x ≠ 0 → ∃ y, e x y ≠ 1) ∧
      (∀ x y, (e x y) ^ N = 1) ∧
      (∀ x y, e (WeilPairing.frobeniusTorsionEnd q Wbar N x)
          (WeilPairing.frobeniusTorsionEnd q Wbar N y) =
        Units.map (WeilPairing.frobAlgHom q).toRingHom.toMonoidHom (e x y)) :=
  sorry

/-- **The `μ_N`-valued Weil pairing over `𝔽_q` at COMPOSITE level** (PROVEN
2026-07-27 over `exists_weilPairing_mu_nondeg_of_coprime` above): on the
`N`-torsion of an elliptic curve over `𝔽_q`, `N` coprime to
`q`, there is a multiplicatively bilinear alternating pairing valued in the
`N`-th roots of unity of `𝔽̄_q`, SURJECTIVE onto `μ_N`, and natural for the
`q`-power Frobenius: `e(Fx, Fy) = F(e(x, y))`.

This is Silverman *AEC* III.8.1 (existence, bilinearity, alternation,
surjectivity III.8.1(d)) together with the Galois-equivariance III.8.1(e)
specialised to Frobenius — stated at level `N` rather than at a prime `p`.

WHAT IS AND IS NOT NEW HERE. `WeilPairing.exists_weilPairing_mu`
(`EllipticCurve/WeilPairing.lean`) is the VERBATIM prime-level analogue and is
PROVEN there by the divisor-theoretic construction (the coordinate ring is a
Dedekind domain; `Point.toClass` embeds the points in its class group; for an
`N`-torsion point the `N`-th power of the point ideal is principal with a
Miller generator `f_P`; the pairing is the evaluation ratio
`e(P,Q) = f_P(D_Q)/f_Q(D_P)`, well-defined and bilinear by Weil reciprocity).
**That construction never uses primality of the level** — `N·(P) − N·(O)` is
principal for any `P ∈ E[N]` — so the intended route is to re-run it with `p`
replaced by `N` under `Nat.Coprime N q`, not to invent anything new. Primality
enters the prime-level file only downstream of the construction, in the
`ZMod p`-linear-algebra layer, and THAT layer is what has already been
generalised here: see `pairing_map_eq_det_smul_of_basis_fin_two`,
`det_eq_of_conj_of_basis_fin_two` and `nonempty_basis_nTorsion` above, and
`exists_weilPairing_frobenius_of_coprime` immediately below, which are all
PROVEN at composite level.

WHY SURJECTIVITY AND NOT NONDEGENERACY. The prime-level statement asserts
`∀ x ≠ 0, ∃ y, e x y ≠ 1`, which over a field is enough to cancel. Over
`ZMod N` it is not (see `det_eq_of_conj_of_basis_fin_two`), so the clause here
is `∃ x y, IsPrimitiveRoot (e x y) N`, i.e. the pairing hits a generator of
`μ_N`. That is the standard surjectivity statement and it is what the
determinant argument consumes.

HOW THE SURJECTIVITY IS OBTAINED (2026-07-27, and this is the whole content
of the proof below). It is NOT assumed: it is DERIVED from the nondegeneracy
form `exists_weilPairing_mu_nondeg_of_coprime` above by
`isPrimitiveRoot_pairing_of_nondegenerate_basis_fin_two`, using the rank-two
freeness of `Wbar[N]` from `nonempty_basis_nTorsion`. That is Silverman *AEC*
III.8.1(d), and it works over a non-field because rank two makes every value
against `b 0` a power of the single value `e (b 0) (b 1)`, so nondegeneracy
pins that value's order to exactly `N`. Consequently the sorried arithmetic
input is now stated in EXACTLY the prime-level shape, and closing it is a
mechanical `p := N` re-run of `WeilPairing.exists_weilPairing_mu` rather than
a differently-shaped statement.

WHY IT CANNOT BE REDUCED TO THE PRIME CASE BY CRT: the prime case covers
`N = p`, not `N = p^k`, and every `N` divisible by a square needs the
prime-power level. So this is genuinely "redo the level-`N` pairing", not
"assemble the prime cases".

NOT VACUOUS, and here is the junk-witness test it survives: a constant
`e ≡ 1` satisfies bilinearity, alternation, `e^N = 1` and Frobenius naturality
but has no primitive value once `N > 1`; and an alternating form on a rank-two
module is determined up to a scalar, so the surjectivity clause forces `e` to
be the Weil pairing up to a unit. The Frobenius clause then carries the
arithmetic — it is what yields `det F = q`.

THE CHECK THAT WOULD REFUTE THE "missing" CLAIM: a `μ_N`-valued pairing on
`nTorsion N` anywhere in `Fermat/`, `.lake/packages/mathlib/` or `~/cs/FLT/`
without a primality hypothesis. THE AXIS SEARCHED was the primality binders of
this project's own Weil-pairing development (grepped 2026-07-27). -/
theorem exists_weilPairing_mu_of_coprime (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] (N : ℕ)
    (hNq : Nat.Coprime N q) :
    ∃ e : ((Wbar.map (algebraMap (ZMod q)
        (AlgebraicClosure (ZMod q)))).nTorsion N) →
        ((Wbar.map (algebraMap (ZMod q)
          (AlgebraicClosure (ZMod q)))).nTorsion N) →
        (AlgebraicClosure (ZMod q))ˣ,
      (∀ x y z, e (x + y) z = e x z * e y z) ∧
      (∀ x y z, e x (y + z) = e x y * e x z) ∧
      (∀ x, e x x = 1) ∧
      (∀ x y, (e x y) ^ N = 1) ∧
      (∃ x y, IsPrimitiveRoot (e x y) N) ∧
      (∀ x y, e (WeilPairing.frobeniusTorsionEnd q Wbar N x)
          (WeilPairing.frobeniusTorsionEnd q Wbar N y) =
        Units.map (WeilPairing.frobAlgHom q).toRingHom.toMonoidHom (e x y)) := by
  classical
  obtain ⟨e, hbl, hbr, halt, hnd, hord, hfrob⟩ :=
    exists_weilPairing_mu_nondeg_of_coprime q Wbar N hNq
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact (Fact.out : q.Prime).ne_one (Nat.coprime_zero_left q |>.mp hNq)
  haveI : NeZero N := ⟨hN0⟩
  obtain ⟨b⟩ := nonempty_basis_nTorsion q Wbar N hNq
  exact ⟨e, hbl, hbr, halt, hord, ⟨b 0, b 1,
    isPrimitiveRoot_pairing_of_nondegenerate_basis_fin_two b e hbl hbr halt
      hnd hord⟩, hfrob⟩

/-- **The `ZMod N`-valued Frobenius-twisted Weil pairing at composite level**
(PROVEN 2026-07-27 over `exists_weilPairing_mu_of_coprime` above, by discrete
logarithm): on the `N`-torsion of an elliptic curve over `𝔽_q` with `N`
coprime to `q` there is an alternating `ZMod N`-bilinear pairing taking a UNIT
value which the `q`-power Frobenius scales by `q`.

This is the exact composite-level analogue of
`WeilPairing.exists_weilPairing_frobenius`, and — unlike the `μ_N`-valued leaf
above — its derivation is entirely level-generic, which is why it is proven
here rather than left open. The discrete logarithm is taken base the primitive
value `ζ := e(x₀, y₀)` supplied by the surjectivity clause, so no separate
root-of-unity existence argument is needed: `IsPrimitiveRoot.zpowers_eq`
identifies `μ_N` with `zpowers ζ`, and `IsPrimitiveRoot.zmodEquivZPowers`
identifies that with `ZMod N` additively. The reference pair then logs to `1`,
which is where the unit value comes from — this is precisely the step that
fails if one only assumes nondegeneracy. -/
theorem exists_weilPairing_frobenius_of_coprime (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] (N : ℕ)
    (hNq : Nat.Coprime N q) :
    ∃ e : ((Wbar.map (algebraMap (ZMod q)
        (AlgebraicClosure (ZMod q)))).nTorsion N) →ₗ[ZMod N]
        (((Wbar.map (algebraMap (ZMod q)
          (AlgebraicClosure (ZMod q)))).nTorsion N) →ₗ[ZMod N] ZMod N),
      (∀ v, e v v = 0) ∧ (∃ x y, IsUnit (e x y)) ∧
      ∀ x y, e (WeilPairing.frobeniusTorsionEnd q Wbar N x)
          (WeilPairing.frobeniusTorsionEnd q Wbar N y) = (q : ZMod N) * e x y := by
  classical
  obtain ⟨e₀, hbl, hbr, halt, hord, ⟨x₀, y₀, hprim⟩, hfrob⟩ :=
    exists_weilPairing_mu_of_coprime q Wbar N hNq
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact (Fact.out : q.Prime).ne_one (Nat.coprime_zero_left q |>.mp hNq)
  haveI : NeZero N := ⟨hN0⟩
  -- the discrete logarithm base the primitive value produced by surjectivity
  set ζu : (AlgebraicClosure (ZMod q))ˣ := e₀ x₀ y₀
  have hmem : ∀ x y, e₀ x y ∈ Subgroup.zpowers ζu := by
    intro x y
    rw [hprim.zpowers_eq]
    exact (mem_rootsOfUnity N _).mpr (hord x y)
  set dlog : ∀ (_ _ : ((Wbar.map (algebraMap (ZMod q)
      (AlgebraicClosure (ZMod q)))).nTorsion N)), ZMod N :=
    fun x y => hprim.zmodEquivZPowers.symm
      (Additive.ofMul (⟨e₀ x y, hmem x y⟩ : Subgroup.zpowers ζu))
    with hdlogdef
  -- the reference pair logs to `1`, which is the unit value
  have hdunit : IsUnit (dlog x₀ y₀) := by
    have hval1 : ((Additive.toMul
        (hprim.zmodEquivZPowers (((1 : ℕ) : ZMod N)))) :
        Subgroup.zpowers ζu).1 = ζu := by
      rw [hprim.zmodEquivZPowers_apply_coe_nat 1]
      exact pow_one ζu
    have helt : (⟨e₀ x₀ y₀, hmem x₀ y₀⟩ : Subgroup.zpowers ζu) =
        Additive.toMul (hprim.zmodEquivZPowers (((1 : ℕ) : ZMod N))) :=
      Subtype.ext hval1.symm
    have h2 : dlog x₀ y₀ = ((1 : ℕ) : ZMod N) := by
      show hprim.zmodEquivZPowers.symm
        (Additive.ofMul (⟨e₀ x₀ y₀, hmem x₀ y₀⟩ : Subgroup.zpowers ζu)) = _
      rw [helt]
      exact hprim.zmodEquivZPowers.symm_apply_apply _
    rw [h2, Nat.cast_one]
    exact isUnit_one
  -- transfer of the pairing laws through the logarithm
  have hdadd_l : ∀ x y z, dlog (x + y) z = dlog x z + dlog y z := by
    intro x y z
    simp only [hdlogdef]
    have hsub : (⟨e₀ (x + y) z, hmem (x + y) z⟩ : Subgroup.zpowers ζu) =
        (⟨e₀ x z, hmem x z⟩ : Subgroup.zpowers ζu) * ⟨e₀ y z, hmem y z⟩ :=
      Subtype.ext (hbl x y z)
    rw [hsub, ofMul_mul, map_add]
  have hdadd_r : ∀ x y z, dlog x (y + z) = dlog x y + dlog x z := by
    intro x y z
    simp only [hdlogdef]
    have hsub : (⟨e₀ x (y + z), hmem x (y + z)⟩ : Subgroup.zpowers ζu) =
        (⟨e₀ x y, hmem x y⟩ : Subgroup.zpowers ζu) * ⟨e₀ x z, hmem x z⟩ :=
      Subtype.ext (hbr x y z)
    rw [hsub, ofMul_mul, map_add]
  have hdalt : ∀ x, dlog x x = 0 := by
    intro x
    simp only [hdlogdef]
    have hsub : (⟨e₀ x x, hmem x x⟩ : Subgroup.zpowers ζu) = 1 :=
      Subtype.ext (halt x)
    rw [hsub]
    rw [show Additive.ofMul (1 : Subgroup.zpowers ζu) = 0 from rfl, map_zero]
  have hdfrob : ∀ x y, dlog (WeilPairing.frobeniusTorsionEnd q Wbar N x)
      (WeilPairing.frobeniusTorsionEnd q Wbar N y) = (q : ZMod N) * dlog x y := by
    intro x y
    simp only [hdlogdef]
    have hval : e₀ (WeilPairing.frobeniusTorsionEnd q Wbar N x)
        (WeilPairing.frobeniusTorsionEnd q Wbar N y) = (e₀ x y) ^ q := by
      rw [hfrob]
      refine Units.ext ?_
      show WeilPairing.frobAlgHom q
          ((e₀ x y : (AlgebraicClosure (ZMod q))ˣ) : (AlgebraicClosure (ZMod q))) =
        (((e₀ x y) ^ q : (AlgebraicClosure (ZMod q))ˣ) : (AlgebraicClosure (ZMod q)))
      rw [Units.val_pow_eq_pow_val]
      rfl
    have hsub : (⟨e₀ (WeilPairing.frobeniusTorsionEnd q Wbar N x)
        (WeilPairing.frobeniusTorsionEnd q Wbar N y), hmem _ _⟩ :
        Subgroup.zpowers ζu) =
        (⟨e₀ x y, hmem x y⟩ : Subgroup.zpowers ζu) ^ q :=
      Subtype.ext (by
        show e₀ (WeilPairing.frobeniusTorsionEnd q Wbar N x)
          (WeilPairing.frobeniusTorsionEnd q Wbar N y) =
          ((⟨e₀ x y, hmem x y⟩ : Subgroup.zpowers ζu) ^ q :
            Subgroup.zpowers ζu).1
        rw [hval]
        rfl)
    refine Eq.trans (congrArg (fun g : Subgroup.zpowers ζu =>
      hprim.zmodEquivZPowers.symm (Additive.ofMul g)) hsub) ?_
    show hprim.zmodEquivZPowers.symm
      (Additive.ofMul ((⟨e₀ x y, hmem x y⟩ : Subgroup.zpowers ζu) ^ q)) = _
    rw [ofMul_pow, map_nsmul, nsmul_eq_mul]
  -- zero laws, then the two linear-map packagings
  have hdzero_r : ∀ x, dlog x 0 = 0 := by
    intro x
    have h2 := hdadd_r x 0 0
    rw [add_zero] at h2
    exact add_left_cancel (h2.symm.trans (add_zero _).symm)
  have hdzero_l : ∀ y, dlog 0 y = 0 := by
    intro y
    have h2 := hdadd_l 0 0 y
    rw [add_zero] at h2
    exact add_left_cancel (h2.symm.trans (add_zero _).symm)
  have heinner : ∀ x : ((Wbar.map (algebraMap (ZMod q)
      (AlgebraicClosure (ZMod q)))).nTorsion N),
      ∃ f : (((Wbar.map (algebraMap (ZMod q)
        (AlgebraicClosure (ZMod q)))).nTorsion N) →ₗ[ZMod N] ZMod N),
      ∀ y, f y = dlog x y := by
    intro x
    refine ⟨AddMonoidHom.toZModLinearMap N
      ⟨⟨dlog x, hdzero_r x⟩, hdadd_r x⟩, fun y => rfl⟩
  choose einner heinnerval using heinner
  have houter : ∃ e : ((Wbar.map (algebraMap (ZMod q)
      (AlgebraicClosure (ZMod q)))).nTorsion N) →ₗ[ZMod N]
      (((Wbar.map (algebraMap (ZMod q)
        (AlgebraicClosure (ZMod q)))).nTorsion N) →ₗ[ZMod N] ZMod N),
      ∀ x y, e x y = dlog x y := by
    refine ⟨AddMonoidHom.toZModLinearMap N
      ⟨⟨einner, ?_⟩, ?_⟩, fun x y => heinnerval x y⟩
    · refine LinearMap.ext fun y => ?_
      rw [heinnerval]
      exact hdzero_l y
    · intro x₁ x₂
      refine LinearMap.ext fun y => ?_
      rw [LinearMap.add_apply, heinnerval, heinnerval, heinnerval]
      exact hdadd_l x₁ x₂ y
  obtain ⟨e, he⟩ := houter
  refine ⟨e, fun v => (he v v).trans (hdalt v), ⟨x₀, y₀, ?_⟩, ?_⟩
  · rw [he]
    exact hdunit
  · intro x y
    rw [he, he]
    exact hdfrob x y

/-- **The Frobenius determinant on the `N`-torsion for `N` coprime to `q`**
(PROVEN 2026-07-27 over `exists_weilPairing_mu_of_coprime` above; itself
opened the same day by decomposing `trace_frobeniusTorsionEnd_eq_natCard`
below): `det F = q` on `Wbar[N]`.

This is `WeilPairing.det_frobeniusTorsionEnd` (`EllipticCurve/WeilPairing.lean`)
generalised from a PRIME level `p ≠ q` to any level coprime to `q`, and the
proof is the same three-line assembly: `nonempty_basis_nTorsion` supplies the
`Fin 2` basis, `exists_weilPairing_frobenius_of_coprime` supplies an
alternating `ZMod N`-valued form with a UNIT value that Frobenius scales by
`q`, and `det_eq_of_conj_of_basis_fin_two` reads off the determinant.

WHAT REMAINS OPEN is only the arithmetic input, isolated as the single leaf
`exists_weilPairing_mu_of_coprime` above: the `μ_N`-valued Weil pairing at
composite level. Everything between that leaf and this statement — the
rank-two linear algebra over a commutative ring, the discrete logarithm, and
the freeness of `Wbar[N]` — is now proven at composite level. -/
theorem det_frobeniusTorsionEnd_of_coprime (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) [Wbar.IsElliptic] (N : ℕ)
    (hNq : Nat.Coprime N q) :
    LinearMap.det (WeilPairing.frobeniusTorsionEnd q Wbar N) = (q : ZMod N) := by
  obtain ⟨b⟩ := nonempty_basis_nTorsion q Wbar N hNq
  obtain ⟨e, halt, hnd, hconj⟩ :=
    exists_weilPairing_frobenius_of_coprime q Wbar N hNq
  exact det_eq_of_conj_of_basis_fin_two b e halt hnd hconj

/-- **Rank-two: an alternating bilinear form transforms under an endomorphism by
its determinant** (PROVEN 2026-07-27), over an arbitrary COMMUTATIVE RING, for a
module with a basis indexed by `Fin 2`.

THIS IS THE COMPOSITE-LEVEL REPLACEMENT FOR `WeilPairing.pairing_map_eq_det_smul`,
AND IT IS SHARED INFRASTRUCTURE. That lemma (`EllipticCurve/WeilPairing.lean`) is
stated for a `2`-dimensional vector space over a FIELD, which is exactly why the
prime-level `WeilPairing.det_frobeniusTorsionEnd` does not generalise to composite
`N`: the coefficient ring at level `N` is `ZMod N`, which is not a field. The proof
here is the same argument with the rank hypothesis replaced by a given `Fin 2`
basis — nothing in it ever divides — so the field is not needed at all.

Consumers: `det_eq_of_pairing_scaling_fin_two` immediately below, and hence
`natCard_affine_point_eq_det_one_sub_frobeniusTorsionEnd`. It is equally the last
step of `det_frobeniusTorsionEnd_of_coprime` above, whose prime-level model
(`WeilPairing.det_frobeniusTorsionEnd`) closes with `WeilPairing.det_eq_of_conj`;
that leaf's owner should use `det_eq_of_pairing_scaling_fin_two` in its place and
supply the rank-two input from `nonempty_basis_nTorsion` above. -/
theorem pairing_map_eq_det_mul_fin_two {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (b : Module.Basis (Fin 2) R M) (e : M →ₗ[R] M →ₗ[R] R)
    (halt : ∀ v, e v v = 0) (f : Module.End R M) (x y : M) :
    e (f x) (f y) = LinearMap.det f * e x y := by
  classical
  haveI : Module.Finite R M := Module.Finite.of_basis b
  haveI : Module.Free R M := Module.Free.of_basis b
  -- skew-symmetry from the alternating property
  have hskew : ∀ v w : M, e w v = -e v w := by
    intro v w
    have h := halt (v + w)
    simp only [map_add, LinearMap.add_apply, halt v, halt w, zero_add, add_zero] at h
    linear_combination h
  -- the matrix of `f` in the basis `b`
  have hfb : ∀ j, f (b j) =
      LinearMap.toMatrix b b f 0 j • b 0 + LinearMap.toMatrix b b f 1 j • b 1 := by
    intro j
    have hsum := b.sum_repr (f (b j))
    rw [Fin.sum_univ_two] at hsum
    rw [← hsum]
    congr 1 <;> rw [LinearMap.toMatrix_apply]
  have hdet : LinearMap.det f =
      LinearMap.toMatrix b b f 0 0 * LinearMap.toMatrix b b f 1 1 -
      LinearMap.toMatrix b b f 0 1 * LinearMap.toMatrix b b f 1 0 := by
    rw [← LinearMap.det_toMatrix b f, Matrix.det_fin_two]
  -- both sides are bilinear; compare on basis pairs
  suffices hb : ∀ i j, e (f (b i)) (f (b j)) = LinearMap.det f * e (b i) (b j) by
    have hBB : e.compl₁₂ (f : M →ₗ[R] M) (f : M →ₗ[R] M) = LinearMap.det f • e := by
      refine b.ext fun i => b.ext fun j => ?_
      simpa [LinearMap.compl₁₂_apply, LinearMap.smul_apply] using hb i j
    have happ := congrArg (fun B : M →ₗ[R] M →ₗ[R] R => B x y) hBB
    simpa [LinearMap.compl₁₂_apply, LinearMap.smul_apply] using happ
  intro i j
  fin_cases i <;> fin_cases j <;>
    · simp only [Fin.mk_zero, Fin.mk_one, hfb, hdet, map_add, map_smul,
        LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, halt,
        hskew (b 0) (b 1)]
      ring

/-- **Rank-two: an endomorphism scaling a unit-valued alternating form by `c` has
determinant `c`** (PROVEN 2026-07-27), over an arbitrary commutative ring.

The composite-level replacement for `WeilPairing.det_eq_of_conj`, which needs a
field and `Module.rank = 2`. Nondegeneracy is asked for in the only form that
survives over a ring that is not a field: SOME value of the form is a UNIT (over a
field, "nonzero" and "a unit" agree, which is why `det_eq_of_conj` can ask for the
weaker-looking `∃ x y, e x y ≠ 0`). For the level-`N` Weil pairing this is exactly
the statement that `e(P, Q)` is a PRIMITIVE `N`-th root of unity on a basis `P, Q`
of `Wbar[N]`, i.e. that the pairing is perfect rather than merely nonzero. -/
theorem det_eq_of_pairing_scaling_fin_two {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (b : Module.Basis (Fin 2) R M) (e : M →ₗ[R] M →ₗ[R] R)
    (halt : ∀ v, e v v = 0) (hnd : ∃ x y, IsUnit (e x y)) {f : Module.End R M} {c : R}
    (hc : ∀ x y, e (f x) (f y) = c * e x y) :
    LinearMap.det f = c := by
  obtain ⟨x, y, hxy⟩ := hnd
  have h2 : LinearMap.det f * e x y = c * e x y :=
    (pairing_map_eq_det_mul_fin_two b e halt f x y).symm.trans (hc x y)
  have h3 : e x y * LinearMap.det f = e x y * c := by linear_combination h2
  exact hxy.mul_left_cancel h3

/-- **`Wbar(𝔽_q)` is the Frobenius-fixed locus of `Wbar(𝔽̄_q)`** (PROVEN
2026-07-27): the number of `𝔽_q`-points of `Wbar` equals the number of points of
the base change to `𝔽̄_q` fixed by the `q`-power Frobenius.

This is the "cheap first step" that the audit of
`natCard_affine_point_eq_det_one_sub_frobeniusTorsionEnd` below identified, and it
is the GALOIS-DESCENT half of that leaf, now discharged. Read the right-hand side
as `#ker(1 − F)` acting on `Wbar(𝔽̄_q)`: it is what turns a point count into a
statement about the isogeny `1 − F`, which is the object a degree theory speaks
about.

The proof is a bijection, not an inequality-and-count:

* the base-change map `Wbar(𝔽_q) → Wbar(𝔽̄_q)` is injective
  (`Affine.Point.map_injective`);
* its image is Frobenius-stable for free — `Affine.Point.map_baseChange` says
  `map φ ∘ baseChange = baseChange` for any `𝔽_q`-algebra map `φ`, and
  `WeilPairing.frobAlgHom q` is one (that is the whole reason it was built as an
  `AlgHom` over `ZMod q`);
* conversely a fixed point is either `0` or `some x y h` with `x^q = x` and
  `y^q = y`, so `x` and `y` descend by `exists_algebraMap_eq_of_pow_card_eq` above
  (the fixed field of `x ↦ x^q` on `𝔽̄_q` is `𝔽_q`), and the nonsingularity
  descends with them along the injective `algebraMap`
  (`Affine.baseChange_nonsingular`).

No ellipticity is needed, and no finiteness: `Nat.card` of a bijection is an
equality whether or not either side is finite. -/
theorem natCard_affine_point_eq_natCard_frobFixed (q : ℕ) [Fact q.Prime]
    (Wbar : WeierstrassCurve (ZMod q)) :
    Nat.card Wbar.toAffine.Point =
      Nat.card {P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point //
        WeierstrassCurve.Affine.Point.map (W' := Wbar) (S := ZMod q)
          (WeilPairing.frobAlgHom q) P = P} := by
  classical
  refine Nat.card_congr (Equiv.ofBijective
    (fun P : Wbar.toAffine.Point =>
      (⟨WeierstrassCurve.Affine.Point.baseChange (W' := Wbar) (ZMod q)
            (AlgebraicClosure (ZMod q)) P,
        WeierstrassCurve.Affine.Point.map_baseChange (W' := Wbar)
          (WeilPairing.frobAlgHom q) P⟩ :
        {P : (Wbar⁄(AlgebraicClosure (ZMod q))).Point //
          WeierstrassCurve.Affine.Point.map (W' := Wbar) (S := ZMod q)
            (WeilPairing.frobAlgHom q) P = P})) ⟨?_, ?_⟩)
  · intro P₁ P₂ h
    exact WeierstrassCurve.Affine.Point.map_injective
      (Algebra.ofId (ZMod q) (AlgebraicClosure (ZMod q))) (Subtype.ext_iff.mp h)
  · rintro ⟨(_ | ⟨x, y, h⟩), hP⟩
    · exact ⟨0, Subtype.ext (map_zero _)⟩
    · rw [WeierstrassCurve.Affine.Point.map_some] at hP
      simp only [WeierstrassCurve.Affine.Point.some.injEq] at hP
      obtain ⟨hx, hy⟩ := hP
      obtain ⟨x₀, hx₀⟩ := exists_algebraMap_eq_of_pow_card_eq q
        (show x ^ q = x by rw [← frobAlgHom_apply q x]; exact hx)
      obtain ⟨y₀, hy₀⟩ := exists_algebraMap_eq_of_pow_card_eq q
        (show y ^ q = y by rw [← frobAlgHom_apply q y]; exact hy)
      subst hx₀
      subst hy₀
      have hns : (Wbar⁄(ZMod q)).Nonsingular x₀ y₀ :=
        (WeierstrassCurve.Affine.baseChange_nonsingular (W := Wbar)
          (f := Algebra.ofId (ZMod q) (AlgebraicClosure (ZMod q)))
          (Algebra.ofId (ZMod q) (AlgebraicClosure (ZMod q))).injective x₀ y₀).mp h
      exact ⟨WeierstrassCurve.Affine.Point.some x₀ y₀ hns,
        Subtype.ext (WeierstrassCurve.Affine.Point.map_some
          (Algebra.ofId (ZMod q) (AlgebraicClosure (ZMod q))) hns)⟩

/-- **Rank-two Cayley–Hamilton** (PROVEN 2026-07-27): over an arbitrary
commutative ring, on a module with a `Fin 2` basis,
`f² = (tr f) • f − (det f) • 1`.

The companion of `det_one_sub_fin_two` above — that one expands `det (1 − f)`,
this one expands `f²` — and proven the same way, by transporting through
`LinearMap.toMatrix b b` and computing with `Matrix.trace_fin_two` and
`Matrix.det_fin_two`. Neither needs a field nor a `Module.rank` hypothesis, which
is exactly what makes them usable at COMPOSITE level `N`, where the coefficient
ring `ZMod N` is not a field. -/
theorem sq_eq_trace_smul_sub_det_smul_fin_two {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (b : Module.Basis (Fin 2) R M) (f : Module.End R M) :
    f * f = LinearMap.trace R M f • f - LinearMap.det f • (1 : Module.End R M) := by
  classical
  haveI : Module.Finite R M := Module.Finite.of_basis b
  haveI : Module.Free R M := Module.Free.of_basis b
  have hmat : ∀ A : Matrix (Fin 2) (Fin 2) R,
      A * A = Matrix.trace A • A - Matrix.det A • (1 : Matrix (Fin 2) (Fin 2) R) := by
    intro A
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;>
      ring
  apply (LinearMap.toMatrix b b).injective
  rw [LinearMap.toMatrix_mul, map_sub, map_smul, map_smul, LinearMap.toMatrix_one,
    LinearMap.trace_eq_matrix_trace R b f, ← LinearMap.det_toMatrix b f]
  exact hmat _

/-- **A scalar that kills an invertible endomorphism is zero** (PROVEN
2026-07-27), on a module with a `Fin 2` basis.

Over a ring that is not a field this needs the invertibility, not merely
`f ≠ 0`: in `Module.End (ZMod 4) (ZMod 4)²` the scalar `2` kills the
endomorphism `2 • 1` without being zero. Multiplying by `f⁻¹` reduces to
`c • 1 = 0`, and evaluating at a basis vector reduces that to `c = 0`. -/
theorem eq_zero_of_smul_eq_zero_of_isUnit_fin_two {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (b : Module.Basis (Fin 2) R M) {f : Module.End R M}
    (hf : IsUnit f) {c : R} (hc : c • f = 0) : c = 0 := by
  obtain ⟨u, hu⟩ := hf
  have h1 : c • (1 : Module.End R M) = 0 := by
    have h0 : (c • f) * (↑u⁻¹ : Module.End R M) = 0 := by rw [hc, zero_mul]
    rw [smul_mul_assoc, ← hu, u.mul_inv] at h0
    exact h0
  have h2 : c • b 0 = 0 := by
    have h := congrArg (fun g : Module.End R M => g (b 0)) h1
    simpa using h
  have h3 := congrArg (fun v => b.repr v 0) h2
  simpa using h3
