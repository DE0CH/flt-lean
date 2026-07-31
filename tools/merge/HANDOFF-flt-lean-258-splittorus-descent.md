# `isSplitTorusAt_of_subring_entries` — a complete route, and five verified lemmas

(2026-07-31, `flt-lean-258`, measured against `merger` `9e7f6e4b`.)

## Why this file exists

`flt-lean-258` was dispatched at `exists_levelIdealSystem_aux_of_clauses`
(`Fermat/FLT/Modularity/Patching.lean`) with the prompt saying it was "the ONE
remaining leaf of the raised-level Schlessinger machine". **It was already PROVEN
on `merger`** — commit `a170e6b8`, "Patching: prove
exists_levelIdealSystem_aux_of_clauses over one split-torus leaf", merged at
`2bd061a9`, `lake build … 5551 jobs EXIT=0`. The task was written against `main`,
and `main` is the frontier as of release 25; release 27 has not published.

So the run was spent on **the residue that proof opened**:
`isSplitTorusAt_of_subring_entries`, which exists on no branch anyone can be
dispatched at and is the genuinely last leaf of that block. Its Hilbert twin
`isHilbertSplitTorusAt_of_subring_entries` is queued (`queue1`); the `ℚ`-side one
is not, and the route below closes BOTH.

## The route: ONE fibre product, not a chain — and induct on `|A|`

The leaf's docstring proposes two routes, and recommends the second: *"Schlessinger
dévissage against `hglue` … the chain `C = C₀ ⊂ C₁ ⊂ ⋯ ⊂ C_n = A` obtained by
adjoining one element of `𝔪_A` at a time"*. **The chain is not needed and does not
by itself close the induction** — each step of it needs the raised-level condition
on a QUOTIENT of `C`, which is not available going upward, so the recursion is not
well-founded on the index alone.

What works is a single fibre product per step, with the induction on the CARDINALITY
OF THE AMBIENT RING:

Let `I := 𝔪_A^{n-1}` be the last nonvanishing power of the maximal ideal, so
`I ≠ 0` and `𝔪_A · I = 0`. Put `R := ι(C)` and `J := R ∩ I`.

* **`J` is an ideal of `A`, not merely an `R`-submodule.** This is the one step
  that uses `C ↠ k`: every `a ∈ A` is `ι(c) + m` with `m ∈ 𝔪_A`, and for `x ∈ I`,
  `m·x ∈ 𝔪_A·I = 0`, so `a·x = ι(c)·x ∈ R ∩ I`.
* **Case `J ≠ 0`.** `C ≅ A ×_{A/J} (C/ι⁻¹J)`, because `J ⊆ R`: an element of `A`
  congruent mod `J` to something in `R` is itself in `R`. Feed that square to
  `hglue` with `A₁ := C ⧸ ι⁻¹J`, `A₂ := A`, `A₀ := A ⧸ J`, `B := C`; `f₂ := mk J`
  is the surjective leg. The `A₂` input is `hHRA` through the `piScalarRight`
  identification (`isRaisedLevelHardlyRamified_of_subring_entries` already builds
  exactly that `hbc`); the `A₁` input is the INDUCTIVE HYPOTHESIS at
  `C ⧸ ι⁻¹J ↪ A ⧸ J`, converted from `pushforwardFrame` shape to `baseChange`
  shape by the already-PROVEN `isRaisedLevelHardlyRamified_baseChange_of_pushforwardFrame`.
  `Nat.card (A ⧸ J) < Nat.card A` because `J ≠ 0`.
* **Case `J = 0`.** Then `mk I ∘ ι` is still injective, so the SAME `C` embeds in
  the strictly smaller `A ⧸ I` and the inductive hypothesis applies there and
  concludes the goal verbatim — no transport at all.
* **Base of the recursion**: `ι` surjective. Then `ρC` is `pushforwardFrame ι⁻¹ ρA`
  and `isRaisedLevelHardlyRamified_pushforwardFrame` (PROVEN) finishes.

The induction therefore proves the FULL `IsRaisedLevelHardlyRamified` on `ρC`, and
the leaf is its `isSplitTorusAt` field. **It never calls
`isRaisedLevelHardlyRamified_of_subring_entries`, so there is no circularity** with
that theorem, which is proven over the leaf.

## TWO HYPOTHESES ARE MISSING FROM THE LEAF, and both are free at the call site

1. **`Function.Surjective (πA.comp C.subtype)` — `C` surjects onto the residue
   field.** The leaf's own docstring assumes it in prose (*"`C` and `A` having the
   same residue field (`πA` is surjective and factors through `C` …)"*) and BOTH of
   its recorded routes need it; it is not in the signature. Without it the leaf is
   not provable by either route, and the obvious shape of a counterexample is
   `A = 𝔽₄ ⊇ C = 𝔽₂` with `ρ(Frob) = [[0,1],[1,1]]`, whose characteristic polynomial
   `x²+x+1` splits over `𝔽₄` and not over `𝔽₂`. (That is a witness against the naive
   statement, not against the statement plus `hglue`, so it is evidence that the
   hypothesis is load-bearing rather than a refutation of the leaf.)
2. **`hQp : ∀ q ∈ Q, q ≠ p`.** `IsAuxFibreProductClause` has carried this arrow
   since `flt-lean-38` added it, and `hglue` cannot be applied without it.

Both must be threaded through `isRaisedLevelHardlyRamified_of_subring_entries` and
`auxFrameLevels_repClause_ker`. **They are discharged for free at the top**: inside
`exists_levelIdealSystem_aux_of_clauses`, `hQp` is a hypothesis of that theorem, and
`hc2' : πA.comp f = ι.comp ev` with `ev = frameEv` surjective and `ι` an isomorphism
gives `Function.Surjective (πA.comp f)`, whose range is exactly `C = f.range`. So
three signatures change and no proof above them does.

## The five lemmas, VERIFIED GREEN (Mathlib only, `lean` EXIT=0)

They are the whole ring-theoretic content of the route and are level-agnostic — the
Hilbert twin needs them verbatim. Paste them wherever the descent is written.

```lean
open IsLocalRing

/-- In a finite (hence Artinian) local ring with nonzero maximal ideal there is a
NONZERO ideal killed by the maximal ideal: the last nonvanishing power. -/
theorem exists_ne_bot_mul_maximalIdeal_eq_bot {A : Type*} [CommRing A] [Finite A]
    [IsLocalRing A] (hm : maximalIdeal A ≠ ⊥) :
    ∃ I : Ideal A, I ≠ ⊥ ∧ maximalIdeal A * I = ⊥ := by
  classical
  haveI : IsArtinianRing A := isArtinian_of_finite
  have hnil : ∃ n, maximalIdeal A ^ n = ⊥ := by
    obtain ⟨c, hc⟩ : IsNilpotent (maximalIdeal A) := by
      have h := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
      rwa [jacobson_eq_maximalIdeal (⊥ : Ideal A) bot_ne_top] at h
    exact ⟨c, hc⟩
  have hnspec : maximalIdeal A ^ (Nat.find hnil) = ⊥ := Nat.find_spec hnil
  have h0 : Nat.find hnil ≠ 0 := by
    intro h
    rw [h, pow_zero, Ideal.one_eq_top] at hnspec
    exact absurd hnspec top_ne_bot
  have h1 : Nat.find hnil ≠ 1 := by
    intro h
    rw [h, pow_one] at hnspec
    exact hm hnspec
  have hn1 : 1 < Nat.find hnil := by omega
  refine ⟨maximalIdeal A ^ (Nat.find hnil - 1), Nat.find_min hnil (by omega), ?_⟩
  have hstep : maximalIdeal A * maximalIdeal A ^ (Nat.find hnil - 1)
      = maximalIdeal A ^ (Nat.find hnil) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hstep]
  exact hnspec

/-- **The key ring-theoretic step of the subring descent.**  If `R ⊆ A` is a
subring of a local ring which surjects onto the residue field (`R + 𝔪 = A`) and
`I` is an ideal killed by `𝔪`, then `R ∩ I` is an IDEAL OF `A`, not merely an
`R`-submodule. -/
theorem exists_ideal_coe_eq_inter {A : Type*} [CommRing A] [IsLocalRing A]
    (R : Subring A) (hR : ∀ a : A, ∃ r ∈ R, a - r ∈ maximalIdeal A)
    (I : Ideal A) (hI : maximalIdeal A * I = ⊥) :
    ∃ J : Ideal A, (J : Set A) = (R : Set A) ∩ (I : Set A) := by
  refine ⟨{ carrier := (R : Set A) ∩ (I : Set A)
            add_mem' := ?_
            zero_mem' := ⟨R.zero_mem, I.zero_mem⟩
            smul_mem' := ?_ }, rfl⟩
  · rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨R.add_mem hx1 hy1, I.add_mem hx2 hy2⟩
  · rintro c x ⟨hx1, hx2⟩
    obtain ⟨r, hrR, hrm⟩ := hR c
    have hzero : (c - r) * x = 0 := by
      have hmem : (c - r) * x ∈ maximalIdeal A * I := Ideal.mul_mem_mul hrm hx2
      rw [hI] at hmem
      simpa using hmem
    have hcx : c • x = r * x := by
      have : c * x - r * x = 0 := by rw [← sub_mul]; exact hzero
      simpa [smul_eq_mul] using sub_eq_zero.mp this
    rw [hcx]
    exact ⟨R.mul_mem hrR hx1, I.mul_mem_left _ hx2⟩

/-- **`ι(C) + 𝔪 = A`**, the form in which "the subring surjects onto the residue
field" is used. -/
theorem exists_sub_mem_maximalIdeal_of_surjective_comp {C A : Type*} [CommRing C]
    [CommRing A] [IsLocalRing A] {k : Type*} [Field k] (πA : A →+* k)
    (hπA : Function.Surjective πA) (ι : C →+* A)
    (hsurj : Function.Surjective (πA.comp ι)) (a : A) :
    ∃ c : C, a - ι c ∈ maximalIdeal A := by
  obtain ⟨c, hc⟩ := hsurj (πA a)
  refine ⟨c, ?_⟩
  have hker : RingHom.ker πA = maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective πA hπA)
  rw [← hker, RingHom.mem_ker, map_sub, sub_eq_zero]
  simpa using hc.symm

/-- If `ι(C) + 𝔪 = A` and the maximal ideal VANISHES then `ι` is already onto —
this is what makes `𝔪 ≠ ⊥` available in the inductive step. -/
theorem surjective_of_maximalIdeal_eq_bot {C A : Type*} [CommRing C] [CommRing A]
    [IsLocalRing A] (ι : C →+* A) (hm : maximalIdeal A = ⊥)
    (h : ∀ a : A, ∃ c : C, a - ι c ∈ maximalIdeal A) : Function.Surjective ι := by
  intro a
  obtain ⟨c, hc⟩ := h a
  rw [hm] at hc
  exact ⟨c, (sub_eq_zero.mp (by simpa using hc)).symm⟩

/-- **THE CARTESIAN SQUARE.**  If the ideal `𝔧 ⊆ A` lies inside `ι(C)`, an element
of `A` congruent mod `𝔧` to something in `ι(C)` is ITSELF in `ι(C)`.  This is
exactly the `∀ a₁ a₂, f₁ a₁ = f₂ a₂ → ∃ b, …` hypothesis of the fibre-product
clause. -/
theorem exists_eq_of_sub_mem_of_le_range {C A : Type*} [CommRing C] [CommRing A]
    (ι : C →+* A) (𝔧 : Ideal A) (h𝔧 : (𝔧 : Set A) ⊆ Set.range ι)
    (c : C) (a : A) (hca : ι c - a ∈ 𝔧) :
    ∃ c' : C, ι c' = a ∧ c' - c ∈ Ideal.comap ι 𝔧 := by
  obtain ⟨d, hd⟩ := h𝔧 hca
  refine ⟨c - d, ?_, ?_⟩
  · rw [map_sub, hd]; ring
  · rw [Ideal.mem_comap, show c - d - c = -d by ring, map_neg, hd]
    exact neg_mem hca

/-- **CASE (ii) OF THE DESCENT.**  When `ι(C)` meets the socle ideal trivially,
`ι` composed with the quotient is still injective — so the SAME `C` embeds into
the strictly smaller ring `A ⧸ I` and the induction applies with no transport. -/
theorem injective_quotient_comp_of_inter_eq_bot {C A : Type*} [CommRing C]
    [CommRing A] (ι : C →+* A) (hι : Function.Injective ι) (I : Ideal A)
    (hIC : ∀ x : A, x ∈ Set.range ι → x ∈ I → x = 0) :
    Function.Injective ((Ideal.Quotient.mk I).comp ι) := by
  intro x y hxy
  simp only [RingHom.coe_comp, Function.comp_apply, Ideal.Quotient.eq] at hxy
  have h0 : ι x - ι y = 0 := hIC _ ⟨x - y, by rw [map_sub]⟩ hxy
  exact hι (sub_eq_zero.mp h0)
```

Imports used: `Mathlib.RingTheory.Ideal.Quotient.Operations`,
`Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic`, `Mathlib.RingTheory.Artinian.Ring`
— all already in `Patching.lean`'s cone.

## Shape of the induction to write over them

State it with an INJECTIVE RING HOM `ι : C →+* A`, not with `C : Subring A`: the
recursive calls land at `C ⧸ ι⁻¹J ↪ A ⧸ J` and at `C ↪ A ⧸ I`, neither of which is
a `Subring` of the original `A`, and the `Subring.map` bookkeeping is pure cost.
Derive the `Subring` form as a one-line corollary at `ι := C.subtype`.

```
theorem …_aux (Q) (hQp) {k} … {ρbar} (hglue) (n : ℕ) :
    ∀ {A : Type uSm} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
      [IsLocalRing A] [Algebra ℤ_[p] A] [Finite A] [DiscreteTopology A],
      Nat.card A ≤ n →
      ∀ (πA : A →+* k), Function.Surjective πA →
      ∀ {C : Type uSm} [CommRing C] … (ι : C →+* A), Function.Injective ι →
        Function.Surjective (πA.comp ι) →
      ∀ {ρC} {ρA}, (entries match) → (charFrob coeff-1 compat) →
        IsRaisedLevelHardlyRamified hpodd Q (rank_finTwoFun A) ρA →
        IsRaisedLevelHardlyRamified hpodd Q (rank_finTwoFun C) ρC
```

`induction n` (not strong induction) suffices: both recursive calls have
`Nat.card` strictly smaller, hence `≤ n`. The `zero` case is vacuous because a
local ring is nontrivial, so `Nat.card A ≥ 1`.

`exists_ne_bot_mul_maximalIdeal_eq_bot` should be strengthened in passing to also
return `I ≤ maximalIdeal A` (it is `𝔪^(n-1)` with `n ≥ 2`, so this is
`Ideal.pow_le_self`), because the quotient `A ⧸ I` needs `I ≤ ker πA` to inherit
`πA` and `IsLocalRing`.

## Build note: `Patching.lean` cannot be built on `merger` right now

`Fermat.FLT.ModularCurve.X0` is red (release 27 did not publish; see
`RELEASE-27-HANDOVER.md`), and `Patching` imports it through
`FreyCurve/MazurTorsion`. A failing `lake build` DELETES `X0.olean`, so even
`lake env lean` on `Patching.lean` then dies with `object file … does not exist`.

The workaround that does not wait for the X0 repair, and does not touch the real
build directory:

```sh
cp -rs /scratch/chend-flt/flt-lean-N/.lake/build/lib/lean /tmp/relean-N/lean
R=~/.flt-release-lake/build/lib/lean
cp --remove-destination -f "$R"/Fermat/FLT/ModularCurve/X0.*        /tmp/relean-N/lean/Fermat/FLT/ModularCurve/
cp --remove-destination -f "$R"/Fermat/FLT/FreyCurve/MazurTorsion.* /tmp/relean-N/lean/Fermat/FLT/FreyCurve/
LP=$(lake env printenv LEAN_PATH); LSP=$(lake env printenv LEAN_SRC_PATH)
LEAN_PATH="/tmp/relean-N/lean:$LP" LEAN_SRC_PATH="$LSP" \
  lean -o /tmp/relean-N/lean/Fermat/FLT/Modularity/Patching.olean Fermat/FLT/Modularity/Patching.lean
```

Two things that cost a round each and are not in the doctrine's version of this
recipe:

* **`cp -f` over a symlink WRITES THROUGH IT** into the real build directory. Use
  `cp --remove-destination`, which unlinks first. On a shared `/scratch` this is
  the difference between a private shim and corrupting your own artifacts.
* **An olean is now FIVE files**, not one: `.olean`, `.olean.private`,
  `.olean.server` and their `.hash` siblings. Overlaying only `.olean` gets you
  `failed to open file '….olean.server'`, which reads like a corrupt snapshot.
  Copy `<module>.*`.

This is sound only because nothing in `Patching`'s cone uses a name added to `X0`
since the release sha — check that before trusting a green result from it.
