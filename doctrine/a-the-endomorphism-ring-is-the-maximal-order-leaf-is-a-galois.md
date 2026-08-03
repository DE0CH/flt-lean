## A "THE ENDOMORPHISM RING IS THE MAXIMAL ORDER" LEAF IS A GALOIS-MODULE LEAF — and the differential character makes the bridge FREE
(2026-08-02, `flt-lean-204`, `two_torsion_add_cmSqrtEnd_of_mem_isolatedCMJInvariants`
in `ModularCurve/X0.lean`, PROVEN over a new elementary leaf.)
A leaf whose content is *"the CM order is MAXIMAL, not the conductor-`2` order"* reads
as Deuring, i.e. as the first main theorem of complex multiplication, i.e. as a theory
this pin does not have in any form. Its own docstring said exactly that ("TRUE, and the
argument is short **once `End(E_ℚ̄) = O_{−p}` is known**"), and three passes had left it.
**But the CONSEQUENCE being used is an action on SMALL TORSION, and there "which order"
is equivalent to a GALOIS-MODULE statement about that torsion — which is an elementary,
twist-invariant, DECIDABLE condition on the `j`-invariant.** The recut is `1 → 1` and it
moves the open statement from CM theory to a rational-root check on five integer cubics.
**The bridge is three steps and every one of them is already in the tree:**
1. **`End(E_ℚ̄) ⊗ ℚ` is a FIELD, for free.** `EllipticCurve/DifferentialCharacter.lean`'s
   `λ` — the scalar an isogeny acts on the invariant differential by — is a ring map into
   `ℚ̄` that is INJECTIVE (`eq_of_isDiffChar`) and `Γ_ℚ`-EQUIVARIANT (`isDiffChar_galConj`).
   So `c := λ(ψ)` satisfies the same polynomial `ψ` does, `σ c` is another root, and
   `σ ψ σ⁻¹ = ±ψ` follows by injectivity. That is `galoisConj_cmSqrtEnd`, ~90 lines
   transcribed from the existing `galoisConj_cmEndomorphism` with one polynomial changed.
2. **On `2`-torsion the `±` is INVISIBLE** (`−X = X`), so `ψ` COMMUTES with `Γ_ℚ` there —
   with no hypothesis on `j` at all.
3. So `Fix(ψ|E[2])` is `Γ`-STABLE. `#E[2] = 4` (`WeierstrassCurve.n_torsion_card`), and if
   the fixed set is proper it has order `2`, whose nonzero element is then a RATIONAL point
   of order `2`. Exclude that and the leaf follows.
**And step 3's residue is decidable arithmetic, which is the part worth stealing.** A curve
over `ℚ` with a rational point of order `2` is `y² = x(x² + Ax + B)`, whose `j`-invariant is
    j = 256 (u − 3)³ / (u − 4),        u := A² / B,
and `(A,B) ↦ u` is onto `ℚ \ {4}` (take `A = 1`, `B = 1/u`). Rational `2`-torsion is
twist-invariant, so **`E/ℚ` with `E.j = j₀ ∉ {0, 1728}` has a rational point of order `2`
iff the cubic `256(u−3)³ − j₀(u−4)` has a rational root** — one `factor` call per `j₀`.
At all five singular moduli `−32768, −884736, −884736000, −147197952000,
−262537412640768000` that cubic is IRREDUCIBLE over `ℚ` (PARI/GP 2.17.4), which is the new
leaf. The conceptual reason, for a reader who wants one: all five `p ≡ 3 mod 8`, so
`disc K = −p ≡ 5 mod 8` and `2` is INERT in `K = ℚ(√−p)`; `E[2] ≅ O_K/2 = 𝔽₄` and the
mod-`2` image sits in the normalizer of the non-split Cartan, which has no fixed vector.
**The generalisable rule: when a leaf's stated obstruction is WHICH ORDER the endomorphism
ring is, ask what the consumer does with it.** If the answer is "acts on `E[n]` for a small
`n`", the CM statement is equivalent to a statement about the `Γ`-module `E[n]`, and that is
an arithmetic condition on `j` — no CM theory, no citation. The tell that this is available
is a `λ`/differential-character (or any injective ring map `End → ` a field) in the tree:
that single object supplies commutativity of `End`, uniqueness of `√−p` up to sign, and
`Γ`-equivariance, which are exactly the three things the naive route has to buy from CM.
**Two audit corrections that fell out, and the second is the reusable shape.** The leaf's
FALSITY AUDIT covered `_hj` only. `_hψ : IsIsogeny ψ` is ALSO load-bearing **for truth**,
with an explicit witness: `E(ℚ̄)` is divisible, so `E(ℚ̄) ≅ (ℚ/ℤ)² ⊕ V` (a divisible group
is an injective `ℤ`-module), and the `AddMonoidHom` acting by `[[0,1],[−p,0]]` on the
torsion and by any `ℚ`-linear square root of `−p` on `V` satisfies `ψ² = [−p]` while
SWAPPING two nonzero `2`-torsion points. It is `2`-adic and unavoidable: `−p ≡ 5 mod 8`, so
`−p` is not a square in `ℤ₂`. **So an underscore on a hypothesis is not evidence it is
decoration — it is evidence nobody has spent it**, and here the underscored one was the
difference between a true leaf and a false one.
### Four mechanical traps, all in the point group of an elliptic curve
* **`linear_combination` NEEDS A COMMUTATIVE RING and the point group is not one.**
  `linear_combination (norm := abel) h` fails on `(E⁄ℚ̄).Point` with a confusing elaboration
  error. Use `add_left_cancel` / `add_right_cancel` / `neg_eq_of_add_eq_zero_left` plus
  `calc … := by abel`, which is what works in an `AddCommGroup`.
* **Finset intersection membership is NOT an `And`.** `hj : E.j ∈ s ∩ t` gives
  `Invalid projection` on `hj.2` — it is a `Quot.lift`, not a structure. Use
  `(Finset.mem_inter.mp hj).2`. (`Set` intersection does destructure; the two read
  identically at the call site.)
* **Pin naming drift, both hit in one proof**: `Finset.card_insert_of_not_mem` is
  `Finset.card_insert_of_notMem`, and `self_eq_add_right` / `self_eq_add_left` are gone.
  Cancellation lemmas are the stable spelling.
* **The `↑σ` coercion trap fires between YOUR spelling and an upstream theorem's.**
  `velu_point_map_symm_map`'s `Point.map ↑σ` and a locally written
  `Point.map (σ : … ≃ₐ[ℚ] …).toAlgHom` print identically and `rw` reports
  `Did not find an occurrence of the pattern`. `congrArg (Point.map …) h` crosses it, as the
  standing rule says — reach for a defeq-checking tactic on the FIRST failure, not the third.
