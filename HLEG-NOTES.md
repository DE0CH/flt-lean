# HLEG-NOTES — proof plan for `hleg1`–`hleg6` of `exists_weilPairing_mu`

Research notes (2026-07-22) for the six sorried legs at
`Fermat/FLT/EllipticCurve/WeilPairing.lean:8093-8106`. Written against the
construction as it stands (IsWeilValue at ~6649, `hexval` 6937, `hsetup3` 7306,
`hrecgen`/`huniqval` 7687-8076, `hvalue`/`e`/`hespec`/`heuniq` 8077-8090), the
engine modules `WeilPairingRecgen.lean` / `WeilPairingStepR.lean`, and
Silverman AEC §III.8 + Exercise 3.16 (`sources/silverman2009aec.txt`,
lines 9432-9930 and 11086-11135).

## 0. What `e` is, in Silverman's terms

`IsWeilValue v w z` (for affine reps `P` of `v.val`, `Q` of `w.val`) says `z`
is the cross-ratio of SOME admissible Miller setup:

* S-slot: translate `S` (data in `F'`, `xS ∉ F`), `PS = P⊕S`,
  Miller numerator `aP` with `span{aP} = I_{PS}^p · I_{⊖S}^p`
  (so `f_P := aP / XClass(xS)^p` has divisor `p(P⊕S) − p(S)`, i.e. `p·D_P`
  with `D_P = (P⊕S) − (S)`, `Σ D_P = P`);
* R-slot: translate `R` (`xR ∉ F'`), `QR = Q⊕R` (`xQR ∉ F'`), `aQ` with
  `span{aQ} = I_{QR}^p · I_{⊖R}^p` (`f_Q := aQ/XClass(xR)^p`, div `p·D_Q`,
  `D_Q = (Q⊕R) − (R)`);
* value equation (division-free, 8 evaluations):
  `z · [X_S^p(QR) · aP(R) · X_R^p(S) · aQ(PS)] = aP(QR) · X_S^p(R) · aQ(S) · X_R^p(PS)`,
  i.e. `z = f_P(D_Q)/f_Q(D_P)`.

This is exactly the **alternative Weil pairing** of Silverman Ex. 3.16
(`ẽ_m(P,Q) = f_P(D_Q)/f_Q(D_P)`), NOT the §III.8 `g`-based `e_m`. Well-definedness
(3.16(a), by Weil reciprocity) is `huniqval` — already proven modulo the `G''`
sorry at 7883. The legs must therefore be proven for the divisor form; where
Silverman's III.8.1 proof uses the `[m]`-pullback function `g`, we either find a
divisor-form substitute (legs 1, 2, 5, 6, skew) or we need new machinery
(leg 4 core, and alternation at p = 2).

Everything below uses only `heuniq`/`hespec` as the interface to `e`: to
evaluate `e v w`, construct ONE admissible setup and hand its value equation to
`heuniq`. Values from *different* pairs are related by building the setups on
SHARED translate chains and proving one span-level "Miller word identity" per
leg (the `hcomp`/`hlfac` pattern from StepR: span equality of ideal products →
`span_singleton_eq_span_singleton` → `Associated` → `hCunits` constant).

In-scope engine facts at line 8093 (all proven): `hsubfin`, `hpoints`,
`hfib2`, `hmill2`, `hgen2`, `hCunits` (4153), `hline` (4378), `hoffdiv` (4911),
`hevvert` (5244), `hnegYF/hslopeF/haddXF/haddYF` (5397-5434), `hgenfac`, `hww`,
`hbaldiv`, `hevconst`, `hevid`, `hsetup3`, `hrecgen`, `huniqval`, `hvalue`,
`hespec`, `heuniq`, `yfib/hyfib`, `xOf`. Also available from the repo:
`TorsionCard.smul_surjective` (divisibility of E(𝔽̄) — PROVEN), the
division-polynomial multiplication formulas (`TorsionCard`), and the
tautological-point machinery (`TautologicalPoint.lean`/`TautMultiplication.lean`,
sorry-free — the generic point of a curve over its own function field with
`n•(tautX,tautY)` coordinate formulas). These matter for legs 3(p=2) and 4.

## 0a. Shared preliminaries (write once, before hleg1, consumed by all legs)

```lean
-- degenerate values: from heuniq + the trivially-satisfied witness
have hdegval : ∀ v w, (v.val = 0 ∨ w.val = 0) → e v w = 1 := by
  intro v w hd
  refine heuniq v w 1 ⟨fun _ => rfl, ?_⟩
  intro xP yP hP xQ yQ hQ hv hw
  exfalso
  rcases hd with h | h
  · rw [hv, WeierstrassCurve.Affine.Point.zero_def] at h; simp at h
  · rw [hw, WeierstrassCurve.Affine.Point.zero_def] at h; simp at h
```

(Mirrors the degenerate branch of `hexval` at 6939-6947. Any leg that
case-splits on `v.val = 0` also uses `Subtype`-level facts: `x.val = 0 → x = 0`
and `zero_add`/`add_zero` to rewrite `e (x+y) z`.)

## 1. hleg1 — `∀ x y z, e (x + y) z = e x z * e y z`

**Mathematics (Silverman III.8.1(a), first slot — but done divisor-style, no
`g` needed).** Choose the second argument's setup ONCE (translate `R`, `QR`,
`aQ`), and chain the first-slot translates: `S`, `T := P₁⊕S`,
`U := (P₁+P₂)⊕S = P₂⊕T`. Then

* `D_{P₁} = (T) − (S)` (translate `S`),
* `D_{P₂} = (U) − (T)` (translate `T`),
* `D_{P₁+P₂} = (U) − (S)` (translate `S`) — and `D_{P₁} + D_{P₂} = D_{P₁+P₂}`
  on the nose, so `f_{P₁}·f_{P₂}` and `f_{P₁+P₂}` have equal divisors and agree
  up to a constant. Silverman's correction function `h` is not needed because
  the chained-translate choice makes the divisors literally add.

**Miller word identity (the one new span computation).** With
`span{aP₁} = I_T^p I_{⊖S}^p`, `span{aP₂} = I_U^p I_{⊖T}^p`,
`span{aP₁₂} = I_U^p I_{⊖S}^p`, and `XYIdeal_neg_mul` at `T`
(`I_T · I_{⊖T} = XIdeal x_T = span{XClass x_T}`):

```lean
have hmulspan :
    Ideal.span {aP₁ * aP₂} =
    Ideal.span {aP₁₂ * (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xT) ^ p} := by
  -- span{a*b} = span a * span b (Ideal.span_singleton_mul_span_singleton),
  -- rewrite by haP₁/haP₂/haP₁₂, XYIdeal_neg_mul at (xT,yT), mul_pow, ring_nf on ideals
have hmulP : ∃ c : AlgebraicClosure (ZMod q), c ≠ 0 ∧
    aP₁ * aP₂ = (AdjoinRoot.of Wb.toAffine.polynomial) (Polynomial.C c) *
      (aP₁₂ * (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xT) ^ p) := by
  -- Ideal.span_singleton_eq_span_singleton.mp hmulspan → Associated → unit → hCunits
```

This is verbatim the `hcomp` pattern of `WeilPairingStepR.lean:394-450` (~60
lines).

**Shared chain setup (the bulk of the work).** A `hchain`-construction in the
`hsetup3` style producing, for affine p-torsion reps `P₁, P₂` (with
`P₁+P₂ ≠ O` for the main case) and `Q`:

* `F₀ := hsubfin` over ALL of `P₁, P₂, P₁+P₂, Q` coordinate data;
* `S` via `hpoints` avoiding: `F₀`'s carrier, the bad-images
  `xOf(−P₁ ⊕ fiber pts of F₀-abscissas)`, `xOf(−(P₁+P₂) ⊕ …)` (so that
  `x_T ∉ F₀` and `x_U ∉ F₀` — the `hxSof`/`neg_add_cancel_left` transport of
  `hsetup3:7404-7419`), and `xOf(−P₁)`, `xOf(−(P₁+P₂))` (affineness of `T`, `U`);
* `F' := hsubfin` over `F₀ ∪ {S, T, U data}`;
* `R` via `hpoints` avoiding `F'`'s carrier plus the α-fold bad-R images
  (`xOf(−Q ⊕ fiber pts over F'-abscissas)`) so `x_{QR} ∉ F'` (the amendment-(α)
  pattern already inside `hexval`), plus `xOf(−Q)` (affineness of `QR`).

All eight `hoffdiv` nonvanishings follow from the F'-separation exactly as in
`hexval` 7634-7680: divisor abscissas of `aP₁, aP₂, aP₁₂` (namely
`x_T, x_U, x_S`) are in `F'`, evaluation points `R, QR` have abscissas outside
`F'`; divisor abscissas of `aQ` (`x_{QR}, x_R`) are outside `F'`, its
evaluation points `S, T, U` inside.

**Three witnesses + assembly.** Package the three setups as `IsWeilValue`
witnesses (F-fields: pair `(x,z)` uses `(F₀, F')` with translate `S`, PS-slot
`T`; pair `(y,z)` uses `(F₀, F')` with translate `T`, PS-slot `U`; pair
`(x+y,z)` uses `(F₀, F')` with translate `S`, PS-slot `U`; all three share
`R/QR/aQ`). Define the three values as `Units.mk0` of the B/A ratios (the
`hexval` `div_mul_cancel₀` pattern at 7295-7300), pin them with `heuniq`, then
close `z₃ = z₁·z₂` by `Units.ext`, `mul_right_cancel₀` against `A₁·A₂·A₃ ≠ 0`,
and one `linear_combination` from the three value equations plus `hmulP`
evaluated at `QR` and at `R` (via `map_mul`, `map_pow`, `hevvert`, `hevconst`).
Cross-multiplied check (done by hand, it balances): after cancelling
`X_S^p(R), aQ(S), X_R^p(T), aQ(T), X_R^p(U), X_S^p(QR), X_R^p(S), aQ(U)`,
`B₁B₂A₃ = B₃A₁A₂` reduces to
`aP₁(QR)aP₂(QR) · X_T^p(R) · aP₁₂(R) = aP₁₂(QR) · aP₁(R)aP₂(R) · X_T^p(QR)`,
which is exactly the two `hmulP` evaluations.

**Special cases.**
* `z.val = 0`, `x.val = 0`, `y.val = 0`: `hdegval` + `zero_add`/`add_zero`.
* `x.val + y.val = 0` (i.e. `P₂ = ⊖P₁`, so `(x+y).val = 0`): target
  `1 = e x z * e y z`. Same chain with `U = S`; the word identity becomes
  `aP₁ * aP₂ = C c * XClass(x_S)^p * XClass(x_T)^p`
  (span: `I_T^p I_{⊖S}^p · I_S^p I_{⊖T}^p = (I_S I_{⊖S})^p (I_T I_{⊖T})^p`,
  two `XYIdeal_neg_mul`s), and `B₁B₂ = A₁A₂` follows by substituting it at `QR`
  and `R`. (Checked by hand; balances.)
* Note `x = y` needs no special treatment.

**Effort:** chain construction ~600-800 lines (mechanical `hsetup3` variant);
witnesses + assembly ~300-400; word identities ~100; special case ~150.
**Strong recommendation:** extract the chain construction and the assembly as a
standalone theorem in a NEW module (`WeilPairingLeg12.lean`, say), engine facts
passed as hypothesis parameters exactly like `stepR`, to keep the μ-theorem's
elaboration time under control. It can serve hleg1 and hleg2 with the slot
roles as parameters if designed symmetrically, but two separate theorems
following one template is the lower-risk plan.

## 2. hleg2 — `∀ x y z, e x (y + z) = e x y * e x z`

Mirror of hleg1 with the chain on the R-side. Shared S-slot `(S, PS, aP)` for
all three pairs; R-chain `R`, `T' := Q₁⊕R` (`QR` of pair `(x,y)` AND translate
of pair `(x,z)`), `U' := Q₂⊕T' = (Q₁+Q₂)⊕R` (`QR` of pairs `(x,z)` and
`(x,y+z)`). Word identity:

```lean
have hmulQ : ∃ c ≠ 0, aQ₁ * aQ₂ =
    (AdjoinRoot.of Wb.toAffine.polynomial) (Polynomial.C c) *
      (aQ₁₂ * (WeierstrassCurve.Affine.CoordinateRing.XClass Wb.toAffine xT') ^ p)
-- spans: I_{T'}^p I_{⊖R}^p · I_{U'}^p I_{⊖T'}^p = I_{U'}^p I_{⊖R}^p · (I_{T'} I_{⊖T'})^p
```

Construction difference: here the whole chain must AVOID `F'` (R-slot
constraints), so `F' := hsubfin(F₀ ∪ S,PS data)` first, then `R` chosen with
iterated α-folds so that all of `x_R, x_{T'}, x_{U'} ∉ F'` (three image-finsets
over `F'`-fibers: `xOf(−Q₁ ⊕ ·)`, `xOf(−(Q₁+Q₂) ⊕ ·)`, plus the direct fold for
`x_R`), plus affineness avoidances `xOf(−Q₁), xOf(−(Q₁+Q₂))`.
Cross-multiplied check (done, balances): after cancellation
`B₁B₂A₃ = B₃A₁A₂` reduces to
`aQ₁(S)aQ₂(S) · X_{T'}^p(PS) · aQ₁₂(PS) = aQ₁₂(S) · X_{T'}^p(S) · aQ₁(PS)aQ₂(PS)`
= the two `hmulQ` evaluations at `S` and `PS`.
Degenerate/`y+z = 0` cases exactly as in hleg1 (word identity
`aQ₁·aQ₂ = C c · X_R^p · X_{T'}^p`).

**Effort:** same as hleg1; second instance of the template.

## 3. hleg3 — `∀ x, e x x = 1` (alternation)

This is the leg where Silverman's proof (III.8.1(b), the telescoping product
`∏ f∘τ_{[i]T}` and its `g`-counterpart) genuinely uses the `[m]`-pullback `g`;
the divisor pairing does not admit a translation-free one-liner. Plan: split
`p = 2` vs odd.

**(a) Skew-symmetry for the self-pair via the swap setup (all p).**
For the pair `(x,x)` (rep `P`), build TWO setups from two mutually-deep
R-families `R₂, R₃` and the SAME Miller generators:

* `a₂` := Miller for `(P⊕R₂, ⊖R₂)`, `a₃` := Miller for `(P⊕R₃, ⊖R₃)`
  (from `hmill2`);
* Setup A: S-slot translate `R₂` (fields `F₀ ≤ F'_A := ⟨F₀ ∪ R₂, P⊕R₂ data⟩`),
  R-slot translate `R₃` — requires `x_{R₃}, x_{P⊕R₃} ∉ F'_A`;
* Setup B: S-slot translate `R₃` (`F'_B := ⟨F₀ ∪ R₃, P⊕R₃ data⟩`), R-slot
  translate `R₂` — requires `x_{R₂}, x_{P⊕R₂} ∉ F'_B`.

Because the generators are literally shared, the two value equations have
identical atoms with the two sides swapped: A: `z·L = R`; B: `z·R = L`. Hence
`z²·(L·R) = L·R` and `z² = 1` (`L, R ≠ 0` from the two setups' nonvanishing
conjuncts). No new reciprocity needed — `huniqval` does all the work.

The mutual-depth requirement is the SAME subfield-lattice problem as the
pending `G''` sorry (line 7883) and should share its machinery. Needed brick
(the `K(n)` lattice; coordinate with the `G''` worker):

```lean
-- the Frobenius-power fixed subfields K n = 𝔽_{q^n}
have hKfix : ∀ n : ℕ, 0 < n → ∃ K : Subfield (AlgebraicClosure (ZMod q)),
    (K : Set _).Finite ∧ (∀ a, a ∈ K ↔ a ^ q ^ n = a) ∧ ...
-- deep-point selection: an abscissa in K(ℓ·m) outside every subfield whose
-- degree is not divisible by ℓ, avoiding a given finite set — by counting
-- (#K(ℓm) = q^(ℓm) exceeds the union of smaller subfields + avoid set);
-- ordinates land in K(2ℓm) via hfib2 (the fiber pair is Frob^(ℓm)-stable).
```

Then choose `R₂`-data inside `K(ℓ₂·m)` and `R₃`-data inside `K(ℓ₃·m)` for
distinct large primes `ℓ₂ ≠ ℓ₃` not dividing `m := deg F₀`-closure data:
`x_{R₃} ∈ F'_A` would force `ℓ₃ | deg F'_A` with `deg F'_A | 2ℓ₂m·(bounded)`,
contradiction; symmetrically for B. The membership promises
(`x_{P⊕R₂} ∈ K(2ℓ₂m)` etc.) come from `haddXF/hslopeF/hnegYF` closure.

**(b) Odd p:** `z² = 1` and `z^p = 1` (hleg5's argument, but derivable here
directly from hleg1, which is already in scope: `e(p•x, x) = e(x,x)^p` by the
first-slot induction below, and `p•x = 0`), `gcd(2,p) = 1` ⟹ `z = 1`
(`orderOf_dvd`… or elementary: `z = z^(2t+... )`; in Lean:
`z ^ (2 * s + p * t) = z` for `2s + pt = 1`… cleanest:
`Nat.Coprime.eq_one_of_dvd` on `orderOf z ∣ 2` and `∣ p`).

**(c) p = 2 (the residual hard case).** For `p = 2` skew is vacuous
(`z² = z^p = 1` already), and abstractly bilinear + symmetric + nondegenerate
forms with `Q ≢ 1` exist over `𝔽₂`, so genuine geometry is required. Two
options:

* **(c-i) Explicit line-square grind (recommended first attempt).** For
  2-torsion `P`: `⊖P = P`, so `XYIdeal_neg_mul` gives `I_P² = span{XClass xP}`,
  and `hline` at the pair `(T, ⊖S)` (third point `⊖P = P`) gives
  `span{ℓ₁} = I_T · I_{⊖S} · I_P` with `ℓ₁` the EXPLICIT line element; hence
  `aP · XClass(xP) = c · ℓ₁²` (hCunits pattern), and similarly
  `aQ · XClass(xP) = c' · ℓ₂²` on the R-side. Substituting into the value
  equation makes `z = β²` for an explicit rational `β` in the configuration
  coordinates; `z = 1` becomes ONE polynomial identity in
  `(xP,yP,xS,yS,xR,yR)` modulo the curve equations, the 2-torsion relation
  `2yP = −a₁xP − a₃`, and the addition formulas for `T = P⊕S`, `PR = P⊕R` —
  in principle closable by `field_simp` + `linear_combination` after
  substituting `add_some_coords`-style formulas. **Verify the identity in a
  CAS (sympy) before attempting Lean**; if it fails as stated, the missing
  factor is a tame-symbol sign and the bookkeeping must be rechecked against
  the `hww` sign conventions. Risk: medium-high; effort ~400-800 lines.
* **(c-ii) Uniform Silverman proof via the `g`-machinery** built for leg 4
  (below): once L4a-L4g exist, III.8.1(b) formalizes verbatim for all `p`
  (`∏_{i<p} g∘τ_{[i]T'}` constant ⟹ `g∘τ_P = g` ⟹ value 1 via the bridge
  lemma L4h). If leg 4's machinery lands first, drop (c-i).

Decomposition advice: write hleg3 as the odd/2 case split now, close the odd
branch, and leave `p = 2` as a named sorried sub-have
(`have hleg3_two : p = 2 → ∀ x, e x x = 1`), consumed by the split.

**STATUS UPDATE (2026-07-24): the `p = 2` case is PROVEN.**
`weilValueProp_self_of_two` (WeilPairing.lean, after
`end FrobeniusTransport`) is sorry-free: the (c-i) line-square route
went through in full. Structure: witness destructured; 2-torsion
relation; `aP·XClass x_P = c·ℓ²` factorizations through the extracted
`MillerEngine` lemmas (`coordRing_isUnit_constant`,
`coordRing_line_span`, `coordRing_evalEval_XClass`); evaluation at the
four points; and the residual polynomial identity `hkey` CLOSED via
the new module `WeilPairingTwoLine.lean`:

* `two_line_reciprocity` — the 8-line-value reciprocity core (hkey
  divided by the four norm factorizations; all x-difference monomials
  cancel pairwise, sign +1). Proven by a machine-generated 123KB
  `linear_combination` certificate: Singular `lift` over the
  substituted configuration ring (eliminations: `x_P, y_PS, y_P,
  y_QR, a₆, a₃` — all exact polynomial substitutions), lifted back to
  the eleven hypothesis generators by exact sequential polynomial
  division, and re-verified symbolically (sympy `expand == 0`).
* `line_norm_cubic` — `ℓ(T)·ℓ(⊖T) = −(x_T−x_B)(x_T−x_U)(x_T−x_P)`,
  small per-branch certificates (chord: localized at `x_U − x_B`;
  tangent: via the tangent-slope relation — plain ideal membership
  FAILS without the slope data, as the phantom-tangent locus breaks
  the factorization).
* `norm_reciprocity_assembly` — atom-level assembly; keeps the heavy
  `ring` normalization out of WeilPairing.lean (the inlined version
  stack-overflowed the LSP file worker even though the CLI accepted
  it).

The μ-theorem's `htwo` is therefore closed (modulo the in-proof
`huniqval`/`hDD`, which it instantiates). Certificate-generation
scripts from this session: scratchpad `lift8.py`, `liftnorm.py`,
`gen_lean8.py` (Singular + sympy pipeline; the pattern is reusable for
any future configuration identity).

**The (c-i) identity is CAS-VERIFIED (chord AND tangent branches).**
With `⊖P = P`, `aP·X_{xP} = c₁ℓ₁²` (ℓ₁ through `PS, ⊖S`, third point
`P`), `aQ·X_{xP} = c₂ℓ₂²` (ℓ₂ through `QR, ⊖R`, third point `P`), the
value equation reduces `z = 1` to

```
ℓ₁(QR)²·ℓ₂(S)²·(x_PS−x_R)²·(x_R−x_P)(x_PS−x_P)
  = ℓ₁(R)²·ℓ₂(PS)²·(x_QR−x_S)²·(x_QR−x_P)(x_S−x_P)
```

modulo the five curve equations, the 2-torsion relation
`2y_P = −a₁x_P − a₃`, and the addition/collinearity relations for
`PS = P⊕S`, `QR = P⊕R`.

**Attack plan for the residual `hkey` leaf** (the in-context scalar
relations that suffice; derivations of (1)-(4) are case-split-free):

1. `L₁² + a₁L₁ − a₂ − x_PS − x_S = x_P` — `hthird₁.1` with mathlib's
   `addX` UNFOLDED (it is definitionally `L² + a₁L − a₂ − x₁ − x₂`).
2. `L₂² + a₁L₂ − a₂ − x_QR − x_R = x_P` — `hthird₂.1`.
3. `ℓ₁(P) = 0`, i.e. `y_P = L₁(x_P−x_PS) + y_PS`: from `hthird₂.2`
   (`addY = negY(addX)(line-y at addX) = y_P`) + the 2-torsion
   relation `h2t` (`negY x_P y_P = y_P`) via `negY_negY` — NO
   chord/tangent split needed.
4. `ℓ₂(P) = 0` — same.
5. `ℓ₁(⊖S) = 0`, i.e. `y_PS + L₁(x_S−x_PS) = negY x_S y_S` — needs
   the `slope` case split: chord (`x_PS ≠ x_S`) by `slope_of_X_ne`;
   tangent (`x_PS = x_S` forces `PS = ⊖S` via `hPne`, so
   `y_PS = negY x_S y_S` and the `L₁`-term vanishes).
6. `ℓ₂(⊖R) = 0` — same.
7. The curve equations (`equation_iff` at `S, R, PS, QR, P`) and the
   2-torsion relation as polynomial identities.

Then `hkey` is one `linear_combination`/`field_simp` grind from
(1)-(7) (per the CAS verification it balances exactly; if the direct
ideal-membership search stalls, substitute (5)/(6) to eliminate
`y_PS, y_QR`, (1) to eliminate `x_P`, (3) to eliminate `y_P`, and
grind the two `slope` branches separately against `E(S), E(R)` and
the substituted `E(PS), E(QR)` — this mirrors the verified numeric
computation exactly).

Relations (1), (3), (5) are PROTOTYPED AND COMPILING (2026-07-23,
run_code-verified against this mathlib pin, ready to paste into
`hkey`'s proof — the hypotheses named here are all in scope at the
`hkey` sorry inside `weilValue_two_torsion_config_eq_one`):

```lean
-- (1): rw [Affine.addX] at hthird₁.1
-- (3): from hthird₁ + h2t:
--   rw [Affine.addY, Affine.negAddY, hthird₁.1] at (hthird₁.2);
--   apply congrArg (W.negY xP); rw [W.negY_negY, h2t]
-- (5): by_cases hx : xPS = xS
--   tangent: rw [W.negY_negY] at hPne; yPS ≠ yS;
--     (Y_eq_of_X_eq hPS.left hS.left rfl).resolve_left; rw [hx,
--     sub_self, mul_zero, zero_add, hy']
--   chord: rw [slope_of_X_ne hx]; field_simp [sub_ne_zero.mpr hx]; ring
```

An additional certificate-free route for the final grind: the **norm
factorization** `ℓ₁(T)·ℓ₁(⊖T) = −(x_T−x_PS)(x_T−x_S)(x_T−x_P)` for
any `T` on the curve — provable from (1)+(3)+(5)+`E(T)` alone
coefficient-wise (monic cubic vanishing at `x_P ≠ x_S` (= `hxSP`)
with root sum pinned by (1); Vieta pins the third root to `x_PS`) —
turns each squared line value into a norm times a fiber ratio; this
is the direction to try if the Groebner certificate over
13 variables stays out of reach.

Verified numerically on 1500 random on-curve
configurations over seven prime fields (q = 2003 … 10⁶+3), value
always exactly 1, chord case; AND on 380 degenerate configurations
(`2S = P` tangent-S, `2R = P` tangent-R, both-tangent) across 20
prime fields — so the identity holds uniformly across mathlib
`slope`'s branches and the Lean proof needs only the case split that
`slope`'s definition already dictates. No tame-symbol sign correction
is needed. (Full symbolic reduction in sympy blows up —
Schwartz–Zippel sampling on the constraint variety is the
verification.) Nonvanishing of every divided factor `x_• − x_P` is
exactly the setup's F-avoidances (`x_S, x_PS ∉ F ∋ x_P`;
`x_R, x_QR ∉ F' ≥ F`).

## 4. hleg4 — `∀ x, x ≠ 0 → ∃ y, e x y ≠ 1` (nondegeneracy)

**This is the deepest leg** — the only one whose classical proof
(III.8.1(c): `g = h∘[p]` descent) has no divisor-form shortcut. I looked hard
for one (product-over-E[p] tricks, counting, Frobenius-determinant routes,
Kummer-class arguments): every candidate collapses because (i) over `𝔽̄_q`
every scalar is a p-th power, so Kummer symbols vanish; (ii) all engine
reciprocity statements relate p-th powers of values, and the only
multiplicity-one information is carried by zero-sum comparison elements, which
preserve values but cannot create nontriviality; (iii) `det φ = q` is
downstream of nondegeneracy, not a source for it. The descent must be built.

**(A) Reduction to global nontriviality (cheap; do first).**

```lean
-- first-slot integer powers, by induction from hleg1 (+ hdegval at 0)
have hsmul : ∀ (n : ℕ) x y, e ((n : ℕ) • x) y = e x y ^ n
-- rank-2 basis: nTorsion p ≅ (ZMod p)², from Nat.card = p^2
-- (TorsionCard.card_torsionBy + the finBasis pattern used at line ~8549)
have hbasis : ∃ u v, ∀ w, ∃ a b : ZMod p, w = a • u + b • v
have hglobal : ∃ u v, e u v ≠ 1 := by sorry   -- THE CORE (B)
-- assembly: given x ≠ 0, complete to a basis {x, s}; if e x y = 1 for all y
-- then bilinear expansion (hleg1, hleg2, hsmul) + alternation (hleg3) +
-- skew (1 = e (a+b)(a+b) = e a b * e b a, from hleg1+2+3) force e u v = 1
-- for the hglobal witnesses — contradiction.
```

Note skew in general is FREE here (from hleg1+hleg2+hleg3 via expanding
`e (a+b) (a+b) = 1`); only the self-pair skew of hleg3(a) needed the lattice.

**(B) Global nontriviality — the descent, staged.** Assume `e ≡ 1`; fix
`P ≠ O` p-torsion; contradict `Point.toClass` injectivity. Sub-nodes:

* **L4-1** `T'` with `p•T' = P`: `TorsionCard.smul_surjective` (PROVEN) —
  `(p : 𝔽̄_q) ≠ 0` from `q ≠ p`.
* **L4-2** `E[p]` as an explicit finite object: the p² torsion points
  (`prime_torsion_card`/`card_torsionBy`), as a `Finset`/`Multiset` of affine
  points plus `O` (all `T'⊕κ` and `⊖κ` affine for `κ ∈ E[p]`, since
  `T' ∉ E[p]`).
* **L4-3** general zero-sum principality (extend `htex` of StepR:276 from 4
  points to arbitrary multisets):
  ```lean
  have hmill0 : ∀ D : Multiset (points-with-nonsingularity),
      (D.map toPoint).sum = 0 →
      ∃ a, Ideal.span {a} = (D.map (XYIdeal ...)).prod
  -- Multiset induction through Point.toClass additivity + ClassGroup.mk_eq_one_iff,
  -- descent of the generator as in hextract (6794-6931)
  ```
  Gives `a_g` with `div a_g = (T') + Σ_{κ≠O} [(T'⊕κ) + (⊖κ)]`; the function
  `g := a_g / ∏_{κ≠O} XClass(x_κ)` has `div g = Σ_κ (T'⊕κ) − (κ)`.
* **L4-4** the τ/[p]-composition substrate: instantiate the
  **tautological-point pattern** (`TautologicalPoint.lean`,
  `TautMultiplication.lean` — sorry-free, currently for the universal curve)
  at `Wb` over its own function field `K = Frac(CoordinateRing)`:
  the taut point `(tautX, tautY) ∈ WbK(K)`; `κ ⊕ taut` (addition formulas,
  `add_some_coords` from `TorsionCard`) realizes `h ↦ h∘τ_κ` as evaluation of
  `h` at `κ ⊕ taut`; `p • taut` (division-polynomial formulas,
  `evalEval_φ_eq`, `zsmul_some_aux`) realizes `h ↦ h∘[p]`.
* **L4-5** τ_κ as field automorphisms of `K` fixing constants, giving a
  faithful `E[p]`-action; `mathlib`'s finite Galois correspondence
  (`IntermediateField.fixedField`, `finrank_fixedField_eq_card`) yields
  `[K : Fix(E[p])] = p²`.
* **L4-6** `[p]^*K ⊆ Fix(E[p])` (from `p•(taut ⊕ κ) = p•taut`, i.e. the smul
  homomorphism identities at the taut point) and `[K : [p]^*K] ≤ p²`
  (`tautX` is a root of `Φ_p − ([p]^*x)·ΨSq_p`, degree p², plus the y-quadratic
  bookkeeping) ⟹ `Fix(E[p]) = [p]^*K`.
* **L4-7** the functional equation `f_P∘[p] = c · g^p` — divisor computation at
  the pullback level. Route WITHOUT abstract pullback theory: word-factorize
  `f_P` by `hgenfac` into lines/verticals; the `[p]`-pullback of a vertical
  `x − c` is the explicit polynomial `Φ_p − c·ΨSq_p` whose root multiset is the
  `p²`-fiber with multiplicity one (separability: `separable_preΨ'` machinery,
  `TorsionCardSep`); lines similarly via the `ω`-formula. Then compare spans
  and finish by `hCunits`. This is the largest single brick.
* **L4-8** the translation character: `χ(κ) := (g∘τ_κ)/g` is constant
  (its divisor is `τ_{−κ}(div g) − div g = 0` — `div g` is `E[p]`-translation
  invariant by reindexing — then the equal-span ⟹ constant pattern), and
  `χ : E[p] → μ_p` is a homomorphism (cocycle identity from
  `τ_κ∘τ_λ = τ_{κ+λ}`).
* **L4-9** the dichotomy:
  - if `χ ≡ 1`: `g ∈ Fix(E[p]) = [p]^*K` (L4-5/6), so `g = h∘[p]`; with L4-7
    and injectivity of `[p]^*`: `f_P = c'·h^p`, so `div h = (P⊕S) − (S)`,
    so `I_{PS}` and `I_S` are associated ⟹ `toClass (P⊕S) = toClass S` ⟹
    `P = O` — contradiction. (This branch needs NO pairing input.)
  - if `χ(κ₀) ≠ 1` for some `κ₀`: the **bridge lemma** (discrete Ex. 3.16(c),
    triviality direction): `e(κ₀, x) = χ(κ₀)^{±1}` — contradicting `e ≡ 1`.
    Proof sketch: with `W = p•W'` and `pκ' = κ₀`,
    `f_P(D_{κ₀}) = [g(κ'⊕W')/g(W')]^p` by L4-7 pointwise (constants cancel in
    the balanced ratio), and the level-p² cocycle collapses the p-th power to
    `χ(κ₀)` times coboundaries; `f_{κ₀}(D_P)` is handled symmetrically. THIS
    STEP NEEDS A CAREFUL PAPER DERIVATION FIRST (Silverman Ex. 3.16(c) is
    starred; see also Howe, "The Weil pairing and the Hilbert symbol").

**Effort:** L4-1..3: days. L4-4..6: a solid week+ (but reusable, and makes
leg3 uniform). L4-7: the big one, comparable to `hgenfac` itself. L4-8..9:
days once the rest exists. Overall this is the critical-path kernel of the
whole μ-node; recommend giving `hglobal` its own named module/subtree
immediately (progress-entries item), and NOT blocking legs 1,2,3,5,6 on it.

**STATUS UPDATE (2026-07-24): L4-1..3 PROVEN and assembled; the residual
leaf is `hres` inside `weilValueProp_all_one_torsion_trivial`.** The
`hclass` skeleton now compiles with a single sorry:

* L4-1: `T'` with `(p:ℤ)•T' = x.val` via `TorsionCard.smul_surjective`
  (`(p : 𝔽̄_q) ≠ 0` from `CharP.cast_ne_zero_of_ne_of_prime` + the
  `CharP` transport along `ZMod q → 𝔽̄_q`).
* L4-2: `Fintype (nTorsion p)` from `TorsionCard.card_torsionBy = p²`;
  the divisor multiset is
  `D := univ.map (κ ↦ T' + κ.val) + univ.map (κ ↦ −κ.val)`, and
  `D.sum = 0` WITHOUT needing `Σκ = 0`: the two `Σ κ.val` terms cancel
  against each other, leaving `p²•T' = p•(p•T') = p•x.val = 0`.
* L4-3: NEW MODULE `WeilPairingDescent.lean` —
  `WeilPairing.exists_span_eq_prod_pointIdeal`: any `Multiset W.Point`
  with group-law sum `0` has principal `pointIdeal`-product with
  nonzero generator (`pointIdeal := XYIdeal` at affine points, `⊤` at
  `O`).  Proof is pure class-group algebra (no Dedekind hypothesis, no
  pair-peeling induction): `ClassGroup.mk (∏ pointIdeal' Pᵢ)` equals
  `toMul (Σ toClass Pᵢ) = toMul (toClass ΣPᵢ) = 1`, and
  `ClassGroup.mk_eq_one_of_coe_ideal` extracts an integral nonzero
  generator directly.  Reusable for every future zero-sum divisor
  (Miller words, L4-7 comparisons).
* The residual sorry `hres` (in-proof, fully stated):
  `∀ a ≠ 0, span {a} = (D.map (pointIdeal _)).prod → toClass x.val = 0`
  — the L4-4..9 core, with `hall`/`huniq` in scope.  NOTE the honest
  interface analysis: a hall-free disjunctive form (`principal ∨
  ∃ nontrivial admissible value`) would force rebuilding the `hexval`
  setup-existence machinery at top level; keeping `hall` in scope lets
  the `χ(κ₀) ≠ 1` branch read its admissible setups out of `hall`'s
  own witnesses.  Next actionable stages for `hres`: L4-4 (taut-point
  instantiation of `τ_κ` at `Wb` over `K = Frac(CoordinateRing)`,
  following `TautologicalPoint.lean`) and L4-7's span-level pullback
  factorization; both should live in `WeilPairingDescent.lean` as
  hypothesis-parametrized lemmas (StepR pattern) to keep iteration off
  the 13k-line main file.

**STATUS UPDATE (2026-07-24): L4-1..3 PROVEN and assembled; the sorry
moved DOWN to the in-proof leaf `hres`.** The `hclass` skeleton of
`weilValueProp_all_one_torsion_trivial` now constructs, sorry-free:

* **L4-1** — `T'` with `(p:ℤ)•T' = x.val` via
  `TorsionCard.smul_surjective` (CharP transport + 
  `CharP.cast_ne_zero_of_ne_of_prime` for `(p : 𝔽̄_q) ≠ 0`);
* **L4-2** — `Finite`/`Fintype` on the torsion from
  `TorsionCard.card_torsionBy` (`p² ≠ 0`);
* the zero-sum divisor multiset
  `D := Σ_{κ ∈ E[p]} (T'⊕κ) + (⊖κ)` with `D.sum = 0` — NO `Σκ = 0`
  input needed: the `Σκ.val` contributions of the two halves cancel,
  leaving `p²•T' = p•x.val = 0`;
* **L4-3** — the Miller generator `g ≠ 0` with
  `span {g} = (D.map (pointIdeal _)).prod`, via the NEW module
  `WeilPairingDescent.lean` (`WeilPairing.pointIdeal`,
  `pointIdeal'`, `coe_pointIdeal'`, `mk_pointIdeal'`,
  `coe_prod_pointIdeal'`, `mk_prod_pointIdeal'`,
  `exists_span_eq_prod_pointIdeal` — all PROVEN, Dedekind-free: pure
  `ClassGroup.mk` algebra + `ClassGroup.mk_eq_one_of_coe_ideal`
  extraction; multiset zero-sum principality for ARBITRARY multisets,
  reusable for every future zero-sum-divisor construction).

The single remaining sorry of the μ-node is the in-proof leaf **`hres`**
(WeilPairing.lean, inside `hclass`): `∀ a ≠ 0, span {a} =
(D.map (pointIdeal _)).prod → toClass x.val = 0` — the L4-4..9 core.
Notes for its owner:

* The engine lemmas continue to live top-level in the `MillerEngine`
  section; extend that section as `hres` consumes new facts.
* `nTorsion` requires `DecidableEq 𝔽̄_q` — provided globally by
  `WeilPairing.instDecEqAlgClosureZMod` (WeilPairingStepR.lean),
  re-exported up the import chain; standalone `lean_run_code`
  experiments must re-declare it (and generic-`F` material needs a
  `[DecidableEq F]` variable — mathlib's `Point` group law now demands
  it).
* L4-4 starting brick: the evaluation `F`-algebra hom
  `R = F[W] → K` at any `K`-point of `W.baseChange K`
  (`AdjoinRoot.lift` against the mapped curve polynomial); `τ_κ^*` is
  its instance at `κ ⊕ taut`, with injectivity via composing with
  `τ_{⊖κ}^*` and the group law `(taut ⊖ κ) ⊕ κ = taut` rather than any
  transcendence argument.
* VERIFICATION TOOLING (this worktree): the report-mcp `diagnostics`
  wrapper has a hard 180 s deadline — a full elaboration of
  WeilPairing.lean (~30 min) can NEVER fit; polling re-`didOpen`s and
  spawns fresh from-scratch workers each call.  Use the
  `PipeLsp`-reuse pattern (scratch `wait_diags.py`: import
  `report-mcp.py`, call `lsp.diagnostics(path, timeout=10800)` in a
  background shell) — one long-deadline `waitForDiagnostics` against
  the resident server.  `lake` CLI is permission-banned; the report-mcp
  `build` tool dies at 1800 s of client-side idle (its aborted child is
  killed with it).

**STATUS UPDATE (2026-07-24, third pass): `hres` PROVEN as glue — the
L4-4..9 core is now decomposed into THREE named top-level sorried
leaves.** The τ/[p]-substrate (L4-4 start) is BUILT AND PROVEN in
`WeilPairingDescent.lean`, section `TautSubstrate`, generic over
`(F, W)` (field `F`, plus `[IsAlgClosed F]`/`[Fact p.Prime]` for the
stage statements):

* PROVEN definitional bricks: `constHom` (constants `F → K = Frac F[W]`;
  injective for free — field hom), `tautX`/`tautY`/`taut_equation`/
  `taut_nonsingular` (TautologicalPoint pattern transplanted to `W`
  over its own function field; needs `hΔ : W.Δ ≠ 0`), `curveK`
  (base change to `K`), `tautPoint`, `constPoint` (pointwise base
  change of rational points, via `map_nonsingular`), `pointEval`
  (evaluation `F[W] →+* K'` at a `K'`-point — `AdjoinRoot.lift`
  against `evalRingHom ∘ mapRingHom`; at `κ ⊕ taut` this IS `τ_κ^*`),
  `pointXClass`/`enumVertical` (the vertical denominator
  `∏ (X − x_κ)` of `g = a/∏(X − x_κ)`).
  NOTE a global `noncomputable instance : DecidableEq W.FunctionField`
  (Classical) — mathlib's point group law needs it over `K`.
* `descent_toClass_eq_zero_or_translationChar` — the **L4-9 dichotomy,
  PROVEN glue**: either `toClass P = 0`, or some torsion index carries
  translation-character data `c ≠ 1`, `c^p = 1` with the multiplied-out
  character equation `τ(a)·v̄ = c·ā·τ(v)` in `K` (`v = enumVertical`;
  no field-extension of `pointEval` needed).  Torsion enumeration is
  hypothesis-parametrized (`val : ι → W.Point` injective, torsion,
  surjective-onto-torsion, `card ι = p²`) so the statement lives
  generically; the main file instantiates `val := Subtype.val` on
  `nTorsion p` (the defeq `E⁄F̄ ≡ E` crossings all unify).
* The THREE residual sorried leaves (each with a full proof-plan
  docstring):
  1. `WeilPairing.exists_translationChar` (WeilPairingDescent.lean)
     — L4-8: χ(κ₀) is a constant `p`-th root of unity + evaluation
     nonvanishing at the generic translate; needs div-g translation
     invariance, units-are-constants, and the L4-7 pullback
     factorization for `c^p = 1`.
  2. `WeilPairing.toClass_eq_zero_of_translationChar_trivial`
     (WeilPairingDescent.lean) — L4-5/6/7 + L4-9 first branch: trivial
     character ⟹ `g = h∘[p]` through `Fix E[p] = [p]^*K` ⟹
     `div h = (P) − (O)` ⟹ class vanishes.
  3. `WeilPairing.weilValue_of_translationChar` (WeilPairing.lean,
     right before the descent-core theorem) — the bridge (Silverman
     Ex. 3.16(c)): nontrivial character data ⟹ a nontrivial
     admissible Weil value `∃ v w z, weilValueProp ∧ z ≠ 1`; consumed
     in `hres` against `hall`/`huniq`.
* CAUTION for successors: the substrate bricks the stage proofs will
  want next (`pointEval_mk`, `pointEval` at `taut` = `algebraMap`,
  `tautX ∉ constants`, `constPoint ⊕ taut ≠ 0`, τ-functoriality/
  injectivity via `τ_{⊖κ}`) were deliberately NOT added — they would
  be free-floating until a consuming skeleton exists.  Open the stage
  lemma's proof skeleton first, then add them to `TautSubstrate`.
* Verification note: the current report-mcp `diagnostics` accepts
  `timeout_seconds` (default 1800) and is retry-safe on unchanged
  content; a from-line-4200 re-elaboration of WeilPairing.lean runs
  ~3-5 min (the 30-min figure is a cold full-file pass).

**STATUS UPDATE (2026-07-23).** The reduction (A) is fully in place and
sorry-free inside the μ-theorem (`hleg4` = `pairing_trivial_of_radical`
+ the rank-2 computation + `hglobal`); `hglobal` itself is discharged
in-proof by `by_contra` + `TorsionCard.card_torsionBy` (`p² > 1`)
against the NEW top-level sorry node
`weilValueProp_all_one_torsion_trivial` (WeilPairing.lean, right after
`end FrobeniusTransport`): hypotheses `huniq` (uniqueness of admissible
values, instantiated with `huniqval`) and
`hall : ∀ v w, weilValueProp q Wbar p v w 1`, conclusion `x = 0` for
every p-torsion `x`. Its skeleton reduces through
`Point.toClass_eq_zero` to the single sorried leaf
`hclass : Point.toClass x.val = 0` — the L4-9 landing point for BOTH
dichotomy branches (`χ ≡ 1` ⟹ principality; `χ(κ₀) ≠ 1` ⟹ `hall`
contradiction ⟹ anything). The L4-1..8 machinery goes inside
`hclass`'s proof; being a top-level context (no in-proof engine haves),
the needed engine facts must be re-derived as top-level lemmas or
extracted from the μ-proof — the `MillerEngine` section
(`coordRing_isUnit_constant`, `coordRing_line_span`,
`coordRing_evalEval_XClass`, extracted 2026-07-23, instantiating the
μ-proof's `hCunits`/`hline`/`hevvert`) is the start of that extraction;
continue it (e.g. `hgen`, `hpoints`, `hker`, `hoffdiv`) as `hclass`'s
proof consumes them.

## 5. hleg5 — `∀ x y, (e x y) ^ p = 1`

Pure consequence of hleg1 (in scope by position) + `hdegval`:

```lean
have hsmul : ∀ (n : ℕ) y, e (n • x) y = e x y ^ n := by
  intro n; induction n with
  | zero => simpa using hdegval 0 y (Or.inl rfl)   -- (0 : nTorsion).val = 0
  | succ n ih => rw [succ_nsmul, hleg1, ih, pow_succ]
-- p • x = 0 : Subtype.ext; (p • x).val = (p:ℤ) • x.val = 0 by
-- Submodule.mem_torsionBy_iff (the hvp pattern at 7748-7752), natCast_zsmul
calc (e x y) ^ p = e (p • x) y := (hsmul p y).symm
  _ = e 0 y := by rw [hpx0]
  _ = 1 := hdegval 0 y (Or.inl rfl)
```

~30-50 lines. (If preferred, `p•x = 0` also follows from the `ZMod p`-module
structure: `(p : ZMod p) = 0`.)

Note the alternative "one hstar instance" proof (Weil reciprocity between the
two Miller pairs of a single setup) is TRUE but strictly more work — skip it.

## 6. hleg6 — Frobenius naturality

`e (φ x) (φ y) = Units.map (frobAlgHom q).toRingHom (e x y)`,
`φ := frobeniusTorsionEnd q Wbar p`. Silverman III.8.1(d): apply σ to
everything. In our framework: **transport an `IsWeilValue` witness through the
q-power Frobenius** and close with `heuniq`. Mechanical; no new mathematics.

New objects/bricks:

```lean
-- the coordinate-ring Frobenius transport: coefficients ↦ c^q, X ↦ X, Y ↦ Y.
-- Wb.toAffine.polynomial has coefficients fixed by frobAlgHom (they are
-- algebraMap-images from ZMod q; frobAlgHom.commutes'), so the map descends:
let σA : Wb.toAffine.CoordinateRing →+* Wb.toAffine.CoordinateRing :=
  AdjoinRoot.lift
    ((AdjoinRoot.of Wb.toAffine.polynomial).comp
      (Polynomial.mapRingHom (frobAlgHom q).toRingHom))
    (AdjoinRoot.root Wb.toAffine.polynomial)
    (by ...)  -- mapped polynomial = the polynomial itself, coefficient check
have hσA_X : ∀ c, σA (CoordinateRing.XClass Wb.toAffine c) =
    CoordinateRing.XClass Wb.toAffine (frobAlgHom q c)
have hσA_ev : ∀ x y (hE : Wb.toAffine.Equation x y) f,
    frobAlgHom q (AdjoinRoot.evalEval hE f) =
    AdjoinRoot.evalEval (hEq : Wb.toAffine.Equation (frobAlgHom q x) (frobAlgHom q y)) (σA f)
    -- both sides are ring homs in f; AdjoinRoot.lift-uniqueness / induction on
    -- the {1, Y} decomposition (hdecomp)
have hσA_span : ∀ x y, Ideal.map σA (CoordinateRing.XYIdeal Wb.toAffine x (Polynomial.C y)) =
    CoordinateRing.XYIdeal Wb.toAffine (frobAlgHom q x) (Polynomial.C (frobAlgHom q y))
    -- Ideal.map of span of the two generators; hσA_X + the YClass analogue
```

Witness transport `hwit : IsWeilValue v w z → IsWeilValue (φ v) (φ w) (Units.map … z)`:

* points: `(φ v).val = Point.map (frobAlgHom q) v.val` unfolds
  (`frobeniusTorsionEnd` def at 129-137, `endRestrict`,
  `Affine.Point.map_some`) to `some (x^q) (y^q) h'`; equation/nonsingularity
  transport by applying the field hom to `equation_iff`/`nonsingular_iff`
  (or the existing `Point.map` machinery);
* subfields: `F ↦ F.map (frobAlgHom q).toRingHom` (a `Subfield.map`);
  finiteness: image of finite; memberships: `mem_map` direct; NON-memberships
  (`xS ∉ F` etc.): injectivity of a field hom;
  inequalities (`xQR ≠ xS`): injectivity again;
* group equations (`PS = P + S` etc.): apply the point-map homomorphism
  (`Point.map` is additive — the repo already uses this; cf. line 173);
* spans: `Ideal.map σA` of `haP` via `Ideal.map_span`, `map_mul`, `map_pow`,
  `hσA_span` — note `Ideal.map σA (span {aP}) = span {σA aP}`;
  negY transport: `frobAlgHom (negY x y) = negY (x^q) (y^q)` (ring identity);
* the value equation and `A ≠ 0`: apply `frobAlgHom` (a ring hom) to both,
  rewrite by `hσA_ev`, `map_pow`, injectivity for the nonvanishing.

Then `hleg6 := fun x y => heuniq _ _ _ (hwit … (hespec x y))` — plus the
`Units.map`-value bookkeeping (`Units.val_map`... the candidate `z`-image is
`Units.map (frobAlgHom q).toRingHom.toMonoidHom z`, matching the goal
spelling at 8103-8105).

**Effort:** ~400-600 lines, low risk. Independent of all other legs — a good
parallel work packet.

## 7. Suggested order / parallelization

1. `hdegval` + **hleg5** skeleton (consume hleg1 even while it is sorried) —
   hours.
2. **hleg6** (independent) — one worker.
3. **hleg1**, then **hleg2** (template reuse; consider a new extracted module
   per the StepR pattern; engine facts as hypothesis parameters since
   `hCunits` etc. are in-proof haves) — one worker each.
4. **hleg3**: odd-p branch after the `K(n)` lattice brick lands (coordinate
   with the `G''`-sorry worker — same machinery); `p = 2` as a named sorried
   sub-have, attacked by CAS-verified explicit computation (c-i) or deferred
   to the leg-4 machinery (c-ii).
5. **hleg4**: write the reduction (A) immediately with `hglobal` as the single
   named sorry; open the L4-1..9 subtree as its own module cluster. This is
   the long pole; L4-3 (`hmill0`), L4-4 (taut instantiation at `Wb`) are
   immediately actionable.

Dependency summary: hleg5 ← hleg1; hleg3(odd) ← lattice + hleg1;
hleg4(reduction) ← hleg1,2,3; hleg4(core), hleg3(p=2 uniform option) ←
taut/τ/[p] machinery; hleg6 independent.
