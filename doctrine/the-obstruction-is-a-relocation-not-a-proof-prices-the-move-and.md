## "THE OBSTRUCTION IS A RELOCATION, NOT A PROOF" PRICES THE MOVE AND NOT THE RESIDUE
(2026-07-31, `flt-lean-100`, on `natCard_ker_degreeFormEnd_abs` in
`EllipticCurve/HasseBound.lean`.) A mature leaf here often carries a verdict of the form
*"the thing you need is PROVEN, downstream; the obstruction is architectural, so the repair
is a RELOCATION and not a proof."* That shape is usually TRUE and it is the most
under-audited sentence in the docstring, because it reads as a cost estimate that has
already been done. Two independent failures, both live in this one leaf.
**1. THE FILE IT NAMES HAS USUALLY MOVED TOO.** Two docstrings in `HasseBound.lean` and the
task prompt built from them all placed `det_frobeniusTorsionEnd_of_coprime` in
`FreyCurve/MazurTorsion.lean`. It had been hoisted to `FreyCurve/IsogenySignature.lean` in
an earlier release, and `grep` in `MazurTorsion.lean` returns **nothing** — which reads as
"the declaration was deleted or renamed", i.e. as the phantom-target shape this file spends
pages on. It is not: a recorded LOCATION is a frontier fact and decays at the same rate as
a leaf count. **Grep the tree for the declaration NAME, never navigate to the recorded
file** — one `grep -rn '<name>' --include=*.lean Fermat/` settles it, and the same command
also tells you whether the block has since been split.
**2. THE VERDICT PRICES THE MOVE AND IS SILENT ABOUT WHAT REMAINS AFTER IT.** Here the
relocation was real, correct, and did not close the leaf. The audits disposed of the whole
`ℓ`-adic half with the phrase *"yields `#ker ψ = |d|` for `q ∤ d` via Smith normal form on
`E[d²]`"*, and that phrase is doing the work of a theorem the tree does not have: converting
`det f = d` over `ZMod N` into a KERNEL CARDINALITY. Mathlib has no Smith normal form over
`ZMod N` (it is not a PID), and a determinant there sees a kernel only through the elementary
divisors. **So before accepting "it is only a relocation", write out the statement that
consumes the relocated theorem and check it is a theorem you HAVE rather than a technique you
can name.** The tell is a route note that ends in a classical phrase — "by Smith normal
form", "by Riemann–Roch", "by dévissage", "by Nakayama" — with no declaration cited.
**The residue, written out, is worth more than the verdict.** Recording it turned a leaf whose
audits said "relocation" into one that names a bounded, elliptic-curve-free obligation:
> `M` free of rank two over `ZMod N`, `f : M →ₗ M` with `det f = (d : ZMod N)`,
> `N = d.natAbs ^ 2`, `d ≠ 0`  ⟹  `Nat.card (ker f) ∣ d.natAbs`.
and — this is the part the audits' phrase hides — **its proof does not run over `ZMod N` at
all.** Present `M` as `ℤ² ⧸ Nℤ²`, pull `ker f` back to a lattice `L ⊆ ℤ²`, and take the
adapted basis there, where mathlib DOES have it (`Submodule.smithNormalForm`, ℤ being a PID).
`L = ⟨α u₁, α' u₂⟩` with `α, α' ∣ N`; put `kᵢ = N/α⁽ⁱ⁾`, so `#ker f = k₁k₂` and both `kᵢ ∣ N`;
the matrix of `f` in that basis has its `i`-th column divisible by `kᵢ`, so `d ≡ k₁k₂·s (mod N)`;
hence every common divisor of `k₁k₂` and `N` divides `d`, so `kᵢ ∣ d`, so `k₁k₂ ∣ d² = N`, so
`k₁k₂ ∣ d`. **`N = d²` rather than `N = |d|` is the whole trick** — at `N = |d|` the determinant
is `≡ 0` and carries no information.
**Generalisable: when a statement over `ZMod N` needs elementary divisors, do not look for
Smith over `ZMod N`. Pull back to `ℤ`, where it is one mathlib lemma, and push the answer
forward as a DIVISIBILITY** — divisibility survives the pullback where an inequality would
need the index computation done twice.
**And a pure move must publish its receipt.** Sorted-line-multiset equality (already recorded
above) proves nothing was edited; what it does NOT prove is that the frontier held. Quote the
comment-stripped `sorry` token count on BOTH files — here `IsogenySignature.lean` `6 → 5` and
`WeilPairingComposite.lean` `0 → 1` — because a relocation that carries a leaf across a file
boundary is otherwise indistinguishable, to every scan, from one closure plus one disclosure.

