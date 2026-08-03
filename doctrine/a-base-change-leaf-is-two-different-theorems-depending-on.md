## A "BASE CHANGE" LEAF IS TWO DIFFERENT THEOREMS DEPENDING ON WHETHER THE EXTENSION IS ALGEBRAIC
(2026-07-31, `flt-lean-325`, closing the base-change half of
`isRegularRing_tensorAlgebraicClosure_of_isInvariant` in `ModularCurve/X1.lean`.)
That leaf's docstring listed, under **WHAT IS ACTUALLY MISSING FROM THE PIN (re-checked
2026-07-30)**, three general theorems, and the second was
> **Krull dimension is invariant under base field extension** for finite-type algebras.
> Grepped: `Mathlib/RingTheory/KrullDimension/` has the polynomial, PID, local-ring, field
> and module lemmas and nothing about `⊗`.
The grep is right, the general theorem is genuinely missing, and it is genuinely hard — it
is dimension theory of finite-type algebras. **And it is not what the leaf needs.** The
extension in the leaf is `k̄/k`, which is **ALGEBRAIC**, and at an algebraic extension the
base change is **INTEGRAL**:
* `Algebra.IsIntegral.tensorProduct` (`Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean`)
  is an INSTANCE — `[Algebra.IsIntegral R B] → Algebra.IsIntegral A (A ⊗[R] B)`;
* `Algebra.TensorProduct.includeLeft_injective` (`Mathlib/RingTheory/Flat/Basic.lean`)
  gives `S ↪ S ⊗[k] K` from `Module.Flat k S`, free over a field;
* so this tree's `ringKrullDim_eq_of_isIntegral_of_injective`
  (`Fermat/FLT/Mathlib/AlgebraicGeometry/SmoothConnectedCriteria.lean`) applies verbatim
  and `ringKrullDim (S ⊗[k] K) = ringKrullDim S` is **three lines**.
The rule generalises past dimension: **before costing "property `P` is preserved by base
change", ask whether the extension in your statement is ALGEBRAIC**, and if it is, look for
the integral-extension version of `P` instead of the flat/geometric one. Algebraic base
change is a completely different regime from a general one, and a docstring that says
"base field extension" has usually not made the distinction — the author was thinking of
the general theorem because that is the one with a name.
### THE ORIENTATION TRAP: `K ⊗[k] S` vs `S ⊗[k] K`, and which properties cross for free
The same repair hit a Lean obstacle that will recur, because this development's two
relevant tools point in OPPOSITE directions:
* mathlib's `Algebra.Smooth.baseChange` is an instance for `Algebra.Smooth B (B ⊗[R] A)` —
  the extension on the LEFT;
* this tree's `Fermat.InvariantBaseChange` (`Fermat/FLT/Mathlib/RingTheory/InvariantBaseChange.lean`)
  states `isInvariant_tensor`, `smulCommClass_tensor`, `injective_bcInclusion` for
  `A ⊗[k] K` — the extension on the RIGHT.
The bridge is **`Algebra.TensorProduct.commRight R S A : S ⊗[R] A ≃ₐ[S] A ⊗[R] S`**
(`Mathlib/RingTheory/TensorProduct/Maps.lean`), an equivalence over the RIGHT factor's
algebra structure `Algebra.TensorProduct.rightAlgebra`, which is an `abbrev` and must be
introduced with `attribute [local instance]` or `letI`. With it,
`Algebra.Smooth.of_equiv` moves smoothness across in one line.
**And most of what you need does not have to cross as an algebra fact at all.**
`IsRegularRing`, `IsReduced`, `IsNoetherianRing`, `IsIntegrallyClosed` and `ringKrullDim`
are BARE RING properties, so a plain `RingEquiv` transports them —
`IsRegularRing.of_ringEquiv`, `IsIntegrallyClosed.of_equiv`, `isNoetherianRing_of_ringEquiv`
— and `Algebra.TensorProduct.comm k R K |>.toRingEquiv` is that equiv. So the disciplined
shape is: **do the whole proof in whichever orientation the hard machinery lives in, and
convert the CONCLUSION once at the end**; only genuinely algebra-level hypotheses
(`Algebra.Smooth` here) need `commRight`. Trying to normalise the orientation up front
costs an `IsScalarTower` diamond for nothing.
### AND THE INVENTORY WAS WRONG ABOUT THE THIRD ITEM TOO — in the direction this file keeps recording
The same list's third item was *"invariants commute with flat base change … Grepped:
`Mathlib/RingTheory/Invariant/` contains no `tensor`, no `baseChange`, no `flat`."* True of
mathlib and **false of this tree**: `Fermat/FLT/Mathlib/RingTheory/InvariantBaseChange.lean`
proves exactly it, `isInvariant_tensor`, with the `MulSemiringAction` plumbing and the
injectivity, and had done for some time. It was written for the SCHEME-level GIT statement,
so its module docstring talks about pullbacks and categorical quotients and nothing in it
matches a grep for the ring-level phrasing.
This is the standing rule ([[flt-inventory-audits-understate-what-exists]], and CLAUDE.md's
own "NOT IN MATHLIB, NOT IN `~/cs/FLT` — CHECK YOUR OWN IMPORT LIST FIRST") firing for at
least the fourth time, so it is worth stating in its sharpest form: **`Fermat/FLT/Mathlib/**`
is where every agent's general-purpose commutative algebra lands, it is small, and an
absence claim that has not grepped it is worthless.** Grep it by CONCEPT — the class name,
the mathlib lemma you would need — never by the phrasing your own leaf uses, because the
file that has your theorem was written for somebody else's consumer.
Net effect on this leaf: of three "missing general theorems", one was already in the tree,
one was not needed at all, and one — *smooth over a field ⇒ regular, hence normal* — is
real and survives, bundled with the genuine difficulty (nothing here is a DOMAIN, and every
relevant mathlib and in-tree lemma about normality carries `[IsDomain]`).
