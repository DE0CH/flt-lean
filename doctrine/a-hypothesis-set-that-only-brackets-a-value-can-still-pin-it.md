## A HYPOTHESIS SET THAT ONLY *BRACKETS* A VALUE CAN STILL PIN IT — MULTIPLY AND TAKE A LIMIT

(2026-07-31, `Interface.lean`'s Stickelberger cluster.) `exists_valuationExtension_of_liesOver`
hands its consumers a valuation `v` carrying exactly ONE arithmetic axiom,
`z ∈ q^N ↔ (ℓ−1)·N ≤ v z` on `𝓞 CF`. The reflection half of Stickelberger needs
`v(ℓ) = ℓ − 1` on the nose. Reading the axiom off at `N = 1` gives only `≥`, and the
axiom genuinely does not determine `v(ℓ)` pointwise: it brackets it inside
`[(ℓ−1)e, (ℓ−1)(e+1))` where `e = v_q(ℓ)`, and that is ALL a single instance of it says.

The obvious conclusions — "this leaf is under-specified", "the producer must be strengthened
to export `v(ℓ)`", "we need ramification theory here" — are all wrong, and each would have
cost a signature change across a producer, a leaf and a consumer.

**What closes it is that the axiom can be instantiated INFINITELY OFTEN and `v` is
multiplicative.** `v(ℓ^k) = k·v(ℓ)` against `ℓ^k ∉ q^{k+1}` gives `k·v(ℓ) < (ℓ−1)(k+1)` for
EVERY `k`, i.e. `v(ℓ) < (ℓ−1)(1 + 1/k)`, and the `k → ∞` limit collapses the bracket to a
point. Ramification theory enters only to supply `ℓ ∉ q²` — one instance, at `k = 1`; the
rest is Archimedes.

**The general shape, and it is worth checking before ANY "the hypotheses are too weak"
verdict:** when a hypothesis bounds a quantity within an interval rather than fixing it, ask
whether some structure map (multiplicativity, additivity, a group action) lets you apply the
same hypothesis to `x^k`, `k·x` or `gx` and divide back. A bracket of fixed WIDTH around a
quantity that scales linearly is a bracket of width `→ 0` around the quantity itself. The
failure mode this avoids is real and expensive: strengthening a producer's conclusion to
export something its existing conclusion already implies.

### Three Lean traps measured in the same session

* **`Ideal.Quotient.field` is a `def`, not an instance.** Supplying `[q.IsMaximal]` does NOT
  make `Field (R ⧸ q)` synthesisable; mathlib itself writes `attribute [local instance]
  Ideal.Quotient.field`, and in a proof the idiom is
  `letI : Field (R ⧸ q) := Ideal.Quotient.field q` (`letI`, not `haveI` — see the existing
  rule about `haveI` making a `Field` opaque). The confusing symptom is not the honest
  `failed to synthesize Field (R ⧸ q)`; it is a **`(deterministic) timeout at whnf`** inside a
  lemma whose statement carries `[Field R]` — the elaborator burns its budget trying to see
  the `CommRing` through a structure it cannot find.
* **`WithTop ℚ` is not a semiring, so `nsmul_eq_mul` does not fire in it** — and `push_cast`
  will cheerfully push a coercion INWARDS and strand the goal as `n • x = ↑n * x` *at the
  `WithTop` level*, where both `rw [nsmul_eq_mul]` ("pattern not found") and
  `simp [nsmul_eq_mul]` ("no progress") fail on a goal that visibly matches. Descend with
  `congr 1` to the `ℚ` level FIRST, then `push_cast; ring`. The lesson generalises to any
  `WithTop`/`WithBot`/tropical target: get out of it before doing ring arithmetic.
* **Prefer `Nat.card` lemmas to `Fintype.card` ones whenever an instance was introduced by
  hand.** `Fintype.card_units` failed to rewrite a goal about `Fintype.card (R ⧸ q)ˣ` because
  the ambient instance came from `haveI := Fintype.ofFinite _` rather than from
  `instFintypeUnits`; `Nat.card_units [GroupWithZero α] : Nat.card αˣ = Nat.card α - 1` has no
  instance argument to mismatch and closed it immediately. Two `Fintype` instances on one type
  are propositionally equal and syntactically different, which is exactly the gap `rw` cannot
  cross.

**ADOPT THE RIVAL'S SPLIT POINT — copy its statement VERBATIM and contribute only the body**
(2026-07-31, flt-lean-290). All three leaves of one task were already proven on `merger` when the
worker started; the queue had been written against a `main` that was 480 commits behind. Two of the
three were straight duplicates and were dropped. The third was the interesting case, and it
generalises:

`merger` had split `exists_mem_hilbertInertiaOutsideSubgroups_resSubgroup_eq_zero` into a cocycle
half (`…_eval₁_eq_zero`, left `sorry`) plus a one-line cohomological consumer. This worktree had
independently proven the WHOLE of that cocycle half except a uniform Hermite–Minkowski bound — i.e.
its work was exactly the body of the rival's open leaf. Neither "decline mine" nor "decline theirs"
was right: the reconciliation is to **take the rival's name and signature as authoritative, paste
your proof into it, and make your copy of the shared consumer byte-identical to theirs.** The merge
then has nothing to choose — one side is a pure insertion, the other is unchanged.

The general rule, and it is cheaper than it sounds: when you find the node already cut elsewhere,
diff the two cuts and ask *which half of theirs do I already have*. A statement copied verbatim from
the incumbent costs nothing and converts a guaranteed conflict into a no-op; a statement you prefer
for aesthetic reasons costs the merger a decision it has no author to make. Say in the docstring
that the signature is inherited and why, so the next reader does not "fix" it back.

Corollary for the DROPPED halves: a duplicate proof does not merely lose, it *poisons*. This
worktree's rival proof of `cyclotomicCharacter_map_map_eq_one_of_mem_localInertiaGroup` came with
five new general-`K` helper declarations sitting in a NON-conflicting region. Resolving the theorem
to the incumbent's body would have left those five behind as free-floating declarations — class-7's
interface split, in the shape of dead code rather than broken code. Revert the whole payload
(`git apply -R` of your own commit's hunks), not just the colliding declaration.

