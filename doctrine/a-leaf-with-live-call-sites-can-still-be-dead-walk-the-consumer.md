## A LEAF WITH LIVE CALL SITES CAN STILL BE DEAD — WALK THE CONSUMER CHAIN TO THE ROOT, NOT ONE HOP

(2026-08-01, `flt-lean-256`, `Threeadic.lean` again, and it is the sequel to the section
above.) The standing check — *"grep the tree for your target's consumers before proving
anything; hits that are docstrings only mean the leaf is DEAD"* — **passes** on a target
whose entire cluster is orphaned, and passing is exactly what makes it dangerous.

`exists_uniform_pow_localInertia_smul_connected_of_threeTorsion_trivial` had **two**
comment-stripped CODE call sites, both real, both inside PROVEN theorems. One hop up: a
proven consumer. Two hops up: another. Three hops up: **nothing at all, on `main` or on
`merger`.** The cluster's own consumer, `exists_ordinary_line_of_flat_hopf_package`, had
gone with the refuted cone two releases earlier and occurs nowhere in the tree.

So the question is not *"does something consume this"* but **"does the consumer chain
reach `fermat_last_theorem`"**, and the two answers differ by however many proven
theorems sit in the orphaned island — here three, i.e. the one-hop check was wrong twice
over. Measured: the target's upward closure was **3 declarations, depth 2, root not
reached**, while the two surviving leaves 700 lines below had closures of **20 487
declarations** reaching the root. That is not a judgement call, and it is ten lines:

    python3 tools/merge/deadleaf.py          # added with this note; --root DIR to aim it

**Run it on your target before your first edit**, not after. It costs seconds against a
file whose elaboration is minutes, and a dead leaf is the one outcome where every further
hour is wasted by construction.

**AND READ ITS OUTPUT THE WAY THE SCRIPT SAYS, because the class is common and only a
few members of it are garbage.** It splits the out-of-cone leaves into PENDING (the
closure reaches a SORRIED consumer — ordinary bottom-up work, leave it) and CANDIDATE
(every maximal element is PROVEN and consumed by nothing). On 2026-08-01 that was 37 and
47. **A CANDIDATE IS NOT A DELETION ORDER**: most are proven top-level package theorems
whose consumer has not been written yet, and deleting those is precisely the `dc6836b9`
failure this section is a sequel to. What promoted mine from candidate to *dead* was one
further, non-mechanical check — the island's intended consumer was verifiably ABSENT,
deleted with a refuted cone in a named commit, occurring nowhere on `main` or `merger`.
Look for that evidence; the closure alone does not supply it.

### HOW THESE ISLANDS ARE MADE: a merge that preserves a PROOF can orphan it

Worth knowing because the reasoning looks careful at the time and is recorded in the
commit message. Two branches each computed a deletion of one refuted cone. `flt-lean-172`
deleted the cluster's middle theorem as free-floating; `flt-lean-293` had concurrently
PROVEN that same theorem over a smaller leaf. The merge worker took 172's deletion but
declined *that one item*, explicitly, so as not to "throw away 293's proof" — and thereby
preserved a proof of a theorem whose consumer **the same commit deleted**.

**"This branch proved it" is not a reason to keep a declaration; "something consumes it"
is.** When two branches disagree about deleting a declaration, resolve it by re-deriving
REACHABILITY against the merged tree, never by crediting either branch's work. The
failure is invisible afterwards: the island compiles, emits an honest
`declaration uses 'sorry'` warning, passes `own.py` and `leafstat.py`, and draws
dispatches for ever.

### Two mechanical notes from the same run

* **The sorry warning is spelled with BACKTICKS.** Lean emits ``declaration uses `sorry` ``;
  a grep for `declaration uses 'sorry'` returns **zero** on a file with three of them, and
  zero warnings alongside `EXIT=0` reads exactly like a clean build. This file quotes the
  message with straight quotes throughout — match on `declaration uses` alone.
* **A deletion is verified by a SHIFT-INVARIANT differential, and the shift is the
  receipt.** Elaborate the pre-edit file (from `git show HEAD:<path>`, placed at a real
  module path) and the post-edit file against the same oleans, then require every
  surviving diagnostic to move by ONE constant offset. Here all five moved by exactly
  `−2195` and the only difference was the target's own warning — which simultaneously
  proves the deletion is complete and that the fixpoint was right, since a still-needed
  declaration would have surfaced as `unknown identifier`.

