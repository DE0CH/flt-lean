## A DOCSTRING'S PRESCRIBED ROUTE CAN NAME A STEP THAT THE RIGHT PRESENTATION DELETES

(2026-07-31, `ker_multIdeal_le_span_idealTensorComparison`, [Stacks 10.99.12/13].) The leaf's
docstring named the dimension shift `ker(↥I ⊗_C D → D) ≅ (K ∩ IF)/IK` as the thing to state
first, calling it "the real cost of this leaf" — and it would have been, because it has to be
applied over two rings and the two copies then have to be compared. It was never needed. On
the **tautological** free presentation `F = (D →₀ C)` — the free module on the underlying SET
— the shift degenerates:

* `multIdeal I F` is INJECTIVE (`Finsupp` is free, hence flat), so the tensors themselves are
  a faithful representation and conclusions transport along it; and
* its image is cut out COEFFICIENTWISE, so `K ∩ IF` needs no separate description.

No quotient is ever formed and no comparison is ever checked. ~300 lines instead of a module.

**The generalisable move: before building the machine a route asks for, try the most concrete
model of the object the route quantifies over.** A route is written by someone reasoning
abstractly ("take a free presentation"); an abstract presentation forces you to construct
every identification by hand, while a *specific* one often makes several of them `rfl` or
coefficientwise. Same reason `ker πj = span_{Cj}(ι '' ker π)` was cheaper proved from the
universal property of `⊗` than through mathlib's `lTensor_exact`: the latter first demands
identifying `(D →₀ Cj)` with `Cj ⊗[Ci] (D →₀ Ci)`, and that transport costs more than the
whole proof.

Corollary for cutting: a leaf's stated route is a *hypothesis about cost*, not a
specification. Re-cost it against a concrete model before you accept its first bullet.

**And an unknown-identifier error on a mathlib name that visibly exists in the source is a
RENAME, not a missing import.** `Basis` is `Module.Basis` at this pin (`Basis.ofVectorSpace`
→ `Module.Basis.ofVectorSpace`), and the error was `unknown namespace 'Basis'` even with the
right file imported. Check `grep -n "^namespace" <the mathlib file>` before hunting imports or
suspecting a partial `.lake`. (A genuinely missing olean gives `object file ... does not
exist`, which looks nothing like this.)

