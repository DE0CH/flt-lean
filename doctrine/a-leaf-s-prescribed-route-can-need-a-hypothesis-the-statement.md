## A LEAF'S PRESCRIBED ROUTE CAN NEED A HYPOTHESIS THE STATEMENT DOES NOT HAVE — DIFF IT AGAINST THE PROVEN TWIN
(2026-07-31, `flt-lean-372`, closing `isUnramifiedAtInfinitePlaces_sup` in
`NumberField/UnramifiedClassFieldExistence.lean`.)
The doctrine already says a leaf's route is a hypothesis about cost. There is a sharper
failure: **the route can be IMPOSSIBLE at the stated signature, because it was transcribed
from a sibling that carries more hypotheses.** That leaf's docstring prescribed "the
ARCHIMEDEAN instance of `forall_mem_sup_of_fixed`" — lift complex conjugation at a place of
`L₁ ⬝ L₂` to `Gal(K̄/K)` and restrict it to each factor. The statement carries no
`IsGalois K Lᵢ`, and `AlgEquiv.restrictNormalHom Lᵢ` needs `Normal K Lᵢ`, so no restriction
exists and the route cannot be started at all. A prover who trusts it spends the run trying
to manufacture normality.
**The tell was one module downstream, and it is mechanical.** `HilbertClassFieldNormal.lean`
proves the SAME theorem for the ambient `AlgebraicClosure ℚ`
(`isUnramifiedAtInfinitePlaces_sup_algClosRat`, and `isUnramifiedAt_sup` for the finite
primes) — and its signature carries `[IsGalois K L₁] [IsGalois K L₂]`. So:
> **When a leaf has a PROVEN twin in another module, diff the two BINDER LISTS before
> transcribing the proof.** Extra hypotheses downstream mean the downstream proof does not
> transcribe, and the upstream statement needs a different — usually more elementary —
> argument. Equal binder lists mean it is a copy-paste.
Here the elementary argument is the EMBEDDING one and it needs nothing: `conj ∘ φ` and `φ`
agree on each `Lᵢ` (that is what unramifiedness at the infinite places says once the place
below is real), hence on the compositum, hence `w` is real. It also generalises the twin
rather than duplicating it.
**The reusable brick, and it is the ring-hom companion of the fixed-field trick this
development already uses everywhere:** two `K`-algebra maps out of an ALGEBRAIC extension
that agree on `L₁` and on `L₂` agree on `L₁ ⊔ L₂`, because `AlgHom.equalizer f g` is a
`K`-subalgebra and over an algebraic extension every `K`-subalgebra is a field
(`Algebra.IsAlgebraic.toIntermediateField`), so it is an intermediate field and `sup_le`
applies. Four lines, no finiteness, no normality. Whenever a compositum obligation is about
maps OUT of the field rather than automorphisms OF it, that is the lemma; reach for it
before `IntermediateField.fixingSubgroup_sup`.
Two smaller notes from the same proof. `IsAlgClosed.lift` is what moves a `w.embedding`
defined on `↥(L₁ ⊔ L₂)` up to `K̄ →ₐ[K] ℂ`, which is where the lattice lives — the algebra
instances it needs are the mathlib idiom `letI := (φ.comp (algebraMap K ↥E)).toAlgebra;
letI := φ.toAlgebra; IsScalarTower.of_algebraMap_eq' rfl`, copied from
`InfinitePlace.isUnramified_mk_iff_forall_isConj`. And **state such a lemma at a VARIABLE
target field, not at `ℂ`**: the consumer supplies `Algebra K ℂ` as a local instance built
from the very embedding it is analysing (there is no canonical one), and a lemma stated at
`ℂ` would have to be applied against that local instance.
**And when a docstring's route turns out to be unavailable, DELETE it and write the route
taken.** A route that cannot be started is worse than no route, because it reads as
permission to stop looking.
