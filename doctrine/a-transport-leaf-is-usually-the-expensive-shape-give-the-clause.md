## A TRANSPORT LEAF IS USUALLY THE EXPENSIVE SHAPE — GIVE THE CLAUSE TO THE LEAF THAT BUILDS THE OBJECT
(2026-08-02, `flt-lean-292`, `Modularity/MoretBailly.lean`.  Frontier 20 → 19 in
that module, no leaf opened, and no mathematics done — which is the point.)
A recurring shape here: a property `P` is known for an object `X₀`, a second
object `X` is produced somewhere by a construction, the two are related by a
comparison (`IsFormOver`, a base change, an equivalence), and somebody cuts a
leaf saying **"`P` transports along the comparison"**.  `affineOpen_of_finite_of_isFormOver`
was exactly that: Serre's criterion (every finite set lies in an affine open)
for a `K`-form, over a bare `IsFormOver K fX fX₀`.
**Before proving a transport leaf, find the leaf that CONSTRUCTS the object and
ask whether `P` falls out of the construction.**  It usually does, and then the
transport leaf is not proven but DELETED — a `1 → 0` trade, where recutting it
is only `1 → 1`.  Here the twist is built by
`exists_isGaloisTwistForm_of_semilinearAction` (Galois descent: glue `Spec (B^G)`
over the `a`-stable affine opens its own `hstab` hypothesis supplies), so the
correspondence *stable affine open upstairs ↦ affine open downstairs* is already
part of what that leaf owes, and Serre's criterion for the twist is three lines
over it.  The clause was appended to its conclusion, threaded through the two
proven assemblies above it and the interface `IsEffectiveQGaloisTwist`, and the
transport leaf deleted.
**THE TELL THAT THE TRANSPORT SHAPE IS WRONG: its route has to REBUILD structure
that the construction leaf already holds.**  Stated over a bare form, this leaf
had thrown away the semilinear action, the open kernel and `hstab`, so its own
four-step route needed transitivity of `Γ_ℚ` on the fibres of `X ⊗ K ⟶ X` and
descent of affineness along `Spec K ⟶ Spec ℚ` — the latter being literally the
open TODO in `Mathlib.AlgebraicGeometry.Morphisms.Descent`.  When a leaf's route
reads as a re-derivation of its neighbour's hypotheses, the cut is on the wrong
seam.
**AND A ROUTE PARAGRAPH THAT ASSIGNS A HYPOTHESIS A JOB IT CANNOT DO IS THE
SECOND TELL.**  Its `WHERE THE HYPOTHESES GO` list said `hqc` "bounds step 3's
translate count together with `halg`".  Quasi-compactness of `fX` says nothing
about how many Galois translates of a given affine open occur; the bound comes
only from the comparison being defined at a FINITE level, i.e. from a
spreading-out (EGA IV 8.8) that the route never mentions.  A hypothesis audit
that cannot account for a step is evidence the hypothesis list is wrong, not
that the step is easy — and it is cheap to check, because you only have to ask
what each named hypothesis actually gives you.
### The technique that removed a whole finiteness obligation: ONE PREIMAGE, NOT THE FIBRE
Worth having on its own, because it applies to every Galois/quotient descent.
To put a finite `s ⊆ X` inside an affine open, the reflex is to pull `s` back
to the full preimage `π⁻¹(s)` upstairs and ask for an affine open containing
THAT — which needs `π⁻¹(s)` finite, i.e. here that the algebraic closure of `ℚ`
in a finitely generated field extension is finite over `ℚ`.  True, classical,
and absent from this pin.
It is not needed.  Choose **one** preimage `t_x` of each `x ∈ s`, and ask for a
`Γ`-STABLE affine open `V` containing the finite set `{t_x}`.  Stability does
the rest: `V = π⁻¹(U)` for an open `U`, and `t_x ∈ V` already gives `x ∈ U`.
So a stability hypothesis you have anyway can delete a finiteness hypothesis you
do not.  **Whenever a descent argument seems to need finite fibres, check
whether the object you are building is stable under the group — if it is, one
point per fibre suffices.**
### Verifying an INTERFACE change: `lake build <YourModule>` builds UPSTREAM only
This edit changed a `def`'s existential and two theorems' conclusions, i.e. it is
the class-7 interface shape.  `lake build Fermat.FLT.Modularity.MoretBailly`
green proves nothing about that, because it builds the module's IMPORT CONE and
stops — every consumer is downstream and is never reached.  The two commands
that close it cost one grep and one build:
    grep -rn '<each changed name>' --include=*.lean Fermat/ | grep -v '<your file>:'
    grep -rln 'import Fermat.FLT.<YourModule>' --include=*.lean Fermat/
The first said the four changed names occur nowhere else; the second named three
importers, and building all three in ONE `lake build` invocation came back
`Build completed successfully (5671 jobs)`, EXIT=0, zero errors (HilbertModularity
206 s, KhareWintenberger 126 s, Interface 851 s).  Do the second even when the
first is empty — a `def` whose unfolding changed can break a downstream proof
that never names it.
### Two measurements from the same run
* **`Modularity/MoretBailly.lean` elaborates in 292 s**, not the 40 minutes this
  file quotes elsewhere for it, and the whole cone replayed in ~6 minutes from a
  release-seeded `.lake`.  Re-measure before designing a workflow around a
  quoted iteration cost; these numbers move in both directions.
* **The build log writes `` declaration uses `sorry` `` with BACKTICKS**, not
  with `'sorry'`.  Every recipe in this file that greps for `declaration uses
  'sorry'` therefore returns ZERO on a green build — which reads exactly like a
  finished, sorry-free module.  Grep for `declaration uses` and nothing more.
