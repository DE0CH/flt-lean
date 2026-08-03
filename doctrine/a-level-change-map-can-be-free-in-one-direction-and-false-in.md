## A LEVEL-CHANGE MAP CAN BE FREE IN ONE DIRECTION AND FALSE IN THE OTHER — ASK WHICH ONE YOUR CONSUMER NEEDS
(2026-08-02, `flt-lean-219`, on `exists_eigenform_eraseS_of_isUnramifiedAt` in
`Modularity/KhareWintenberger.lean`. The automorphic-forms development had NO
level-changing statement of any kind; it now has three, and the shape of the
finding generalises past automorphic forms.)
`LevelStruct.form D M` is a `Submodule R (WeightTwoAutomorphicForm F D M)` — the
SAME ambient module for every level — so comparing two levels is comparing two
submodules of one module, and no map has to be constructed at all. That makes it
tempting to write down "the oldform inclusion" in whichever direction the prose
suggests. **The two directions are not equally available, and the asymmetry is
invisible until you write the proof:**
* `form(ℒ') ≤ form(ℒ)` for `ℒ.U ≤ ℒ'.U` — the naive degeneracy/oldform map, and
  the one a task prompt will name — needs the CHARACTERS to agree, i.e. needs
  `ℒ.χ` to be TRIVIAL on the small group at the place where the levels differ.
  In this development that is `𝒮.χS w₀ = 1`, which the caller cannot supply.
* the other direction — `f ∈ form(ℒ)` **plus invariance under `ℒ'`'s local group
  at `w₀`** implies `f ∈ form(ℒ')` — is FREE, with no hypothesis on `ℒ.χ w₀`
  whatever. The reason is one line: `LocalLevelStruct.exists_mul_eq` decomposes
  `y = A · incl_{w₀} b` with `A` trivial in the `w₀`-slot, so `ℒ.χ w₀` is
  evaluated at `1` and contributes nothing.
**So the discipline is: before proving a comparison lemma, write down which side
your consumer starts on.** Here the consumer starts with a form at the SMALL
level and wants it at the BIG one, which is the free direction; the blocked
direction is the one the prompt asked for, and landing it would have been
free-floating code that no assembly could consume.
**And the same asymmetry decides whether a proposed reframing is even true.** The
prompt's route (a) said the map "makes the target expressible as `f` is in the
image". It is not: for an unramified `π_{w₀}` the Iwahori-fixed space `π^{I}` is
`2`-dimensional and the spherical space `π^{K}` is `1`-dimensional, so the
newvector is a DIFFERENT vector of the same eigensystem and `f` is generically
not in the image. A reframing that reads as bookkeeping can be a false
mathematical claim; check it against the dimensions before building for it.
### `_eq_finsetSum` IS THE INDEPENDENCE LEMMA — read the RHS for what it does NOT mention
The bridge that made the whole cut work is four lines, and it was found by
reading one existing lemma rather than by proving anything:
    LocalLevelStruct.heckeOperator_eq_finsetSum … (s) (hs) (f) :
      (ℒ.heckeOperator D M v hv g f).1 = ∑ i ∈ s, i • f.1
The right-hand side mentions the level `ℒ` **only through `s`**, the set of coset
representatives — and `s` is constrained only by `ℒ.US v`. So when two levels have
the SAME local group at `v`, one `s` serves both and the two operators agree on
the common underlying form. That is `heckeOperator_congr_of_US_eq`, and it is what
lets an eigenvalue proved at one level be read at another.
**Generalisable: whenever an operator has a "`= ∑ …` over chosen data" lemma, look
at which parameters survive on the right.** Every parameter that does NOT is a
free congruence lemma, and in a development that defines operators by double
cosets this is where the level-change API comes from. Do not go looking for a
functorial construction first.
### Two traps met on the way
* **`@[simps]` on a structure-valued `def` gives a rewrite that DESTROYS the
  syntactic form of its own subject.** After `simp only [LocalLevelStruct.toStruct_χ]`
  the product's domain prints as an anonymous subgroup literal
  `{ carrier := …, mul_mem' := …, … }` rather than as `ℒ.toStruct.U`, so
  `rw [MonoidHom.finsetProd_apply]` fails with *"Did not find an occurrence of the
  pattern `(∏ x ∈ ?s, ?f x) ?b`"* against a goal that displays exactly that
  pattern. The cure is the standing one — state the reduced form as a named lemma
  proved by `exact MonoidHom.finsetProd_apply _ _ _`, since `exact` checks up to
  defeq and `rw` cannot. Worth doing ONCE per such `@[simps]` projection; every
  later consumer then rewrites with a clean statement.
* **`Subtype.ext_iff.mp h` and `congrArg Subtype.val h` both elaborate their
  implicit types from the EXPECTED result, not from `h`.** Given
  `h : (⟨f.1, _⟩ : form') = 0` and a goal `f = 0`, both report *"argument `h` has
  type `⟨↑f, ⋯⟩ = 0` but is expected to have type `f = 0`"* — the unifier ran the
  wrong way. Pin the function explicitly:
  `congrArg (fun z : form' => (z : Ambient)) h`.
### `HeckeOperator.U` is the TAYLOR–WILES `U`, not the Iwahori one
Checked 2026-08-02, and it kills a route that reads as obviously available.
`TotallyDefiniteQuaternionAlgebra.HeckeOperator.U` in
`HeckeOperators/Concrete.lean` takes `hvQ : v ∈ 𝒮.Q` as a hypothesis. So at a
level datum with `𝒮.Q = ∅` — which is what the whole `KhareWintenberger.lean`
level-lowering cluster carries — **there is no `U` operator at all**, and any cut
"through the Iwahori relation `α² − a_v α + Nv = 0` on the Iwahori-fixed space"
is not expressible. `U_mul_U` is likewise about `Q`-places. Before costing a
route through an operator, read the hypothesis list of the operator, not its name.
