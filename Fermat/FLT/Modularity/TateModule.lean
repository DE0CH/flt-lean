/-
Modularity/TateModule.lean — own work for the Fermat project (not
vendored from the FLT project).

# Tate modules of a geometric fibre of an abelian scheme

This module supplies the **second missing piece** of the classical
discharge of `exists_twistedHilbertBlumenthalModuli_of_five_le`
(`Modularity/KhareWintenberger.lean`), continuing
`Modularity/AbelianScheme.lean`. That module made the *torsion* of a
geometric fibre a `Γ_F`-module; this one makes the *Tate module* — the
inverse limit of the torsion along a uniformizer — an object the pin can
name, and cuts the Tate-module construction

  `nonempty_hilbertBlumenthalPoint_of_isTwistedHilbertBlumenthalModuli`

into two independently citable statements of the theory of abelian
varieties:

* `exists_tateFrame_of_levelStructure` — items 7 and 8 of that leaf's
  missing-machinery list: `T_I A` is free of rank `2` over the
  completion `𝒪_{D,I}`, with continuous `Γ_F`-action, and its reduction
  is `A[I]`, so the Frobenius characteristic polynomials of `T_I A`
  reduce to those of the level structure;
* `exists_weilFrobeniusSystem_of_mult` — item 9, Weil/Faltings: those
  characteristic polynomials are already defined over `D` and are
  INDEPENDENT of `I`, i.e. the `T_I A` for varying `I` are members of one
  strictly compatible system. This is the deepest statement in the
  chain.

## Why a DEFINITION is needed here, and what it buys

The two statements above cannot be cut apart without an object that ties
them together. Each of them is an existence statement about a coefficient
ring `O` and a representation `τ : Γ_F → GL₂(O)`; but "there exists a
rank-`2` representation whose reduction is `A[I]`" and "there exists a
`D`-rational compatible system" are, taken separately, statements about
*unrelated* representations — the second is outright FALSE when applied
to an arbitrary `τ` that merely happens to have the right reduction,
since a residual condition constrains `τ` only modulo `I`. Any cut into
two leaves must therefore name the actual Tate module.

`TatePt` is that name. It is the honest inverse limit

  `T = lim ( ⋯ →  A[I³]  --·π-->  A[I²]  --·π-->  A[I] )`,

taken inside the `Γ_F`-module of geometric points supplied by
`Modularity/AbelianScheme.lean`, with the transition maps given by
multiplication by an element `π ∈ I ∖ I²` (which generates `I` in the
local ring `𝒪_{D,I}`, so the limit is the usual `I`-adic Tate module and
not a product over several primes). No completion, no topology and no
profinite machinery is needed to WRITE it: it is a subtype of
`ℕ → GeomFibrePt f x` cut out by two equations, exactly as
`Mult.torsion` is a subset cut out by one.

Both leaves below then speak about `TatePt`: the first produces a FRAME
— a `Γ_F`-equivariant additive bijection `(Fin 2 → O) ≃ T` — and the
second consumes one. That is the link, and it is what makes the second
leaf a true statement rather than a plausible-looking false one.

## What is proven here

One lemma, `isIrreducible_map_of_restrictionSurjective`: irreducibility
of a Galois representation descends along a restriction that preserves
the image. It is what lets the consumer supply the irreducibility
hypothesis that the first leaf needs at `λ` (see the FAITHFULNESS AUDIT
there — the leaf was FALSE without it). Otherwise this module is the cut:
one definition and two sorried leaves, both statements about the
geometric objects of `AbelianScheme.lean` and about nothing else.
-/
module

public import Fermat.FLT.Modularity.AbelianScheme
public import Fermat.FLT.Deformations.RepresentationTheory.GaloisRep
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Dimension.Constructions
-- `NumberField.IsTotallyReal`: the real-multiplication field of a
-- Hilbert–Blumenthal family is totally real, in both leaf STATEMENTS
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry IsDedekindDomain Polynomial

namespace Fermat

/-! ### The Tate module of a geometric fibre -/

/-- **The `I`-adic Tate module of the geometric fibre of `f : A ⟶ S` at
an `F`-point `x`**, for an ideal `I` of the coefficient ring `R` acting
on `A` and an element `π ∈ I`:

  `T = lim_n A[Iⁿ]`, the transition maps being multiplication by `π`.

Concretely a point of `T` is a sequence `y : ℕ → A(F̄)` with `y n`
killed by `Iⁿ` and `π · y (n+1) = y n`. The zeroth stage is trivial —
`I⁰ = ⊤` contains `1`, so `A[I⁰] = 0` and hence `y 0 = 0` — which is the
usual indexing of the limit.

The intended `π` is an element of `I ∖ I²` for `I` maximal in the ring
of integers of a number field, so that `I` becomes principal generated
by `π` in the local ring `R_I` and the limit above is the classical
`I`-adic Tate module. Leaves stating properties of `TatePt` therefore
carry `π ∈ I` and `π ∉ I ^ 2` as hypotheses; with a `π` violating them
(most brutally `π = 0`, which forces `T = 0`) the object is not the Tate
module and no rank-`2` frame exists — which is exactly why the frame is
what the leaves below quantify over.

The Galois action is the one induced from
`Fermat.AbelianSchemeStruct.galSMul` componentwise, and the additive
structure the one induced from `Fermat.AbelianSchemeStruct.add`
componentwise; both are written out explicitly in the statements below
rather than installed as instances, in the same style as the level
structures of `IsTwistedHilbertBlumenthalModuli`, so that nothing has to
be carried through the `letI` of `AbelianSchemeStruct.addCommGroup`. -/
def TatePt {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {R : Type u} [CommRing R] (m : Mult ab R)
    {F : Type u} [Field F] (x : Spec (CommRingCat.of F) ⟶ S)
    (I : Ideal R) (π : R) : Type u :=
  {y : ℕ → GeomFibrePt f x //
    (∀ n, y n ∈ (m.torsion x (I ^ n)).1) ∧ (∀ n, m.act π (y (n + 1)) = y n)}

/-! ### Irreducibility along an image-preserving restriction -/

/-- **Irreducibility descends to a subgroup with the same image** (PROVEN).

If every value of `ρ` is already a value of `ρ.map f` — which is what the
`hrestr` hypothesis of the twisted moduli problem asserts — then the two
representations have literally the same invariant submodules, so the
lattice of subrepresentations is the same and simplicity transfers.

This is what carries the irreducibility hypothesis of
`exists_twistedHilbertBlumenthalModuli_of_five_le` from `Γ_ℚ` down to
`Γ_F`, where `exists_tateFrame_of_levelStructure` needs it; see the
FAITHFULNESS AUDIT there for why it is needed. -/
theorem isIrreducible_map_of_restrictionSurjective
    {F : Type u} [Field F]
    {k : Type u} [Field k] [TopologicalSpace k]
    {W : Type v} [AddCommGroup W] [Module k W]
    (ρ : GaloisRep ℚ k W) (f : ℚ →+* F)
    (hrestr : ∀ g : Field.absoluteGaloisGroup ℚ,
      ∃ h : Field.absoluteGaloisGroup F, (ρ.map f) h = ρ g)
    (hirr : ρ.IsIrreducible) : (ρ.map f).IsIrreducible := by
  have key : ∀ s : Submodule k W,
      (∀ (h : Field.absoluteGaloisGroup F) ⦃v : W⦄, v ∈ s → (ρ.map f) h v ∈ s) ↔
        (∀ (g : Field.absoluteGaloisGroup ℚ) ⦃v : W⦄, v ∈ s → ρ g v ∈ s) := by
    intro s
    constructor
    · intro hs g v hv
      obtain ⟨h, hh⟩ := hrestr g
      have hmem := hs h hv
      rwa [hh] at hmem
    · intro hs h v hv
      have hmem := hs (Field.absoluteGaloisGroup.map f h) hv
      rwa [← GaloisRep.map_apply] at hmem
  let e : Subrepresentation (ρ.map f).toRepresentation ≃o
      Subrepresentation ρ.toRepresentation :=
    { toFun := fun s => ⟨s.toSubmodule, (key _).mp s.apply_mem_toSubmodule⟩
      invFun := fun s => ⟨s.toSubmodule, (key _).mpr s.apply_mem_toSubmodule⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact (OrderIso.isSimpleOrder_iff e).mpr hirr

/-! ### The two leaves of the Tate-module construction -/

/-- **Tate modules are free of rank two, and reduce to the torsion**
(sorry node — items 7 and 8 of the Tate-module construction; Silverman
*AEC* III.7 and *ATAEC* for the elliptic case, Mumford *Abelian
Varieties* §18 in general, Taylor 2002 §2 for the Hilbert–Blumenthal
normalization).

Let `A ⟶ S` be an abelian scheme with a multiplication by the ring of
integers of a totally real field `D` whose degree equals the relative
dimension — a Hilbert–Blumenthal family — and let `x` be an `F`-point.
Let `I` be a maximal ideal of `𝒪_D` over the rational prime `q`, and
suppose the `I`-torsion of the geometric fibre at `x` is identified, as a
`Γ_F`-module, with a two-dimensional representation `ρ'` over a finite
field `k'` (this is precisely the shape of a level structure of
`IsTwistedHilbertBlumenthalModuli`).

Then there are an element `π ∈ I ∖ I²`, a coefficient ring `O`
(classically the completion `𝒪_{D,I}`: a local ring, finite free over
`ℤ_q`, with its module topology) and a continuous representation
`τ : Γ_F → GL₂(O)` which **frames** the Tate module `TatePt m x I π`:
an additive, `Γ_F`-equivariant bijection `(Fin 2 → O) ≃ T`. Moreover the
reduction `O →+* k'` carries the Frobenius characteristic polynomials of
`τ` onto those of `ρ'`.

Two remarks on the statement.

* The residual clause holds at EVERY place `w`, not merely outside a bad
  set: it expresses an isomorphism `T / I·T ≅ A[I]` of `Γ_F`-modules,
  and isomorphic representations have equal characteristic polynomials
  at every group element. The finite bad set of the compatible system
  enters only through `exists_weilFrobeniusSystem_of_mult`.
* The reduction map `ι₀` is EXISTENTIALLY quantified rather than being
  "the" residue map. This is not slack: the level structure `e` is only
  an isomorphism of `Γ_F`-modules, so the `k'`-structure of `ρ'` and the
  `𝒪_D/I`-structure transported from `A[I]` are two embeddings of a
  finite field into the commutant of the Galois image, conjugate only up
  to an automorphism of that field. Composing the residue map with that
  automorphism is exactly what `ι₀` absorbs — but ONLY under `hirr`; see
  the audit below. It is also why the two-dimensionality hypothesis `hV`
  cannot be dropped: see the FAITHFULNESS AUDIT in
  `nonempty_hilbertBlumenthalPoint_of_isTwistedHilbertBlumenthalModuli`,
  where dropping it makes the consumer FALSE.

THE FRAME REMEMBERS THE REAL MULTIPLICATION (2026-07-26, requested by
the owner of `exists_weilFrobeniusSystem_of_mult`, whose leaf is FALSE
without it). The conclusion also produces a ring map
`j : 𝒪_D →+* O` together with `hj`, saying that the `O`-action
transported to `TatePt` along `φ` EXTENDS the real multiplication
`m.act`. Without that clause `O` ranges over every commutative subring
of `End_{Γ_F}(T)` of the right `ℤ_q`-rank over which `T` is free of rank
two, and when `A_x` has endomorphisms beyond `𝒪_D` such rings exist and
are not `𝒪_{D,I}`: for `D = ℚ(√5)`, `A = E × E` with `𝒪_D` acting by the
companion matrix of `X² - X - 1` and `q = 13` inert, `O = ℤ₁₃[N] ≅
ℤ₁₃[ε]/(ε²)` with `N` nilpotent satisfies every other clause of this
conclusion and admits NO injective ring map into `AlgebraicClosure ℚ₁₃`.
With `j` and `hj` the image of `𝒪_D ⊗ ℤ_q` lies in `O`, and with the
rank count and integral closedness `O = 𝒪_{D,I}`; then `τ.charFrob` is
the reduced rank-two Frobenius polynomial that Weil/Faltings is about.
This is free for the prover, who constructs `𝒪_{D,I}` anyway: `j` is its
structure map and `hj` is how the action was built.

FAITHFULNESS AUDIT (2026-07-26): **THE LEAF WAS FALSE AS STATED**, and
is repaired here by the hypothesis `hirr : ρ'.IsIrreducible`.

The refuted claim is the one recorded in the ASSEMBLY docstring of
`nonempty_hilbertBlumenthalPoint_of_isTwistedHilbertBlumenthalModuli`:
that the `k'`-structure of `ρ'` and the `𝒪_D/I`-structure transported
from `A[I]` are "two embeddings of `𝔽_q` into the commutant of the
Galois image, conjugate up to an automorphism of `𝔽_q` by
Wedderburn–Malcev". That is not a theorem. Wedderburn–Malcev and
Noether–Skolem conjugate embeddings inside a SIMPLE algebra, and the
commutant `C := End_{ℤ[Γ_F]}(A[I])` need not be simple; when it is
commutative it has no inner automorphisms at all, and two embeddings of
`𝔽_q` into it are genuinely inequivalent.

COUNTEREXAMPLE (no hypothesis of the previous statement is violated).
Let `A₀/ℚ` be a Hilbert–Blumenthal abelian surface with real
multiplication by `𝒪_D`, `D` real quadratic, `A₀` without complex
multiplication — e.g. `J₀(23)`, with `D = ℚ(√5)`. By Ribet's big-image
theorem the mod-`I` image contains `SL₂(𝒪_D/I)` for all but finitely
many `I`, and the `I`-adic image is open in `GL₂(𝒪_{D,I})`. Choose such
an `I` with `q` INERT in `D`, so `k := 𝒪_D/I ≅ 𝔽_{q²}`. Let `F` be the
fixed field of the preimage under `ρ̄ := ρ̄_{A₀,I}` of the diagonal
torus and `A := A₀ ×_ℚ F`; then `ρ̄|_{Γ_F} = α ⊕ β` with `(α,β)`
surjecting onto `{(a, a⁻¹) : a ∈ 𝔽_{q²}ˣ}`.

Take `V := A[I]` as an abelian group, `e := id`, and give `V` the
`k' := 𝔽_{q²}`-structure `λ ∗ (a₁, a₂) := (λ a₁, λ^q a₂)` in the
eigenbasis. It commutes with the diagonal Galois action, so `e` is an
additive `Γ_F`-equivariant bijection onto `(m.torsion x I).1`,
`Module.rank k' V = 2`, and `ρ'` is the `k'`-linear representation
`diag(α, β^q)`. Every hypothesis of the previous statement holds.

But openness of the `I`-adic image forces `End_{ℤ[Γ_F]}(T_I A) =
𝒪_{D,I}`, so any frame forces `O ≅ 𝒪_{D,I}` and `charpoly (τ σ)` to be
a `ψ`-twist of the canonical one, `ψ ∈ Aut(𝒪_{D,I}/ℤ_q)`; and every ring
map `ι₀ : O →+* k'` is the residue map followed by a field isomorphism
`k ≅ k'`. So the achievable residual characteristic polynomials are
exactly `(X - θα)(X - θβ)` for `θ ∈ Aut(k)`, while the conclusion
demands `(X - α)(X - β^q)` at every `w`. Pick `w` with `α(Frob_w)` of
order `q² - 1` (Chebotarev): `θ = id` would need `β = β^q` and
`θ = Frob` would need `α = α^q`, both false. No `ι₀` exists.

THE REPAIR, and why it is exactly right. If `ρ'` is irreducible then
`A[I]` is a semisimple `𝔽_p[Γ_F]`-module (`k'/𝔽_p` is separable, so
`J(k'[Γ]) = k' ⊗ J(𝔽_p[Γ])`) and the `𝒪_D/I`-structure representation
`ρ̄` is irreducible as well: a split `ρ̄ = α ⊕ β` with `α ≠ β` has
commutant `k × k` and a scalar `ρ̄` has commutant `M₂(k)`, and in both
every field structure of order `#k` makes `ρ'` REDUCIBLE. With `ρ̄`
irreducible, `C` is either a finite field — when `ρ̄` is irreducible but
not absolutely irreducible — or a central simple algebra over its centre
in which `k` is self-centralizing; in both cases the two embeddings of
`k` into `C` differ by an inner automorphism of `C` composed with an
element of `Aut(k)`. The inner automorphism is an additive
`Γ_F`-equivariant change of frame, absorbed by `φ`; the field
automorphism is absorbed by `ι₀`. That is the argument the previous
docstring intended, and irreducibility is exactly what makes it
available.

`hirr` costs the consumers nothing: at `𝔭` the moduli condition
`IsTwistedHilbertBlumenthalModuli` already carries `ρbarp.IsIrreducible`,
and at `λ` the irreducibility of `ρbar` is a hypothesis of
`exists_twistedHilbertBlumenthalModuli_of_five_le`, transported to `Γ_F`
along `hrestr` by `isIrreducible_map_of_restrictionSurjective` above. -/
theorem exists_tateFrame_of_levelStructure
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f)
    (q : ℕ) [Fact q.Prime]
    (I : Ideal (NumberField.RingOfIntegers D)) (hI : I.IsMaximal)
    (hqI : (q : NumberField.RingOfIntegers D) ∈ I)
    {k' : Type u} [Field k'] [Finite k'] [TopologicalSpace k'] [DiscreteTopology k']
    {V : Type v} [AddCommGroup V] [Module k' V] [Module.Finite k' V] [Module.Free k' V]
    (hV : Module.rank k' V = 2)
    (ρ' : GaloisRep F k' V)
    (hirr : ρ'.IsIrreducible)
    (e : V → GeomFibrePt f x)
    (headd : ∀ v v' : V, e (v + v') = ab.add (e v) (e v'))
    (heinj : Function.Injective e)
    (heequiv : ∀ (σ : Field.absoluteGaloisGroup F) (v : V),
      e (ρ' σ v) = ab.galSMul x σ (e v))
    (heimg : ∀ y, y ∈ (m.torsion x I).1 ↔ ∃ v, e v = y) :
    ∃ (π : NumberField.RingOfIntegers D) (_ : π ∈ I) (_ : π ∉ I ^ 2)
      (O : Type u) (_ : CommRing O) (_ : TopologicalSpace O) (_ : IsTopologicalRing O)
      (_ : Algebra ℤ_[q] O) (_ : IsLocalRing O) (_ : Module.Finite ℤ_[q] O)
      (_ : Module.Free ℤ_[q] O) (_ : IsModuleTopology ℤ_[q] O)
      (τ : GaloisRep F O (Fin 2 → O))
      (φ : (Fin 2 → O) → TatePt m x I π) (ι₀ : O →+* k')
      (j : NumberField.RingOfIntegers D →+* O),
      (∀ (u u' : Fin 2 → O) (n : ℕ),
        (φ (u + u')).1 n = ab.add ((φ u).1 n) ((φ u').1 n)) ∧
      Function.Bijective φ ∧
      (∀ (σ : Field.absoluteGaloisGroup F) (u : Fin 2 → O) (n : ℕ),
        (φ (τ σ u)).1 n = ab.galSMul x σ ((φ u).1 n)) ∧
      (∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
        (τ.charFrob w).map ι₀ = ρ'.charFrob w) ∧
      ∀ (a : NumberField.RingOfIntegers D) (u : Fin 2 → O) (n : ℕ),
        (φ (j a • u)).1 n = m.act a ((φ u).1 n) :=
  sorry

/-- **The Frobenius characteristic polynomials of the Tate modules form
one `D`-rational compatible system** (sorry node — item 9 of the
Tate-module construction, and the deepest statement in the chain: Weil's
Riemann hypothesis for abelian varieties over finite fields together
with Faltings' theorem that the system is independent of the residue
characteristic; see Faltings, *Endlichkeitssätze für abelsche
Varietäten über Zahlkörpern*, Invent. Math. 73 (1983), and Taylor 2002
§2 for the Hilbert–Blumenthal normalization used here).

For an abelian scheme with real multiplication by `𝒪_D` and an
`F`-point `x` there is a family `P : w ↦ P_w ∈ D[T]` of polynomials with
coefficients in `D` ITSELF, such that for EVERY maximal ideal `I` of
`𝒪_D`, every `π` and every frame `φ` of `TatePt m x I π` by a rank-two
representation `τ` over a coefficient ring `O`, the characteristic
polynomial of Frobenius at `w` on `τ` agrees with `P_w` inside an
algebraic closure of `ℚ_q`, for all but finitely many `w`.

Four points are load-bearing in the way this is stated.

* The system `P` is quantified BEFORE `I`: one family of polynomials
  serves every residue characteristic. That is exactly the
  independence-of-`λ` statement, and it is what makes the `λ`-adic and
  `𝔭`-adic Tate modules of a single abelian variety two members of ONE
  compatible system — the fields `matchℓ` and `matchp` of
  `HilbertBlumenthalPoint`.
* The exceptional set `bad` is quantified AFTER `q`, and this is not
  slack — the statement would be FALSE the other way round. `bad` must
  contain the places of `F` above `q`, where the `I`-adic representation
  is ramified and its Frobenius characteristic polynomial is not the
  Weil polynomial at all; and since `q` ranges over every rational
  prime, no single finite set can contain the places above all of them.
  Only the places of bad reduction of `A_x` are independent of `q`. The
  consumer needs no more: it applies this leaf at exactly two ideals and
  takes the union of the two exceptional sets, which is finite.
* `τ` is not quantified freely: it must FRAME the Tate module
  `TatePt m x I π`. Without that hypothesis the statement would be false,
  since nothing would tie `τ` to `A` — a residual condition constrains a
  representation only modulo `I`. The frame is transported along a
  bijection, and characteristic polynomials are invariant under
  conjugation, so no compatibility beyond additivity and Galois
  equivariance is required of `φ`.
* The embeddings `ψ` of `D` and `ι` of `O` into `ℚ̄_q` are likewise
  produced per `I` (they are the place of `D` over `q` determined by
  `I`, and the structural embedding of the completion), whereas `P` is
  not; `ι` is required injective, which is the statement that `O` is a
  domain of characteristic zero — the Carayol normalization of the
  coefficients. -/
theorem exists_weilFrobeniusSystem_of_mult
    {A S : Scheme.{u}} {f : A ⟶ S} {ab : AbelianSchemeStruct f}
    {D : Type u} [Field D] [NumberField D] [NumberField.IsTotallyReal D]
    (m : Mult ab (NumberField.RingOfIntegers D))
    {F : Type u} [Field F] [NumberField F]
    (x : Spec (CommRingCat.of F) ⟶ S)
    (hdim : SmoothOfRelativeDimension (Module.finrank ℚ D) f) :
    ∃ P : HeightOneSpectrum (NumberField.RingOfIntegers F) → Polynomial D,
      ∀ (q : ℕ) (_ : Fact q.Prime)
        (I : Ideal (NumberField.RingOfIntegers D)) (_ : I.IsMaximal)
        (_ : (q : NumberField.RingOfIntegers D) ∈ I)
        (π : NumberField.RingOfIntegers D) (_ : π ∈ I) (_ : π ∉ I ^ 2)
        (O : Type u) (_ : CommRing O) (_ : TopologicalSpace O) (_ : IsTopologicalRing O)
        (τ : GaloisRep F O (Fin 2 → O)) (φ : (Fin 2 → O) → TatePt m x I π),
        (∀ (u u' : Fin 2 → O) (n : ℕ),
          (φ (u + u')).1 n = ab.add ((φ u).1 n) ((φ u').1 n)) →
        Function.Bijective φ →
        (∀ (σ : Field.absoluteGaloisGroup F) (u : Fin 2 → O) (n : ℕ),
          (φ (τ σ u)).1 n = ab.galSMul x σ ((φ u).1 n)) →
        ∃ (bad : Finset (HeightOneSpectrum (NumberField.RingOfIntegers F)))
          (ψ : D →+* AlgebraicClosure ℚ_[q]) (ι : O →+* AlgebraicClosure ℚ_[q]),
          Function.Injective ι ∧
          ∀ w ∉ bad, (τ.charFrob w).map ι = (P w).map ψ :=
  sorry

end Fermat
