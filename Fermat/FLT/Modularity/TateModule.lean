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
  chain. **It is currently FALSE AS STATED** — see the FAITHFULNESS
  AUDIT in its own docstring, which refutes it with two explicit
  counterexamples and gives the three-declaration seam repair. Do not
  dispatch a prover at it before the repair lands.

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
second consumes one. That is the link, and it is what was supposed to
make the second leaf a true statement rather than a plausible-looking
false one.

**It is not enough, and the second leaf is false because of it**
(2026-07-26). An additive `Γ_F`-equivariant bijection ties `τ` to `A`
but NOT to the real multiplication `m`: the coefficient ring `O` is
pinned only up to "some commutative subring of `End_{Γ_F}(T)` over
which `T` is free of rank two", and when `A_x` has endomorphisms beyond
`𝒪_D` there are such rings that are not `𝒪_{D,I}` — including
non-domains, for which the second leaf's conclusion fails outright. The
frame notion must carry a ring map `𝒪_D →+* O` intertwining `φ` with
`m.act`; see the FAITHFULNESS AUDIT on
`exists_weilFrobeniusSystem_of_mult`.

## What is proven here

Nothing. This module contains exactly one definition and two sorried
leaves; its content is the cut. The definition carries no axioms of its
own, so the leaves are statements about the geometric objects of
`AbelianScheme.lean` and about nothing else.
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
  to an automorphism of that field (Wedderburn–Malcev). Composing the
  residue map with that automorphism is exactly what `ι₀` absorbs. It is
  also why the two-dimensionality hypothesis `hV` cannot be dropped: see
  the FAITHFULNESS AUDIT in
  `nonempty_hilbertBlumenthalPoint_of_isTwistedHilbertBlumenthalModuli`,
  where dropping it makes the consumer FALSE. -/
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
      (φ : (Fin 2 → O) → TatePt m x I π) (ι₀ : O →+* k'),
      (∀ (u u' : Fin 2 → O) (n : ℕ),
        (φ (u + u')).1 n = ab.add ((φ u).1 n) ((φ u').1 n)) ∧
      Function.Bijective φ ∧
      (∀ (σ : Field.absoluteGaloisGroup F) (u : Fin 2 → O) (n : ℕ),
        (φ (τ σ u)).1 n = ab.galSMul x σ ((φ u).1 n)) ∧
      ∀ w : HeightOneSpectrum (NumberField.RingOfIntegers F),
        (τ.charFrob w).map ι₀ = ρ'.charFrob w :=
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
  conjugation, so — the original claim continued — no compatibility
  beyond additivity and Galois equivariance is required of `φ`. **That
  last clause is exactly the falsity refuted below.**
* The embeddings `ψ` of `D` and `ι` of `O` into `ℚ̄_q` are likewise
  produced per `I` (they are the place of `D` over `q` determined by
  `I`, and the structural embedding of the completion), whereas `P` is
  not; `ι` is required injective, which is the statement that `O` is a
  domain of characteristic zero — the Carayol normalization of the
  coefficients. **`O` being a domain is not a consequence of any
  hypothesis here**; see the audit.

## FAITHFULNESS AUDIT (2026-07-26) — THIS LEAF IS FALSE AS STATED

Two independent explicit counterexamples are given below. **Do not
dispatch a prover at this statement**: it cannot be proven, and anything
derived from it is worthless. The repair is a CUT-LEVEL change spanning
three declarations with three different owners and is described at the
end; it is REPORTED, not made here, because the frame is produced by the
sibling `exists_tateFrame_of_levelStructure` (another owner, working
concurrently) and consumed by the PROVEN assembly
`nonempty_hilbertBlumenthalPoint_of_isTwistedHilbertBlumenthalModuli`
(`Modularity/KhareWintenberger.lean`), whose `HilbertBlumenthalPoint`
fields `ιO₀_injective` / `ιC_injective` and `matchℓ` / `matchp` are
exactly the two clauses refuted. Changing this statement in isolation
turns a false leaf into a hard build error, which is worse.

**The quantifier repair recorded in the second bullet DID hold up.**
`bad`, `ψ` and `ι` are all produced after `q`, `I`, `π` and the frame;
`P` alone is produced before `q`; every remaining binder (`D`, `m`, `x`,
`hdim`) is genuinely independent of `q`. No sibling quantifier has the
same defect. The falsity found here is a different one.

### The defect

`O`, `τ` and `φ` range over ALL frames of `TatePt m x I π` that are
merely additive, bijective and `Γ_F`-equivariant. Nothing requires the
frame to REMEMBER THE REAL MULTIPLICATION — that the `O`-module
structure transported to `T` along `φ` is the one induced by `𝒪_D`
through `m.act`. Additivity plus `Γ_F`-equivariance determine `τ`
uniquely as `φ⁻¹ ∘ galSMul σ ∘ φ`, but they leave `O` free: any
commutative subring `O ⊆ End_{Γ_F}(T)` that is `ℤ_q`-free of rank
`[𝒪_{D,I} : ℤ_q]` and over which `T` is free of rank `2` is a legal
frame. When `A_x` has endomorphisms beyond `𝒪_D`, such rings exist and
are NOT `𝒪_{D,I}`.

(`O` is automatically a `ℤ_q`-algebra even though nothing says so: `φ`
forces `O ⊕ O ≅ T ≅ ℤ_q^{2d}` as abelian groups, and every additive
endomorphism of `ℤ_q^n` is `ℤ_q`-linear, since divisibility by `q^n` is
preserved. So the exotic frames below really are the general shape.)

### Counterexample 1 — `Function.Injective ι` fails, and it survives
### EVERY clause the sibling leaf produces

`D = ℚ(√5)` (totally real, `finrank ℚ D = 2`), `F` any number field,
`E/F` any elliptic curve, `A = E × E` over `S = Spec F`, `x = 𝟙`. Then
`f : A ⟶ S` is proper, smooth, with geometrically connected fibres, of
relative dimension `2 = finrank ℚ D`, and `𝒪_D = ℤ[(1+√5)/2]` acts by
the companion matrix `[[0,1],[1,1]] ∈ M₂(ℤ) ⊆ End(E × E)` of `X² − X − 1`
(verified: `charpoly [0,1;1,1] = x² − x − 1`). Every hypothesis holds.

Take `q = 13`, which is INERT in `ℚ(√5)` (`kronecker(5,13) = −1`), so
`I = 13·𝒪_D` is maximal, `13 ∈ I`, `π = 13 ∉ I²`, and
`T := TatePt m x I π = T₁₃(E × E) = W ⊗_{ℤ₁₃} T₁₃E` with `W = ℤ₁₃²` the
"multiplicity space" on which `M₂(ℤ₁₃)` acts and `Γ_F` acts trivially.

Now put `O := ℤ₁₃[N] ≅ ℤ₁₃[ε]/(ε²)`, `N = [[0,1],[0,0]] ∈ End(W)`. It is
a commutative topological ring; `W` is free of rank `1` over it
(`W = O·e₂`), so `T ≅ O ⊗_{ℤ₁₃} T₁₃E ≅ O²`; and `Γ_F`, acting only on
the `T₁₃E` factor, is `O`-linear. So `(O, τ, φ)` is a legal frame. But
`O` has a nonzero nilpotent, so **there is no injective ring
homomorphism `O →+* AlgebraicClosure ℚ₁₃` at all**, and the conclusion
fails outright.

This frame satisfies **every** clause of the sibling leaf's conclusion,
which is what makes it decisive: `O` is LOCAL, an `ℤ₁₃`-algebra, finite
free over `ℤ₁₃`, carries its module topology — and it even meets the
residual clause. Indeed `τ.charFrob w = X² − a_w X + N(w) ∈ ℤ₁₃[X]`
(`a_w` the trace of `Frob_w` on `T₁₃E`), while `A[I] = A[13]` is
`𝔽₁₆₉ ⊗_{𝔽₁₃} E[13]` with `ρ'.charFrob w = X² − ā_w X + N̄(w)` over
`k' = 𝔽₁₆₉`; so `ι₀ : ℤ₁₃[ε] →+* 𝔽₁₆₉`, `ε ↦ 0`, discharges
`(τ.charFrob w).map ι₀ = ρ'.charFrob w` at every `w`. **Hence adding to
this leaf every hypothesis the consumer could actually supply from the
sibling still leaves it false.** That is why the repair has to reach the
real multiplication rather than the shape of `O`.

### Counterexample 2 — the charpoly equation itself fails

Its role is different from Counterexample 1's, and the difference
matters when choosing a repair. This frame is NOT local and does NOT
satisfy the sibling's residual clause, so it is not a counterexample to
the strengthened statements — but it refutes the CHARPOLY EQUATION
itself, not merely the injectivity of `ι`. **So "just delete
`Function.Injective ι`" is not a repair either**: what is broken is the
identification of `τ.charFrob` with a member of the system, and the
injectivity failure of Counterexample 1 is a symptom of the same cause.

Same `D = ℚ(√5)` and `q = 13`, but take `F = ℚ(i)` and `E : y² = x³ − x`
(conductor `32`), which has CM by `ℤ[i] ⊆ F`; `A = E × E` as before.
`13 ≡ 1 mod 4`, so `13` SPLITS in `ℚ(i)`, whence
`T₁₃E = T_𝔭 ⊕ T_𝔭̄` with `Γ_F` acting by two distinct characters
`χ, χ̄ : Γ_F → ℤ₁₃^×`. Hence `T = U₁ ⊕ U₂` with `U_i ≅ ℤ₁₃²` and `Γ_F`
acting on `U₁`, `U₂` by the SCALARS `χ(σ)`, `χ̄(σ)`.

Frame: `O := ℤ₁₃ × ℤ₁₃` acting by the two projections. `T` is free of
rank `2` over it (`e_iT ≅ ℤ₁₃²`), `Γ_F` is `O`-linear, and in the basis
`t_i = u_i + v_i` one has `τ(σ) = (χ(σ), χ̄(σ))·id`, so

    τ.charFrob w = (X − c_w)²  with  c_w = (χ(w), χ̄(w)) ∈ O.

A ring hom out of a product into a field kills one of the two orthogonal
idempotents, so EVERY `ι : O →+* ℚ̄₁₃` factors through a projection and
`(τ.charFrob w).map ι` is a SQUARE `(X − ι(c_w))²` — whatever embedding
of `ℤ₁₃` it uses (this is why possibly-discontinuous embeddings do not
rescue the statement).

Meanwhile the STANDARD frame at the same `(q, I, π)` — namely
`O = 𝒪_{D,I} = ℤ₁₃[α]`, the unramified quadratic extension of `ℤ₁₃`,
`α` the companion matrix acting on `W`, with `T ≅ 𝒪_{D,I} ⊗_{ℤ₁₃} T₁₃E`
— has `τ.charFrob w = X² − a_w X + N(w)`, where `a_w ∈ ℤ` is the trace
of `Frob_w` on `T₁₃E` and `N(w)` its norm; since `ψ` is a field
embedding, hence injective, this
FORCES `P w = X² − a_w X + N(w) ∈ ℚ[X] ⊆ D[X]`, and `ψ` fixes it. So the
exotic frame demands that `X² − a_w X + N(w)` be a square, i.e.
`a_w² = 4N(w)`, i.e. `χ(w) = χ̄(w)`, for all `w` outside a finite set.
But `χ ≠ χ̄` (for `w` over a split `p`,
`{χ(w), χ̄(w)}` is the pair of conjugate Hecke values, e.g. `{9, 2}` in
`ℤ₁₃` at `w | 5`, since `a₅(E) = −2` and `π₅ = −1 + 2i`, `i ↦ 5`), so by
Chebotarev they differ at infinitely many `w`. Contradiction.

(Consistency check that the exotic frame is real rather than an
arithmetic slip: the `ℤ₁₃`-characteristic polynomial of `Frob_w` on `T`
must be the norm of the `O`-one, and indeed
`(X−χ)²(X−χ̄)² = N_{O/ℤ₁₃}((X−c_w)²)` agrees with the value computed
from the standard frame.)

### What does NOT repair it

Three cheaper patches suggest themselves; all three fail, and the reason
each fails is worth recording so that nobody spends a cycle on it.

* *Add the sibling's `O`-conditions* (`Algebra ℤ_[q] O`, `IsLocalRing O`,
  `Module.Finite`/`Module.Free ℤ_[q] O`, `IsModuleTopology ℤ_[q] O`) —
  the only strengthening the consumer could actually supply, since the
  sibling produces exactly these. It excludes Counterexample 2 (that `O`
  is not local) but NOT Counterexample 1, which satisfies all of them.
* *Delete `Function.Injective ι`.* Counterexample 2 refutes the charpoly
  equation on its own, so the statement stays false; and the consumer
  needs the injectivity anyway — it is the `HilbertBlumenthalPoint`
  fields `ιO₀_injective`/`ιC_injective`, used again downstream at
  `KhareWintenberger.lean:3309`. Deleting it breaks the assembly without
  buying truth.
* *Add `IsDomain O`.* This does kill Counterexample 1, but it is an
  ad-hoc symptom patch — it asserts the conclusion one wanted about `O`
  instead of deriving it — and the consumer cannot supply it: the
  sibling's `O` is only known to be LOCAL, and `ℤ₁₃[ε]` is a local ring
  that is not a domain. So it is neither structural nor available.

Corroboration that `IsDomain` is precisely what is missing: the tree's
own PROVEN helper for producing such an embedding,
`exists_injective_ringHom_algebraicClosure_of_moduleFinite`
(`Modularity/KhareWintenberger.lean`), takes `[IsDomain O]`,
`[Algebra ℤ_[ℓ] O]`, `[Module.Finite ℤ_[ℓ] O]` and injectivity of
`algebraMap ℤ_[ℓ] O` as hypotheses — it factors through
`FractionRing O` and `IsAlgClosed.lift`, and there is no such
factorization without the domain hypothesis. This leaf ASSERTS the
existence of that embedding for an `O` about which it hypothesises
strictly less, which is how the clause got in.

### The repair (REPORTED, not made here)

Pin the frame to the real multiplication. Concretely, add to THIS leaf a
ring homomorphism together with the intertwining it must satisfy,

    (j : NumberField.RingOfIntegers D →+* O)
    (hj : ∀ (a : NumberField.RingOfIntegers D) (u : Fin 2 → O) (n : ℕ),
            (φ (j a • u)).1 n = m.act a ((φ u).1 n))

as further hypotheses of the innermost `∀`. This is exactly the
statement that `φ` is a frame of the Tate module AS AN `𝒪_D`-MODULE,
and it repairs both counterexamples at once: `j` forces `O` to contain
the image of `𝒪_D ⊗ ℤ_q` acting on `T`, which is `𝒪_{D,I}`, and the
rank count `rank_{ℤ_q} O = [𝒪_{D,I} : ℤ_q]` together with `𝒪_{D,I}`
being integrally closed then forces `O = 𝒪_{D,I}`. In particular `O` is
a domain of characteristic `0`, so `Function.Injective ι` becomes
automatic rather than an assumption smuggled into the conclusion, and
`τ.charFrob` becomes the reduced (rank-two over `𝒪_{D,I}`) Frobenius
polynomial, which is what Weil and Faltings are about.

Neither counterexample survives: `ℤ₁₃[ε] = ℤ₁₃[N]` admits no `j`,
because `j((1+√5)/2)` would have to act on `W` as the companion matrix
`α`, which generates the unramified quadratic `ℤ₁₃[α] ≠ ℤ₁₃[N]`; and
`ℤ₁₃ × ℤ₁₃` admits none either, because `𝒪_D` acts through the
`W`-factor and is therefore not scalar on either `e_iT`.

The seam therefore needs three coordinated edits, none of which is this
declaration's owner's to make alone:

1. `exists_tateFrame_of_levelStructure` must additionally PRODUCE `j`
   and `hj`. This is free for its author: it constructs
   `O = 𝒪_{D,I}` and `φ` from the `I`-adic Tate module, so `j` is the
   structural map.
2. This leaf takes `j`, `hj` as hypotheses (as displayed above).
3. `nonempty_hilbertBlumenthalPoint_of_isTwistedHilbertBlumenthalModuli`
   threads them through its two `obtain`s.

Until (1) lands, adding (2) alone would break (3), so the statement is
left untouched and the falsity is recorded here instead. The sibling
`exists_tateFrame_of_levelStructure` is NOT itself false — the honest
`I`-adic Tate module does frame it — it is merely too weak, and that
weakness is what this leaf inherited. -/
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
