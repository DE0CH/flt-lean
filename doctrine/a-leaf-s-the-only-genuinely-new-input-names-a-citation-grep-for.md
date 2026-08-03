## A LEAF'S "THE ONLY GENUINELY NEW INPUT" NAMES A CITATION — GREP FOR THE OBJECT, AND START WITH THE FILE THAT SUPPLIES THE LEAF'S OWN VOCABULARY
(2026-08-02, `flt-lean-337`, closing `exists_frobLift_conj_pow_mem_wildInertiaGroup`
in `HardlyRamified/HilbertModularity.lean` — cut two days earlier as a citation
leaf, PROVEN in ~120 lines with no new input at all.)
That leaf's `WHAT A PROVER MUST DO` section was a model of its kind: it named the
two halves of the classical argument, said which half was already in the tree
(injectivity of `μ_n → k̄ᵥ`, `eq_one_of_pow_eq_one_of_sub_one_mem_maximalIdeal`),
and identified the other as *"the only genuinely new input … the existence of a
Frobenius lift for the unramified quotient — Serre, Local Fields IV §2 and
Prop. 8; Neukirch, ANT II.9.9 and II.7.5."* Every clause was true except the word
**new**. The Frobenius lift was already in the tree:
    Field.AbsoluteGaloisGroup.adicArithFrob v : Γ Kᵥ
    Field.AbsoluteGaloisGroup.isArithFrobAt_adicArithFrob v
in `Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean` — **the very file
that defines `localInertiaGroup`**, i.e. the file supplying the leaf's own
vocabulary, upstream of everything it mentions.
**Why the search missed it, and this is the transferable part.** The audit
searched `ArtinConductor.lean` (the tame-quotient file) for the CITATION's
vocabulary — "unramified", "residue field", "Frobenius lift". The object is filed
under neither: it is `arithFrobAt'`, a wrapper around mathlib's
`Mathlib/RingTheory/Frobenius.lean`, whose surjectivity content is
`Ideal.Quotient.stabilizerHom_surjective_of_profinite` — the profinite-group form
of `Γ Kᵥ ↠ Gal(k̄ᵥ/kᵥ)`, with no local field and no "unramified" anywhere in its
statement. No amount of grepping for the theory finds it.
So, before writing or believing a "the only new input is X" clause:
* **list the OBJECTS the classical proof consumes** (here: an automorphism acting
  as `q`-th power on residues; and a root-of-unity injectivity), and grep the
  whole tree for each — by TYPE (`: Γ Kᵥ`, `→+* `), by the mathlib class that
  would carry it (`IsArithFrobAt`), and by the mathlib DIRECTORY it would live in;
* **read the declaration list of the module that defines the leaf's own
  vocabulary FIRST.** A leaf's statement is written in the words of one upstream
  module; that module is where its inputs were most likely already needed, and it
  is the one place an author who is thinking about the CITATION will not look.
**The standing local-Frobenius toolkit, so nobody re-derives it.** For any
statement about the local Galois group `Γ Kᵥ` of a number field at `v`:
* `Field.AbsoluteGaloisGroup.adicArithFrob v` and its
  `isArithFrobAt_adicArithFrob` — an arithmetic Frobenius, PROVEN to exist;
* `AlgHom.IsArithFrobAt.apply_of_pow_eq_one` (mathlib) — turns the defining
  CONGRUENCE into an EQUALITY `Fr ζ = ζ ^ q` on roots of unity whose order is
  invertible mod the ideal. This is where `μ_n ↪ k̄ᵥ` is really spent;
* `IsDedekindDomain.HeightOneSpectrum.natCard_under_maximalIdeal`
  (`CompletionTransport.lean`) — identifies the `IsArithFrobAt` exponent
  `Nat.card (𝒪ᵥ ⧸ Q.under 𝒪ᵥ)` with `Nat.card (𝓞 K ⧸ v.asIdeal)`. Without it
  every statement is about the wrong `q`;
* `Field.absoluteGaloisGroup.conj_mem_localInertiaGroup` (same file) — inertia is
  normal;
* `smul_eq_self_of_pow_eq_one_algebraicClosure` (`ArtinConductor.lean`) — inertia
  fixes `μ_n` for `n` prime to the residue characteristic;
* `IntegralClosure.coe_smul` (`rfl`) and `coe_pow_integralClosure` — the two
  coercion lemmas that get you between `Oᵥ` and `Kᵥᵃˡᵍ`; the `IntegralClosure`
  `def` barrier stops `push_cast` from finding them.
**And the proof shape, because it is the one a tame-quotient statement always
wants: work with RATIOS and let the ambiguity cancel.** The leaf quantifies over
every `X` with `X ^ n ∈ 𝒪ᵥ` — the family `tameFixingSubgroup` is defined by — so
there is no distinguished uniformiser and no normalisation available. Put
`ζ := (σ • X)/X` and `η := (Fr⁻¹ • X)/X`; both are `n`-th roots of unity because
`σ` and `Fr` fix `X ^ n ∈ 𝒪ᵥ`. Then
    Fr σ Fr⁻¹ • X = (Fr • η)(Fr • ζ)(Fr • X) = (Fr • ζ) · X
because `(Fr • η)(Fr • X) = Fr • (η · X) = Fr • (Fr⁻¹ • X) = X` — **the `η`
factor cancels against itself**, so nothing has to be known about how `Fr` acts on
`X` itself, only on roots of unity. That is what makes the group-theoretic form of
the tame relation cheap where the `θ`-character form is not, and it is worth
trying whenever a leaf's conclusion is invariant under scaling its subject by the
group the ambiguity lives in.
