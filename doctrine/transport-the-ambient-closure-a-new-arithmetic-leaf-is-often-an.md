## TRANSPORT THE AMBIENT CLOSURE — a "new arithmetic" leaf is often an existing theorem in the wrong `ℚ̄`

(2026-07-31, `flt-lean-24`, the sibling leaf
`isUnramifiedAt_of_localInertia_le_fixingSubgroup_muSubfield`.)

That leaf's own docstring prescribed a split: "at every `ℓ ≠ p` the absolute statement does
apply … only the place above `p` needs the genuinely relative argument." Following it produces a
proof plus a NEW SORRY LEAF for the `ℓ = p` case — which is what the rival cut on `merger` did
(`isUnramifiedAt_muSubfield_of_localInertia_at_p`, one consumer, still open).

No split is needed. `HardlyRamified/HilbertModularity.lean` already proves the RELATIVE
dictionary `isUnramifiedAt_of_hilbertInertiaTrivialAt` — inertia-trivial at `w` ⟹ unramified
above `w`, for a finite Galois subextension of any number field `F`, `p` included. The ONLY
obstruction was that it is stated inside Lean's canonical `AlgebraicClosure F`, whereas the
consumer's whole Galois dictionary (`Γℚ`, `ker χ`, `muSubfield p`) lives in `AlgebraicClosure ℚ`.
Two transports (now `NumberField/RelativeUnramifiedTransport.lean`, ~250 lines, sorry-free) close
the gap and the leaf becomes a 40-line assembly with NO new leaf:

* the dictionary along an `F`-isomorphism `ee : Fᵃˡᵍ ≃ₐ[F] Ω`, with its inertia hypothesis
  phrased as an equation in `Ω` so a consumer never mentions `Fᵃˡᵍ`;
* the group-side companion: a local inertia element of `F` at `w`, read through `ee`, IS a
  `Γ K`-conjugate `σ κ̃ σ⁻¹` of a local inertia element of the base `K`. That is what turns a
  `K`-level hypothesis into an `F`-level one, and it is the ALL-PLACES form of
  `GaloisRepTransport.lean`'s `exists_finset_conj_localInertiaGroup_le` — whose finite exceptional
  set is fatal here, because the excluded place is exactly the one the leaf exists to handle.
  Deleting the `S`/`T` bookkeeping from that proof is the whole of the new proof.

**So before believing a leaf needs arithmetic the tree does not have, ask whether the tree has it
in a DIFFERENT ALGEBRAIC CLOSURE.** This development runs three at once (`AlgebraicClosure ℚ`,
`AlgebraicClosure CF`, `AlgebraicClosure (muSubfield p)`) and a statement is not reusable across
them without an explicit `ee`. Keep `ee` a HYPOTHESIS rather than building `IsAlgClosure.equiv`
inside, for the reason recorded at
`NumberField.exists_unramifiedAbelian_of_algebraicClosureEquiv`: with it opaque, no defeq check
can try to unfold `IsAlgClosed.lift`.

**Two mechanical traps met on the way, both cheap once named.**

1. *A scratch module that `public import`s the target file does NOT see what the target sees.*
   `exists_prime_eq_toHeightOneSpectrumRingOfIntegersRat` is `unknown constant` in a scratch that
   imports `Modularity/Interface`, because `Interface.lean:426` imports `Threeadic`
   NON-publicly — visible inside `Interface`, not re-exported. **Copy the target's non-`public`
   imports into the scratch**, or you will "discover" that a constant the target file can cite
   does not exist.
2. *`Algebra ℚ ℚ_ℓ` has two live spellings*, `DivisionRing.toRatAlgebra` (what you get writing
   `algebraMap ℚ (v.adicCompletion ℚ)` in your own `have`) and
   `HeightOneSpectrum.instAlgebraAdicCompletion` (what the transport theorems carry). They are
   NOT defeq at default transparency, so `exact` fails with three instance arguments differing at
   once. The standing idiom, already all over `Threeadic.lean`, is one `Subsingleton.elim` plus
   `▸`:

       have halg : (IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
           (NumberField.RingOfIntegers ℚ) ℚ hℓ.toHeightOneSpectrumRingOfIntegersRat) =
           (DivisionRing.toRatAlgebra) := Subsingleton.elim _ _
       …
       exact halg ▸ hfin

**And the release-window check is worth running BEFORE the proof, not after** (it caught all
THREE of this task's targets, already proven on `merger` and invisible from `main`). It also
changes what the task is: with a rival cut in hand the question stops being "can I prove it" and
becomes **"which cut leaves fewer OPEN leaves"** — here mine leaves zero and `merger`'s leaves
one, so the right output is a `to_merger` note naming the leaf that becomes consumerless, not a
proof race. One command:

    git show merger:Fermat/FLT/Modularity/Interface.lean | grep -n -A3 '^theorem <name>'

