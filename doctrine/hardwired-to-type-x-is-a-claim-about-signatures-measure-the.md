## "HARDWIRED TO TYPE `X`" IS A CLAIM ABOUT SIGNATURES — MEASURE THE **SPINE**, AND THE PROOFS USUALLY DO NOT CARE
(2026-08-01, `flt-lean-186`. A standing obstruction that four docstrings in two
files had priced as "a mechanical but large edit that belongs to that file's
owners" turned out to be a signature substitution in which **not one proof
changed**, and it closed `zmodIdealSymbol_eq_one_of_mk0_eq_one_three`.)
`ModThree.lean` carries a Childress-following Artin-reciprocity development whose
character is valued in `Dickson.K 3 = 𝔽̄₃`. Because `𝔽̄₃` has characteristic `3`, the
chain carries `hℓ3 : ℓ ≠ 3` and is unusable at `ℓ = 3` — and that is REAL, not an
artefact: at `ℓ = 3` the hypothesis `∀ a, χ a ^ (3 ^ k) = 1` forces `χ ≡ 1`, so no
injective `Multiplicative (ZMod (3 ^ k)) →* 𝔽̄₃` exists. Every docstring that
mentioned it said "price generalizing that value group", and the price on record was
**"~116 declarations, `Dickson.K 3` in ~340 signatures"**.
**The real number is the SPINE, and it was 31 declarations plus 2 in one other file.**
The gap is not sloppiness: `grep -c 'Dickson.K 3'` over the file returns 603, the
`_ray_class` cluster accounts for 308 of them, and the transitive dependencies of the
theorem you actually consume account for 137. **Cluster ≠ cone.** Compute the cone.
**The four measurements that decide such a generalisation, in the order that kills it
fastest, all of them minutes:**
1. **The spine.** Comment-strip, attribute each line to its enclosing declaration,
   tokenise with `isalnum() or c in "_'."` (never a unicode range —
   [[lean-identifier-regex-swallows-brackets]]), and take the transitive closure of
   the top theorem's uses. Intersect with "mentions the type". Here 140 in-file
   dependencies, of which **31** mention `Dickson.K 3`.
2. **Does any spine proof use a PROPERTY of the type?** Grep the spine bodies for
   `IsAlgClosed`, `CharP`, `ringChar`, `ZMod`, `Fintype`, and for `<Namespace>.<other>`
   lemmas about it. Here: **zero**. The characters are turned into homomorphisms into
   `Kˣ`, their images are finite subgroups of a field's unit group (cyclic over ANY
   field), and every root of unity the argument manipulates lives in
   `AlgebraicClosure F`, i.e. in characteristic zero — never in the value field. The
   one genuinely characteristic-`3` declaration of the cluster
   (`exists_forall_pow_eq_one_ray_class`, which strips the `3`-part of an exponent) was
   NOT in the spine and was left alone.
3. **Cross-file dependencies of the spine that mention the type.** Here exactly ONE,
   in a 395-line file.
4. **External CODE references to the spine** — comment-stripped, because in this tree
   a `grep -rl` over a spine name returns a dozen files of which all but one are
   docstrings. Here **one**, and it is the sibling leaf. That number is what decides
   whether you need the "keep the old statement as a WRAPPER" dance at all; at one
   site you just fix the site.
**THE TRAP IN MEASUREMENT 4, AND IT REPORTS THE ANSWER YOU WANT.** A word-boundary
regex written as `(?<![A-Za-z0-9_.\'])NAME(?![A-Za-z0-9_\'])` excludes a preceding
DOT — and a cross-file reference in this project is *always* qualified
(`GaloisRepresentation.IsHardlyRamified.exists_…`). So that regex reported **zero**
external code references for all 31 names, including one I already knew existed.
Drop `.` from the lookbehind. A scan that under-reports is worse than no scan,
because it certifies.
**THE HYPOTHESIS IS THE OTHER HALF, AND IT IS USUALLY A NAME FOR A PROPERTY OF THE
PARAMETER YOU ARE INTRODUCING.** `hℓ3 : ℓ ≠ 3` was never a statement about `ℓ`: over
`𝔽̄₃` it is exactly `((ℓ : ℕ) : 𝔽̄₃) ≠ 0`, the condition under which the value field
contains a primitive `ℓ ^ k`-th root of unity. Rewriting it as
`hℓchar : ((ℓ : ℕ) : KK) ≠ 0` is not a weakening and not a strengthening — it is the
same hypothesis, said in terms that survive the generalisation. **When a threaded
hypothesis is never consumed by any proof, ask what it MEANS about the object you are
abstracting; that is its general form.** Keep it rather than deleting it: it costs a
prover nothing, every consumer supplies it, and deleting it makes the leaf cover the
degenerate case `char KK = ℓ` where the statement is vacuous.
Two riders, both of which cost nothing once the above is measured.
* **Give the old callers a one-line bridge instead of restating anything.** One lemma
  (`natCast_ne_zero_dicksonThree_ray_class : ℓ.Prime → ℓ ≠ 3 → ((ℓ : ℕ) : Dickson.K 3) ≠ 0`)
  discharged the new hypothesis at every un-generalised call site, so the `_ramified_`
  family of the same cluster kept its `𝔽̄₃` signatures and did not move.
* **Restating a `sorry` leaf VOIDS its audit even when the restatement is "only" a type
  parameter.** Two of the generalised declarations are open leaves; both got a fresh
  audit in their own docstring, and the argument to write is *which of the statement's
  clauses can see the parameter at all*. Here neither can: the first depends on the
  character only through `ker χ`, and the second is the norm-index inequality, every
  object of which lives over the number field.
**Report the accounting exactly.** `ModThree`+`NormIndex` sorry set 15 → 15 (identical
declarations, shifted by the inserted helper); `Interface.lean` **16 → 15**, the
missing one being the target. Net −1, no new leaf anywhere. And say the debt moved
rather than closed: the chain is still transitively sorried over the ray-class
cluster, which is what the sibling's docstring says and what this one now says too.
