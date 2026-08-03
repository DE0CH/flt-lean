## THE SEVENTH CLASS HAS A DOCUMENTARY FORM: A MERGE CAN KEEP ONE BRANCH'S DOCSTRING AND THE OTHER'S STATEMENT
(Same task, and it is what dispatched the task.) The interface-split section above is about
two halves of *code*. The same merge boundary runs through the DOCSTRING, and there the
failure is worse, because **the loop writes task prompts out of docstrings**.
Two branches repaired one falsity — `AuxDeformationDatum.IsWeaklyUniversal` being
existence-only, so a received `𝒟Q` is unpinned and `𝒟Q.R := 𝒟Q⁰.R[[y_1, …, y_m]]` refutes any
bound on it — in two RIVAL ways: `flt-lean-247` made the leaf PRODUCE its datum out of a
guard `hwu`, and `flt-lean-69` kept the datum received and pinned it with
`hgenQ : IsTraceGeneratedDeformation`. The merge took **247's prose and 69's statement**. The
surviving paragraph then said, in the file, that the leaf "PRODUCES the datum rather than
receiving it" and that "what arrives here instead is the nonemptiness guard `hwu`" — a
signature that exists on one branch and in no tree.
My task prompt was generated from that paragraph, verbatim, down to the `hwu` binder and a
`# FALSITY AUDIT (2026-07-31)` heading that is not in the file. **Every freshness check
passed**: the leaf name was real, the file was real, the worktree was current after one
`git merge --ff-only main`, and the `merger` check confirmed the name was there. Only reading
the STATEMENT next to the prose showed the prompt described nothing.
Three things follow:
* **A docstring is not evidence about the statement three lines below it.** This file already
  says an audit can be stale about the tree; a docstring can be stale about *its own
  declaration*, and a merge is how that happens without anyone writing a false sentence.
* **When two branches repair one falsity, ask whether the repairs are RIVALS or
  COMPLEMENTS before taking either half of either.** These were rivals: each pins `𝒟Q`
  independently, and the union is not the repair (cf. the duplicated-hypothesis failure in
  the ninety-branch section). Record in the docstring WHICH pin the tree took and why, or
  the next reader gets to choose at random.
* **If your prompt's binder list does not match the file, the prompt is the stale one.** The
  existing rule reads line numbers as a checksum on your checkout; a SIGNATURE is a checksum
  on your prompt. Diff them before writing any Lean — it is one `sed` and it is the whole
  difference between a proof and a phantom.
### The follow-up: neither the localisation NOR the re-presentation was needed
(2026-07-31, `exists_pow_X7_mul_mem_idl`, the first half of that cut, now PROVEN.) The plan above
is right about the mathematics and wrong about the cost, in a way worth generalising: **it named
two expensive objects — a localisation and a structural isomorphism `MvPolynomial (Fin n) ≃ E[T]` —
and the proof needed neither.** Both were replaced by one cheap gadget.
**Use the INJECTION `R ↪ R[T]`, not the isomorphism `R ≃ E[T]`.** To see a `MvPolynomial (Fin n) ℤ`
as a polynomial ring in one chosen variable `X k`, do not peel `X k` off into an `n−1`-variable base
ring. Map `X k ↦ T` and every *other* `X i ↦ C (X i)`, **landing in `R[T]` over `R` itself**:
    noncomputable def peel (k : Fin n) : R →ₐ[ℤ] Polynomial R :=
      aeval (fun i => if i = k then Polynomial.X else Polynomial.C (X i))
This is not surjective, so it is not the structural iso — but it is injective with an explicit
retraction (`Polynomial.eval (X k)`), and it costs nothing:
- **no second index convention.** The `Fin (n−1)` version renumbers every variable above `k`, so
  each polynomial must be transcribed twice and the two copies kept in sync by hand. Here
  `peel k p = C p` *literally*, for any `p` written in the `X i, i ≠ k`, by `simp`.
- **"`X k` does not occur in `p`" becomes `peel k p = C p`** — an `AlgHom.equalizer`, i.e. a
  subalgebra, so closure under `+ - * ^` is free rather than eleven lemmas.
- **degree-in-`X k` arguments work unchanged**, because `Polynomial R` is a domain when `R` is:
  "an `X k`-free multiple of something of degree exactly 1 in `X k` is 0" is `natDegree_mul`.
The one thing to know before committing to it: **irreducibility does NOT transfer back along a
non-surjection, but primality DOES.** From `peel k p ∣ peel k a`, apply the retraction to get
`p ∣ a`; that gives `Prime (peel k p) → Prime p` directly. So prove `Irreducible` upstairs in
`R[T]` (via `irreducible_C_mul_X_add_C`), upgrade to `Prime` upstairs (UFD), and only then come
down. Anything quantifying over *all* of `R[T]` will not come down.
**And "invert `f`'s leading coefficient" can be done by hand, keeping the cofactor.** Localisation
was only ever wanted to divide by `-Pz ^ 3`, the `a₆`-coefficient of `gen₁`. Instead prove
"for every `a` there are `n` and an `a₆`-free `r` with `Pz ^ n * a ≡ r (mod gen₁)`" by
`MvPolynomial.induction_on` — three cases, the `X k` step being one `ring` — and the `∃ n` in the
leaf's own statement absorbs the powers. **A leaf already stated in saturated form
(`∃ n, Pz ^ n * a ∈ I`) is telling you that no localisation object is required.** Read the
statement before building the machine.
**Last, and it removed every remaining computation: prove `¬ p ∣ q` by evaluating at ONE integer
point** where `p` vanishes and `q` does not (`p ∣ q → eval pt p ∣ eval pt q → 0 ∣ nonzero`). All
four primitivity non-divisibilities went this way, each a two-line `norm_num`. The CAS work quoted
in the plan (generic-point substitutions, `factorize`, `minAssGTZ`) was still worth doing — but its
output is *where to look for the point*, never anything transcribed into Lean. That is the CAS
doctrine's "untrusted searcher" in its cheapest possible form: the certificate is a point.
