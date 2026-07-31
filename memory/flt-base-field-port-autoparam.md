---
name: flt-base-field-port-autoparam
description: Generalising a ℚ-only development to an arbitrary base field in place — the free-over-ℚ fact becomes an autoParam hypothesis, and the morphism usually determines the base
metadata:
  type: project
---

Porting `EllipticScheme.lean`'s `ProjCoords` cluster from `ℚ` to `F : Type u`
(2026-07-31) turned two things that looked like the cost of the job into
non-problems.

**1. A fact that is FREE over `ℚ` becomes an `autoParam`, not a new argument at
every call site.** `ProjCoords.base_eq` (`ℚ →+* A` is a subsingleton) was used
implicitly by `add`, `add2`, `ext`, and by 58 `hom_ext_spec_rat` invocations.
Writing

    (hb : c.base = d.base := by exact Subsingleton.elim _ _)

as the LAST binder leaves **every existing `ℚ` call site byte-identical** — the
tactic fires and finds `Rat.subsingleton_ringHom` — while a general-`F` caller
gets a hard error until it supplies the proof. That is exactly the wanted
behaviour: the port is opt-in per call site and `ℚ` never regresses. Two
caveats: a `@[simp]` projection lemma about the autoParam'd definition must take
the hypothesis as an explicit anonymous binder (`(h) (hb)`), because its own
statement is elaborated at `F` where the tactic fails; and proof irrelevance is
what makes `rw`/`exact` still match a goal whose proof term came from the
tactic rather than from the caller.

**2. Ask whether the DATA is recoverable from the morphism before threading it.**
`hom_ext_spec_rat` ("a scheme has at most one map to `Spec ℚ`") is false over
`F`, and its 58 uses all sit in the same position: the commuting square of
`Limits.pullback.lift c.toHom d.toHom _`. The honest replacement is one lemma,
`c.toHom ≫ projToSpec E = X.toSpecΓ ≫ Spec.map (ofHom c.base)`, which is
mathlib's `Proj.fromOfGlobalSections_toSpecZero` plus "`ringHom` evaluates a
constant to itself". And its **converse** is what makes the port cheap:
`Γ ⊣ Spec` is an adjunction, so `base_eq_of_toHom_eq : c.toHom = d.toHom →
c.base = d.base` holds — every rigidity/congruence lemma that already knew the
two morphisms agree needs NO new hypothesis at all. See
[[flt-cut-leftovers-close-sibling-leaves]] for the same shape one level up.

**3. For a pervasive edit inside a monolith, the scratch module is a truncated
PREFIX of the same file, not a small import.** CLAUDE.md's throughput rule says
develop against a throwaway module importing only what you need; that assumes
the new code is separable. When the edit is spread over 3 000 lines of a
12 686-line file, the equivalent is `lines[:N] + the closing end`s` written to
`ScratchN.lean` — same imports, a quarter of the elaboration. Iterating on two
lemmas that way cost 60 s per round against >10 min for the whole file. Delete
the scratch before committing: a module under `Fermat/` that nothing imports is
CLAUDE.md's fourth invisibility class.

Measured: the clean 12 686-line file elaborates in **72 s**; the same file with
a dozen errors ran past **10 minutes**. Error recovery, not size, is what makes
a broken monolith slow — so never price the next round off the last one.
