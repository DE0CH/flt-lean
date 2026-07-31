---
name: flt-consumer-supplies-the-missing-stability
description: When a general theorem walls on a missing "the property is stable under localization/base change" step, check whether the actual consumer's objects supply that stability directly — usually they do, and the wall costs nothing
metadata:
  type: feedback
---

A general commutative-algebra theorem often walls not on its own mathematics but on a
missing **stability** lemma: *the hypothesis class is closed under localization / quotient /
base change*. Before reporting the wall, check what the CONSUMER actually holds — it very
often supplies the stability for free, in which case the general theorem is unreachable and
every consumer of it is nevertheless unblocked.

Worked instance (2026-07-31, `Fermat/FLT/Mathlib/RingTheory/RegularLocalNormal.lean`).
`IsRegularLocalRing R → IsIntegrallyClosed R` is genuinely blocked at this mathlib pin: the
induction on embedding dimension needs `R_p` regular local for `p < 𝔪`, i.e. it needs
`IsRegularLocalRing R → IsRegularRing R` — **mathlib's own recorded TODO** in
`RingTheory/RegularLocalRing/Defs.lean`, and a real homological theorem (regular ⟺ finite
global dimension). All three classical routes around it are also absent: no Krull domains
(`grep -rl KrullDomain Mathlib/` empty), no Cohen–Macaulay hence no Serre `R1+S2`
(`grep -rl CohenMacaulay Mathlib/` empty), no Auslander–Buchsbaum, no Cohen structure theorem.

But the consumer holds a stalk of a SMOOTH scheme, and there the stability is a triviality:
a localization at a prime of `T_q` is a localization at a prime of the SAME smooth algebra
`T`, so `isRegularLocalRing_stalk_of_smooth_over_field` applies again at a different point of
`Spec T` — never to a localization of a localization. So state the theorem over
`[IsRegularRing R] [IsLocalRing R]`, prove `Algebra.Smooth → IsRegularRing` of the
localization, and the geometric corollaries come out **unconditional**.

**Why:** "the general statement is out of reach" and "my task is out of reach" are different
claims, and conflating them turns a completed task into a reported wall. The stability step
is also the right thing to name in the report: it is one theorem, in mathlib's own terms,
that would upgrade the file with no further work here.

**How to apply:** when an induction/localization step is the blocker, write the theorem over
the *closure* hypothesis (`IsRegularRing`, `IsRegularRing`-like, "…and all its localizations"),
then discharge that hypothesis separately for the class the consumer actually has. Related:
[[flt-inventory-audits-understate-what-exists]], [[audit-searched-production-not-invariant]].
