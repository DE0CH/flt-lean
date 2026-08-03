## "THIS ENDOMORPHISM ACTS TRIVIALLY ON `E[n]`" IS A GALOIS-CENTRALIZER FACT, NOT A CM FACT
(2026-08-01, `flt-lean-170`, recutting `two_torsion_add_cmSqrtEnd_of_mem_isolatedCMJInvariants`
in `ModularCurve/X0.lean`.)
That leaf asked for `√−p ≡ 1` on `E[2]`, and both its own docstring and the subsection
above it identified the content correctly and expensively: it is exactly *the CM order is
the MAXIMAL order `O_{−p}` and not the conductor-`2` order `ℤ[√−p]`*, which is
`[ℚ(j(E)) : ℚ] = h(disc End)` — the first main theorem of complex multiplication — together
with `qfbclassno(−4p) = 3`. None of that is in this tree, and the leaf had sat there on
that basis.
**The same conclusion follows from two facts that know nothing about orders**, and the
shape generalises to any "endomorphism `α` acts as a scalar on `E[n]`" leaf:
1. **`α` COMMUTES WITH GALOIS ON `E[n]`.** For `E/ℚ` and `α` an ISOGENY satisfying a monic
   quadratic over `ℤ`, the differential character `λ : End(E_ℚ̄) → ℚ̄` — injective, and
   Galois-equivariant because the invariant differential is defined over `ℚ` — forces
   `σ α σ⁻¹` to be a root of the SAME quadratic, hence one of `α`'s two conjugates. On the
   `n`-torsion the ambiguity usually collapses: at `n = 2`, `−X = X`, so BOTH branches say
   `α` commutes with `σ`.
2. **THE CENTRALIZER OF THE MOD-`n` GALOIS IMAGE IS SMALL.** `Aut(E[2])` is `Sym(3)` on the
   three nonzero points, and an involution commuting with a `3`-cycle is the identity. So
   `α² = 1` on `E[2]` plus one `3`-cycle in the image pins `α = 1`.
and a `3`-cycle in the mod-`2` image is exactly **irreducibility of the `2`-division
polynomial**, i.e. *`E` has no rational point of order `2`* — a finite computation on `j`,
since for `j ∉ {0, 1728}` every curve with that `j` is a quadratic twist and twisting by `d`
scales the roots of the cubic by `d`, leaving its splitting field alone.
Net: leaf `1 → 1`, and what is LEFT went from the first main theorem of CM to *the cubic
`X³ + 3j(1728−j)X + 2j(1728−j)²` is irreducible at five explicit `j`* — checkable by
reduction mod a small prime (`5, 5, 11, 17, 41` respectively), so nobody has to factor a
`10⁵²` constant term.
**Three things worth reusing beyond the instance.**
* **A PROVEN Galois-conjugation lemma transcribes to a different quadratic mechanically.**
  `galoisConj_cmEndomorphism` (for `φ`, `X² − X + (p+1)/4`) could not be cited: it is 700
  lines BELOW and is about the wrong element. Copying its proof with the quadratic changed
  to `X² + p`, and the "some `σ` actually moves `c`" half DELETED, was ~90 lines and
  compiled first try. **When a lemma is unusable for declaration-order reasons, check
  whether its PROOF is generic in the thing you need to vary** — here every step was, and
  the whole `IsDiffChar` API (`exists_isDiffChar`, `isDiffChar_comp/_neg/_add/_mulByHom`,
  `isDiffChar_unique`, `eq_of_isDiffChar`, `isDiffChar_galConj`, `velu_point_map_symm_map`)
  is stated for an arbitrary isogeny.
* **CHECK THE RECUT AGAINST THE OLD LEAF'S OWN FALSITY WITNESS.** The old audit exhibited
  curves with CM by `ℤ[√−p]` on which the conclusion fails. On those, `ℤ[√−p]/2 =
  𝔽₂[t]/(t+1)²` is not a field, `√−p` acts as the nonidentity unipotent, its centralizer in
  `Sym(3)` has order `2`, and **no `3`-cycle can occur** — so the new leaf fails on exactly
  the curves the old audit names. Agreement of that kind is what shows a recut did not
  quietly weaken the hypothesis; disagreement means one half is false.
* **`p ≡ 3 mod 8` at all five is not a coincidence and is the conceptual check**: `2` is
  then INERT, `O_K/2 = 𝔽₄` is a FIELD, and `x² = 1` there forces `x = 1`. That is the same
  statement as the centralizer argument, and it is the fastest way to convince yourself the
  leaf is true before formalising anything.
### Two Lean traps met on the way, both in the standing "printed types are identical" family
* **`(E⁄K).Point` and `((E.map (algebraMap ℚ K))⁄K).Point` are DEFEQ AND NOT SYNTACTICALLY
  EQUAL**, which is unavoidable as soon as you touch `WeierstrassCurve.nTorsion` (defined
  as `Submodule.torsionBy ℤ (E⁄k).Point n` for `E` over its OWN field) from a file whose
  points are the base change from `ℚ`. A term crosses by `exact`; `simpa … using` does not,
  and reports two character-identical types. Two cures, both used here: a one-line
  `have cast' : ∀ {X Y : (E⁄K).Point}, @Eq ((E.map _)⁄K).Point X Y → X = Y := fun h => h`,
  and — where the mismatch is in a NUMERAL's instance path (`0`) rather than in a variable —
  a `show` at the *other* type before the `simpa`. The `0` case is the one that fails after
  the variable cases already pass, so do not read the first three successes as evidence.
* **`set S := …` makes every later `rw` about `S` fail**, exactly as the standing rule says.
  The fix that worked is `obtain ⟨S, hSdef⟩ : ∃ S : … →+ …, S = <the map> := ⟨_, rfl⟩`: `S`
  is then a genuine free variable, `map_add`/`map_zero` apply to it directly, and `rw
  [hSdef]` unfolds it exactly where a lemma about the concrete map is needed. For a Galois
  action on points this is strictly better than `set`, because `Point.map σ` already IS an
  `AddMonoidHom` and the `obtain` keeps it one.
Also: `mul_nsmul` at this pin is `(m * n) • a = n • m • a` — note the ORDER — so
`(2 * k) • T = k • (2 • T)` needs no `mul_comm`, and inserting one sends you to
`2 • k • T` and a `rw` that cannot find `2 • T`.
