# X0.lean — fresh full census, measured 2026-07-31 on `merger` @ `1ead8a94`

Regenerated because `RELEASE-27-HANDOVER.md` says its log lived at `/tmp/v_X0b.log`
on **nightcrawler** and would not survive a reboot. This run was on **cyclops**, in
worktree `flt-lean-287`, against `merger` fast-forwarded, with the import cone built:

    lake env lean -DmaxErrors=800 Fermat/FLT/ModularCurve/X0.lean     # EXIT=1

**130 errors, 119 `declaration uses 'sorry'` warnings.**  The handover recorded 193
after release 27's round 2, so the three commits after it (`202634b2`, `98f0fd00`,
`9e7f6e4b`) took it 193 → 130.  Nothing here was fixed by this worktree: X0.lean is
untouched on branch `flt-lean-287`.

## 1. The SIX remaining parse errors — fix these first, they truncate

The handover's post-round-2 list was `80434, 80524, 80542, 82118, 82209, 82217,
95137, 97943`.  **`80434` and `82217` are gone; the other six remain, at the same
line numbers.**

| line | token | shape | repair |
|---|---|---|---|
| 80524 | `'*'` | orphaned docstring BODY — prose runs 80524‑80563 and is closed by an existing `-/` at 80563 | reopen at 80524 |
| 80542 | `'to'` | *same block* — it is one wound, not two | — |
| 82118 | `'/--'` | a `-/` at 82118:85 is immediately followed by `/--` at 82120: a docstring with **no declaration under it** | merge the two, or make the first `/-!` |
| 82209 | `'*'` | orphaned docstring BODY — prose runs 82209‑82249, closed by `-/` at 82249, and the next declaration starts at 82251 | reopen at 82209 |
| 95137 | `'('` | **TRUNCATED HEADER**, not a comment: `neronPt_comp`'s proof ends at 95136 and a foreign binder list `(_hthree : ∀ (K : Type) [Field K] …)` follows | interface reconciliation — needs the call sites, so an author's call, not a passer-by's |
| 97943 | `'#'` | a single stray markdown heading line `## OPEN FAITHFULNESS QUESTION: …` sitting immediately above the `/--` at 97944 | move it inside that docstring, or delete |

Five of the six are the orphaned-docstring shape the handover names; the sixth
(95137) is the truncated-header shape, and it is the only one that carries a
mathematical decision.

## 2. The 99xxx cluster is DOWNSTREAM of the 97943 parse error

`Unknown identifier 'pullback'`, `'pullback.fst'`, `'pullback.snd'`, `'pullback.lift'`,
`'pullback.condition'` all sit at **99782‑99924**, i.e. after the parse error at
97943, together with the tail of the `Function expected at` block (99879, 99914,
99916, 99924).  A parse error drops the enclosing `open … in` / `section … open
CategoryTheory.Limits` scope, which is exactly the failure mode the handover's
"Declaration order" note describes from the other direction.  **Expect a large part
of the semantic residue to evaporate when 97943 is fixed** — and expect NEW errors
to appear in the regions the six parse errors are currently hiding.  The count will
not fall monotonically.

## 3. Error census by class (130 total)

```
 40  Function expected at              (38247‑39424 and 99879‑99924)
 20  unsolved goals
  9  Tactic `rcases` failed             (all downstream of an Unknown identifier)
  9  Application type mismatch
  8  Ambiguous term                     (31360, 31373, 31474, 31479, 31571, 31585, …)
  6  don't know how to synthesize implicit argument
  6  parse errors                       (§1)
  5  No goals to be solved
  4  linarith failed
  3  (kernel) declaration has metavariables
  3  cannot coerce to sort
  2  Invalid projection                 (5047)
  2  (deterministic) timeout at whnf    — the declaration to bump is the one BELOW the reported line
  2  (deterministic) timeout at isDefEq
  2  Type mismatch
  1  unknown metavariable
```

44 `Unknown identifier`/`Unknown constant` occurrences.  The distinct names, which
are what a declaration-order or lost-`open` diagnosis keys on:

```
exists_gamma0Rigidification_of_rigidifiedModuli   exists_jSection
exists_nonConstant_qExpansion_gamma0GITPresentation
exists_nonconstant_toAbelianScheme_of_nontrivial_cuspForm
exists_pointwiseCommutingHeckeAlbaneseFamily
exists_relPointGroup_schemeTheoreticImage_of_isAdditiveOn
exists_surjectiveAbelianImage_of_isAdditiveOn     flat_of_surjective_of_isAdditiveOn
gres_add   hm   homogeneousSubmodule_zero
isReduced_isIntegrallyClosed_ringKrullDim_of_rigidifiedModuliData_specF
noFixedRationalPoint_atkinLehner_chabautySemiprimeLevel
nonempty_gamma0CurveAtlasOver_of_ringHom
pullback  pullback.condition  pullback.condition.symm  pullback.fst  pullback.lift
pullback.lift_fst  (…)
```

`hm` is a binder underscored in a signature while the body still uses it — the
`_foo`/`foo` shape CLAUDE.md's class-7 section describes, catchable by grep.

## 4. Consequence for anybody else building in this window

`lake` will happily report a green build of a module downstream of X0 while
serving a **stale `X0.olean`**: X0 has not built since release 25, so the olean on
disk predates it and lake replays the failure rather than the artifact.  Measured
here: `Fermat.IsReductionBase` in the served olean has only 8 of the ~14 lemmas its
source declares (`isUnit_of_ne_zero`, `two_le`, `mem_of_not_dvd_den`,
`exists_pow_mul_mem`, `isLocalization_away` are all absent).  So an agent working
downstream of X0 on `merger` must not treat "my scratch compiled" as evidence about
names added to X0 since 2026‑07‑29 — and should prefer, as `FormalImmersion.lean`
does, to derive what it needs from first principles rather than from X0's newer API.
