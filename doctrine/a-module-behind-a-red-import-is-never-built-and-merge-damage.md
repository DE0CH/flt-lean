## A MODULE BEHIND A RED IMPORT IS NEVER BUILT, AND MERGE DAMAGE ACCUMULATES IN IT SILENTLY — AND THE BALANCE SCAN CAN REPORT IT CLEAN
(2026-07-31, `flt-lean-47`, on `merger` at `1ead8a94`.) Release 27's handover
states *"Every module except `ModularCurve/X0.lean` builds"*, and lists nine X0
wounds repaired. That sentence is FALSE, and its falsity is structural rather
than careless: `Modularity/Interface.lean` `public import`s `X0`, so **it has
not been built since release 25 either** — and neither has anything else behind
X0. A release build stops at the first failing module in dependency order, so
"everything else builds" is a statement about what lake *reached*, never about
what is *sound*.
What was in there: `Interface.lean` had **41 600 lines inside one block
comment**. A docstring at line 39911 lost its closing delimiter *and* its
declaration in the merge that created `merger`; a stray closer 41 600 lines
below (left by the *other* half of the same class of wound, a truncated
pre-rename header `pow_dvd_log_valuation_of_exists_fixed_rootOfUnity_of_not_
forall_commute_localInertia` with no signature) closed it. Everything between
was prose to Lean.
**THE STANDING COMMENT-BALANCE SCAN REPORTED THE FILE CLEAN**, because the two
wounds are of opposite sign and cancel: `depth = 0`, `strays = []`. That is the
same layering the memory note [[flt-comment-wounds-are-layered]] records, in its
worst form — the check that is supposed to find this class is the check that
certifies the file. The scan is still worth running (it found the wound the
moment I merged `merger` into a `main`-based branch, because the merge broke the
cancellation), but **a clean balance is not evidence.** What IS evidence, and
costs one pass:
* trace the depth AT the line of a declaration you expect to be code. If
  `depth > 0` there, that declaration does not exist as far as Lean is
  concerned, however ordinary it looks in an editor;
* scan for a `theorem`/`lemma`/`def` line with NO signature after it — the
  truncated-header shape — over comment-MASKED source;
* and note that both shapes are invisible to `git diff`, to conflict markers, to
  the duplicate-declaration scan and to `verify_added.py`, because no
  declaration is added, removed or renamed. Only the comment structure moved.
Two riders, both of which cost a round here. **Do not write a comment delimiter
inside a comment** — a repair note containing a backticked opener or closer in
prose re-breaks the file, silently and in either direction (a backticked opener
swallows the rest; a backticked closer ends the comment early). And when you
delete an orphaned docstring, first check whether the declaration it documents
was DECLINED rather than lost: here the leaf
`isUnramifiedAt_muSubfield_of_localInertia_at_p` really is gone on purpose,
because its consumer was proven outright by a rival cut, so restoring it would
have been free-floating. Keep the prose as a plain block comment with a header
saying which, and say why.
