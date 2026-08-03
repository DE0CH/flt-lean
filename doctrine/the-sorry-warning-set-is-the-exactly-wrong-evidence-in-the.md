## THE `sorry`-WARNING SET IS THE EXACTLY-WRONG EVIDENCE IN THE RELEASE WINDOW

(2026-07-31, `flt-lean-235`. The release-window section above already prescribes the check that
would have caught this; this is a note on WHY an agent following the rest of this file skips it.)

Three leaves were dispatched. I fast-forwarded to `main`, ran `lake build` on the module, and read
the `declaration uses 'sorry'` warning set: all three target line numbers were in it — `42221`,
`53124`, `53285` — matching the task prompt exactly. That is the compiler speaking, and this file
says in bold that **the compiler is the only reliable ownership evidence**. So I started work.

**All three were already PROVEN on `merger`**, over a new file
`Fermat/FLT/NumberField/CyclotomicIdealSymbol.lean` that does not exist on `main` at all. I spent
the run rebuilding a strictly weaker version of one of them, and it had to be thrown away.

The two rules are in tension and the tension is not marked:

- *"Prefer the compiler to any prose claim about what is still open"* is about **`main` being
  wrong in the direction of claiming a leaf is CLOSED** — a stale docstring, a commit message, an
  agent's report.
- The **release window** is `main` being wrong in the other direction: a leaf that is closed on an
  unmerged branch is still `sorry` on `main`, so the warning set lists it, **truthfully and
  uselessly**. A green build cannot see work that has not merged, and by construction the work you
  are being dispatched at is the work most likely to be in flight.

So: **a build tells you the state of the tree you built, and the tree you built is `main`.** For
"is this leaf still open" that is not an answer. Run, before the first edit and before trusting any
line number:

    git show merger:<the file> | grep -n '^theorem <name>'   # then read the body: `sorry` or not?

and check `~/.flt-loop/queue2` / `~/.flt-merge-batch` for branches touching the same file. One
command, ten seconds, ahead of a multi-hour build.

Two smaller traps met on the way, both worth avoiding:

- **Do not `awk` for `/^theorem |^\/--/` to find where a declaration's body ends.** Statements in
  this development run to a hundred lines and the naive scan reports "not sorry" for a sorried leaf
  and vice versa. Locate the `^theorem <name>` line, then print forward and READ it.
- **A superseded branch is worse than an empty one.** My version proved the same theorem over ONE
  large leaf; `merger`'s proves it over FIVE small ones plus a reusable ideal-symbol lemma. Merging
  mine would have cost a conflict resolution and risked replacing the better proof with the worse.
  When your work is superseded rather than partial, **revert the Lean change** and report it —
  the value left is the report, not the code.

