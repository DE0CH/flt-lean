## A FROZEN `main` ROTS THE QUEUE SILENTLY — AUDIT queue1 AGAINST `merger`, NOT AGAINST `main`

(2026-07-31, release 32.  Measured: **48 of 265 queue1 tasks, 18%, named a leaf
that `merger` had already PROVEN**, plus 10 naming no open leaf at all.)

Every release the loop refuses to publish is a release in which `main` does not
move.  That is the correct outcome and it has a cost nobody had priced: because
`main` does not move, `queue1`'s `AUDITED: <main sha>` stamp stays valid, the
loop's `audit_current` guard keeps passing, and dispatch keeps running — off a
task list that has not been re-audited since the last PUBLISHED release.
Meanwhile the fleet keeps proving things, and every leaf it closes lands on
`merger` and turns one queue entry into a guaranteed wasted agent-run.

Five consecutive holds took that to nearly one dispatch in five.

**The audit that works is against the tree the fleet's work actually lands in.**
It is one script and it needs no build:

    python3 tools/merge/frontier.py --root . > /tmp/frontier-merger.tsv   # YOUR merger tree
    # then, per task, tokenise (isalnum plus _ and ') and keep it iff it names
    # a short name still in that frontier

Three things about doing it:

* **Tokenise unicode-safely.** A `[A-Za-z_][A-Za-z0-9_.']*` regex misses every
  name containing `ι`, `Ψ`, `₁`; splitting on "not `isalnum()` and not `_ '`"
  does not.  Do NOT use an `À-￿` character class — it swallows `⟨⟩←▸`
  ([[lean-identifier-regex-swallows-brackets]]).
* **Match on the SHORT name** (last dotted component).  Rows used to need a
  trailing dot stripped as well — declarations with explicit universe parameters
  came out as `foo.`, so `split('.')[-1]` was the empty string and matched
  everything.  **`frontier.py` now normalises that at source (2026-08-02), so
  the workaround is no longer needed**; see the section below for why fixing it
  in the scanner beat fixing it in each consumer.
* **The stamp must stay equal to `main`.**  `flt_loop_rows.py`'s `r15_guard`
  refuses to dispatch at all when `queue1` is not `AUDITED` at main, so under a
  hold you keep the old sha verbatim.  The stamp says which MAIN the queue was
  audited against; it does not, and cannot, say the tasks are still live.  That
  is the hole this section is about.
* **Re-read both queues immediately before writing, and write with
  `os.replace`.**  The loop pops tasks every ten seconds; a read-modify-write
  with a wide window resurrects whatever it popped.

Do the coverage arithmetic the same way — frontier minus (queue ∪ leaves live
agents hold) — and expect exactly one residual, `<no-enclosing-decl>` in
`Fermat/SorryGate.lean`, whose `elab` contains the token inside a STRING
LITERAL.  Any scan that does not special-case that file is off by one.

