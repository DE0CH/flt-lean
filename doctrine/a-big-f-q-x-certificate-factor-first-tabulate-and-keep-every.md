## A BIG `F_q[X]` CERTIFICATE: FACTOR FIRST, TABULATE, AND KEEP EVERY COEFFICIENT POSITIVE

(2026-07-31, all three measured while proving `dvd_X_pow_card_pow_sub_X_hPolyElevenA`,
`H ∣ X ^ (23 ^ 11) - X` for a degree-`55` `H` over `ZMod 23`. The whole file is 159 s green;
the route its own cut docstring prescribed would have been ~40 minutes and RED.)

`ring` over `ZMod p` is the only tool for these, so the single thing that matters is how big
each identity is. Three levers, in decreasing order of payoff:

1. **FACTOR `H` FIRST.** A Frobenius table for a degree-`d` modulus costs `O(d²)` per entry
   and needs `d` entries, so it is CUBIC in `d`. Splitting `55` into five `11`s cut the work
   ~5×. `polisirreducible` in PARI hands you the factors; you never have to prove them
   irreducible — recombine with ten explicit Bézout `IsCoprime` certificates and
   `IsCoprime.mul_dvd`, which are ~264 monomial ops apiece and free by comparison.
2. **TABULATE, NEVER DIVIDE BIG.** The naive step `p ^ 23 - p' = h * q` has `deg q = 196`:
   **46 s for ONE such identity, and `ring_nf; reduce_mod_char` does not even close it.**
   Precompute `u i := (X ^ 23) ^ i mod h` for `i ≤ deg h`, then decompose each step as
   `p ^ 23 - p' = ∑ c i * (X ^ (23 * i) - u i)`. Every identity is then of degree `≤ 21`:
   **0.8 s.** What makes this legal is that over `ZMod p` the Frobenius is LINEAR —
   `f ^ p = f.comp (X ^ p)`, from `Polynomial.map_frobenius_expand` plus
   `ZMod.frobenius_zmod` (note `Polynomial.expand_char` is DEPRECATED in this pin; the live
   name is `map_frobenius_expand`).
3. **STATE THE WITNESS ALL-POSITIVE.** `reduce_mod_char` rewrites `-1` to `22` and then
   leaves an unnormalised `22 * (X ^ 2 * 6)` sitting in the goal, which `ring_nf` has already
   run past — the identity is TRUE and the tactic block fails anyway. Do not chase it with
   more `ring_nf; reduce_mod_char` rounds; remove the minus sign instead. `rw
   [sub_eq_iff_eq_add]` turns the `Dvd` witness goal `A - B = h * q` into `A = h * q + B`,
   after which no negative coefficient exists to be mangled.

Two smaller notes. `Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X` is the converse
direction and already in the pin. And GENERATE the file from a script that re-derives every
certificate in a second, independent implementation of `F_q[X]` arithmetic and asserts each
identity before emitting it — every one of the ~2300 lines here was checked in Python before
Lean ever saw it, which is why the first full build had zero errors.

### MEASURED at degree `34`: ~14 min wall per factor, 9.3 GB — the `p = 17` rows ARE affordable

(2026-07-31, `flt-lean-343`, `ZMod 67`, one degree-`34` irreducible factor of the `p = 17`
row's `H`, `m = 34`, elaborated twice on an otherwise-busy `quicksilver`:)

    WALL=987 s
    WALL=829 s   CPU=6989 user + 7013 sys = 14 002 s   MAXRSS=9.3 GB   EXIT=0

Against the whole `p = 11` file — five factors of degree `11`, `m = 11` — at **159 s** idle
and **578 s** under fleet load, that is a per-factor wall blow-up of roughly **7–26×**, well
under the **~90×** that the cost model predicts (`O(d²)` per table entry × `d` entries × `m`
steps is cubic in `deg h`, linear in `m`; `(34/11)³ × (34/11) ≈ 90`). The parallel elaborator
absorbs the rest — see the correction below. **So a `p = 17` row is four factor-blocks at
~14 min each, and both rows are a job of hours, not days.** What to watch is not time but
**memory**: 9.3 GB for ONE factor, so a four-factor file wants headroom in the tens of GB.

Lever 1 (factor first) is what makes the route work at all; it does not make `d = 34` behave
like `d = 11`, since a degree-`34` irreducible cannot be split further. For the `p = 37` row
(`deg H = 666` as `222³`, `ℓ = 397`) the model gives `222³/34³ ≈ 278` on top of the above,
which is what the "DO NOT DISPATCH A PLAIN COMPUTATION AT THIS ROW" note in `X0.lean` is
about; that note stands.

### `/proc` utime+stime IS NOT WALL TIME — and "one core per file" is FALSE for generated files

Both halves of this cost real effort on the same day, and the first nearly went into this
file as a fact.

Watching the probe through `/proc/<pid>/stat` fields 14+15, I read **1631 → 3843 → 4747 CPU-s**
on a run that had started ~16 minutes earlier, and was about to record "still elaborating
after 79 CPU-minutes, never finished". It had in fact finished, in **987 s**. The reading was
right; the interpretation was not — utime+stime sums **all threads**, and this file was
running **110 threads at ~15–17 cores**. A `/proc` CPU delta overstates elapsed time by
exactly the parallelism factor, so **never compare a CPU-seconds reading against a wall-clock
budget.** Wrap the run in `/usr/bin/time` and read `%e`.

That also corrects the standing claim in the throughput section above that **"elaboration is
single-threaded — one core per file"**. Lean elaborates *independent top-level declarations*
in parallel, and here reached ~17 cores. Both observations are true of the files they were
made on, and the discriminator is **dependency structure, not size**: a GENERATED certificate
is thousands of mutually independent theorems and parallelises almost perfectly, whereas
`Interface.lean` — where the original one-core measurement was taken — is a long dependency
chain and cannot. So "split the file to win cores" applies to hand-written chains; a generated
file already gets them. Note the cost: `sys` time here equals `user` time, so ~14 000 CPU-s
buys 829 s of progress — cheap in wall-clock, expensive in machine.

### The coprimality certificate: REDUCE FIRST, or the Bézout cofactor has degree `q ^ k`

A row where some `d > 1` divides `m` and is `≤ n` — the `p = 17` rows, `d = 2` — needs
`IsCoprime H (X ^ (q ^ d) - X)` on top of the divisibility, because
`not_monic_dvd_of_smallDegreePart`'s `hmn` fails there. Writing that Bézout **directly** is
hopeless: a certificate `s * H + t * (X ^ (q ^ 2) - X) = 1` has `deg s ≈ q ^ 2 = 4489`.

Do it mod `h` instead. `X ^ (q ^ 2)` is ALREADY reduced by the table — it is the chain's
`p 2` — so certify `IsCoprime h (p 2 - X)`, where both cofactors have degree `< deg h`, and
transport it along the congruence with

    theorem isCoprime_of_dvd_sub {R} [CommRing R] {a b c : R}
        (hab : IsCoprime a b) (hc : a ∣ c - b) : IsCoprime a c := by
      obtain ⟨u, v, huv⟩ := hab; obtain ⟨k, hk⟩ := hc
      exact ⟨u - v * k, v, by linear_combination huv + v * hk⟩

then recombine the factors with `IsCoprime.mul_left`. `flt-frobenius-cert.py` emits all of
this under `--coprime-exponent k`; verified green end to end.

### A GENERATOR'S ROUND-TRIP TEST EARNS ITS KEEP — it caught a shadowed parameter

`flt-frobenius-cert.py` claims that regenerating its committed output reproduces it byte for
byte. Running that check while ADDING the coprimality option found two things at once. The
real one: the recombination loop wrote its accumulator to a local named `cop`, which is also
the function's `--coprime-exponent` **parameter** — so after the loop `cop is not None` was
always true and *every* run silently emitted a coprimality block, with the Bézout expression
interpolated into the docstring where the exponent belonged. Nothing about the output looked
malformed enough to notice by eye in a 2300-line file.

The second: the committed `MazurNonCMFrobenius.lean` did **not** round-trip, because it
predated the tool's generalisation from `23` to any `q` (`pow_twentythree` → `pow_frob`,
`d12`/`d123` → `d2`/`d3`). The claim in the docstring was simply false, and a regression test
that is known to fail is a regression test nobody runs. Both files are now regenerated and
both round-trip. **If a generator says its output round-trips, run it — and if it does not,
fix the file rather than softening the claim.**

