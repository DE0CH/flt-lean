## `reduce_mod_char` dies on COEFFICIENT SIZE, not degree — stage products two at a time
(2026-07-31, measured while closing the four `p = 17` leaves of Mazur's non-CM table.)
The generated Frobenius certificates end by identifying `H` with the product of its factors.
For `deg H = 136` over `ZMod 67` as a product of four degree-`34` polynomials, the obvious
    simp only [F1.h, F2.h, F3.h, F4.h]; ring_nf; reduce_mod_char
**DOES NOT CLOSE.**  It runs 269 s and then dies in `reduce_mod_char` with
`(deterministic) timeout at isDefEq, maximum number of heartbeats (1000000)`.
**`ring_nf` is not the bottleneck — it gets through.**  What runs out is reducing the
coefficients afterwards.  Expanding a 4-fold product BEFORE any reduction pushes the
intermediate coefficients to `≈ 10 ^ 12` (35 terms cubed, times `66 ^ 4`), and it is 137
numerals of that size that `reduce_mod_char` cannot chew.  Degree is a red herring: the same
tactic triple is fine at degree 55 (the `p = 11` rows, 5 factors of degree 11).
The fix is to multiply **one factor at a time** through named partial products
`g2 = h₁h₂`, `g3 = g2·h₃`, …, each already reduced mod `q` in the emitted definition, and
finish with `rw [hg2, hg3, hg4, g4]`.  No `ring_nf` then sees more than TWO explicit
polynomials, and no numeral exceeds `deg · (q−1)² ≈ 4·10⁵`.  Same statement, same three
tactics: **224 s and EXIT=0**.  Implemented as `product_block` in `flt-frobenius-cert.py`.
Two things worth carrying beyond this file:
* **The generalisable rule is "keep the numerals small", not "keep the degree small".**  Any
  `ring_nf; reduce_mod_char` over `ZMod q` on a product of `k ≥ 3` explicit polynomials is
  suspect, because the coefficient blow-up is exponential in `k` while the degree is only
  additive.  Insert reduced intermediates.
* **Isolate the single riskiest identity into a scratch module and time it BEFORE launching
  the hour-long build.**  Here that cost 269 s and saved discovering the failure at the end of
  a 65-minute elaboration — which is exactly where it would otherwise have surfaced, since the
  product identity is the LAST thing in the module.
