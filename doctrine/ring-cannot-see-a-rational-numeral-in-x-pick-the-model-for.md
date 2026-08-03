## `ring` CANNOT SEE A RATIONAL NUMERAL IN `ℚ[X]` — pick the model for writability

(2026-07-31, flt-lean-106, and it decided the shape of a whole leaf.) `ℚ[X]`
carries a `Div` instance — `Polynomial.div`, the *Euclidean* one — and is **not
a `DivisionRing`**. `ring` only evaluates `/` in a `DivisionRing`; everywhere
else it treats the quotient as an **atom**. So in `ℚ[X]` the numeral `3/37` is
opaque, `ring` cannot prove `(3/37)^2 = 9/1369`, and every polynomial identity
containing a non-integral coefficient fails. Measured on a two-line `example`,
not assumed — and the failure is silent in the sense that it looks like an
ordinary `ring` defeat, not like a missing instance.

Consequence for the explicit-certificate files (`GenusOneKernelPolynomials.lean`
and its level-`37` analogue): **the model is chosen for INTEGRALITY of the
derived polynomial, not for minimality of the curve.** At `p = 37` the minimal
conductor-`1225` Mazur–Swinnerton-Dyer curve `[1,1,1,−208083,−36621194]` has a
kernel polynomial with constant term `−N/37` — genuine, since `elldivpol(E,37)`
has leading coefficient `37`, so Gauss's lemma does not force monic factors to
be integral. Mathematically fine for `IsKernelPolynomial`, which asks only for
monicity; unwritable in Lean.

The repair is a change of model, and the arithmetic of *which* model is short:
the models of a fixed `j` are the quadratic twists composed with the
`u`-scalings, which multiply every `x`-coordinate by an arbitrary `c = d·w²`,
and a derived polynomial's coefficients transform as `f_k ↦ c^(deg−k) f_k`. So
integrality of `f_0` is a divisibility condition on `c`, and the optimal `c` is
the smallest one meeting it — here `c = 37`, i.e. the quadratic twist by `37`
(model `[1, 46, 1, −284864943, −1854973327019]`, conductor `1225·37²`), which
clears the `1/37` exactly once and costs only a factor `37^(18−k)` on the
coefficients. Scaling instead (`u = 1/37`, `c = 37²`) is legal and twice as
expensive; there is nothing cheaper than `c = 37`.

**So: compute the certificate polynomial BEFORE committing to a model, and check
its denominators.** Doing it the other way round means generating a megabyte of
Lean that cannot compile, and the diagnosis costs a full build.

