## A "DOES NOT USEFULLY SPLIT" VERDICT IS SCOPED TO THE CONSTRUCTION ITS AUTHOR HAD IN MIND

(2026-07-31, `ArtinSymbol.lean`.) `closure_frobAt_eq_top` (Chebotarev) carried a careful,
honest docstring verdict: *"audited, faithful, and deliberately NOT decomposed"*, with a
numbered list of three ingredients the fixed-field reduction would need and which the pin
does not have. **Two of the three did not exist.** They were consequences of one unstated
design choice — that the fixed field `M = L^H` should be GALOIS over `K`, so that one can
speak of `frobAt K M`. Galois-ness forces `H` normal, which forces transporting
`Algebra.IsUnramifiedAt` along an automorphism (obstacle 1), and `frobAt K M` forces
functoriality of `arithFrobAt` down a tower (obstacle 2). But the reduction never needs
`frobAt K M`: the only thing wanted from `M` is that its primes have residue degree `1`,
and that is read straight off the congruence `σ y ≡ y^(N𝔭) (mod Q)` restricted to `𝓞 M`,
with `M` used as a RING and no Galois structure at all. With that, the reduction is ~90
lines against mathlib as it stands, and the residual leaf is a clean density statement
naming no Frobenius and no Galois group.

**So when a docstring says a node does not decompose, read the obstacle list as a claim
about ONE route.** Ask which of the obstacles are forced by the goal and which are forced
by the author's chosen intermediate object; the second kind vanishes when you weaken the
intermediate object to the least structure the argument actually uses. The tell here was
that every listed obstacle mentioned `M` being Galois, while the conclusion mentions only
`Subgroup.closure`.

Two corollaries worth keeping separate:

- **The verdict was still right about the OTHER cut it considered**, and said so: the
  contrapositive ("for every proper `H` there is an unramified `Q` with `frobAt K L Q ∉ H`")
  trades one leaf for an equivalent one. The discriminator between a real cut and noise is
  whether the residual statement stops mentioning the project's own vocabulary. That test
  also correctly REJECTS the analogous cut on the sibling leaf `artinMap_toPrincipalIdeal`
  (reduce abelian reciprocity to the cyclic case): the residual still mentions `frobAt` and
  `Gal(L/K)`, and is where the classical proof spends all its effort.
- **Do not add the infrastructure an obstacle list names once you no longer need it.**
  Tower functoriality of `frobAt` is genuinely missing and genuinely reusable — and adding
  it here would have been FREE-FLOATING code, since nothing in the cone consumes it. An
  obstacle that dissolves is not a licence to build it anyway.

