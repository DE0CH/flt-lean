# G''-package design (the mirror field for hstepS) — derived 2026-07-22

Status: hstepS is PROVEN in WeilPairingRecgen.lean as the σ-mirror
instance of the field-generic `WeilPairing.stepR` at a second subfield
G''. The one remaining leaf of that chain is the sorried G''-existence
obtain in WeilPairing.lean (~line 7873, inside huniqval's cross-setup
block). This file records the complete discharge design and the
adversarial-setup analysis that forced amendment (β).

## The setting

Inside `huniqval`, the two level-1 setups (F₁,F₁',S₁,R₁,PS₁,QR₁,aP₁,aQ₁)
and (F₂,…) are DESTRUCTURED FROM the IsWeilValue existentials hz₁.2 /
hz₂.2 — they are ADVERSARIAL (universally quantified), not chosen here.
Only the shared level-3 family (S₃,R₃,PS₃,QR₃,aP₃,aQ₃) is chosen
locally, by `hsetup3 G` (G = the hsubfin closure of F₁' ∪ F₂' ∪
{QR₁,QR₂-coords} ∪ yfib-images).

Required: a subfield G'' with
  xR₃,yR₃,xQR₃,yQR₃ ∈ G''  and
  xS₁,xPS₁,xS₂,xPS₂,xS₃,xPS₃, x(M'₁), x(M'₂) ∉ G''
(M'ᵢ = PSᵢ ⊕ S₃, the addX/slope expressions in the obtain).

## Key structural fact (makes everything work)

Finite subfields of 𝔽̄_q are TOTALLY ORDERED: for each n there is
exactly one subfield of size q^n, namely K(n) := {x | x^(q^n) = x}
(the frobⁿ-fixed subfield, `frobFixed q n` in the ktoolkit module
FrobeniusFixedField.lean). Every finite subfield F equals K(n) for
|F| = q^n; membership is the degree condition d(a) ∣ n where
d(a) := the Frobenius period of a. Curve coefficients are in the PRIME
field (Wb = base change of Wbar over ZMod q), so the y-coordinate over
a given x satisfies a quadratic over 𝔽_q(x): d(y) ∣ 2·d(x).

## The construction

Let F₀ := 𝔽_q(P,Q-coords) = K(f₀) (computable inside hsetup3 from its
xP,yP,xQ,yQ inputs). Note g_Q := [𝔽_q(Q-coords)] ∣ f₀ ∣ f₁ and f₀ ∣ f₂
(P,Q-coords lie in F₁ and F₂).

Inside a STRENGTHENED hsetup3:
1. Choose S (=S₃) as now, ADDITIONALLY avoiding the xOf-images of
   K(f₀)-fibers translated by each caller-passed base point
   (new input: the finite list of base points, here PS₁ and PS₂, plus
   P as before) — this yields x(basept ⊕ S₃) ∉ K(f₀) and xS₃ ∉ K(f₀)
   (the latter already follows from xS₃ ∉ G ⊇ K(f₀)).
2. Pick a prime ℓ > max(N, degrees of all S₃/PS₃/M'-relevant elements,
   [closure(G):𝔽_q]) where N is a caller-passed certificate bound
   (caller sets N := [closure(G):𝔽_q], so every element of G has
   degree ≤ N < ℓ). Also ℓ large enough that #E(K(ℓ)) beats the
   avoid-set (q^ℓ − q − |avoid| > 0 counting).
3. Choose R (=R₃) a point of E with BOTH coords in K(ℓ) and x ∉ K(1),
   satisfying the existing avoidances. Then QR₃ = Q ⊕ R₃ has coords in
   K(lcm(g_Q,ℓ)) ⊆ K(ℓ·f₀).
4. G'' := K(ℓ·f₀).

Exclusion principle: a ∈ G'' ⟹ d(a) ∣ ℓ·f₀ ⟹ (if d(a) < ℓ, so
gcd(d(a),ℓ)=1) d(a) ∣ f₀ ⟹ a ∈ K(f₀). Contrapositive: any a with a
degree certificate d(a) ≤ N < ℓ and a ∉ K(f₀) is NOT in G''.

Discharge of the ∉ facts (each element has certificate ∈ K(N) or an
hsetup3-internal bound):
- xS₁: xS₁ ∈ G (cert). If xS₁ ∈ K(f₀) ⊆ K(f₁) = F₁, contradicts
  hxS₁F : xS₁ ∉ F₁. (Uses F₁ = K(f₁), f₀ ∣ f₁.)
- xS₂: same with F₂.
- xPS₁/xPS₂: needs xPS ∉ F — NOT currently in IsWeilValue. This is
  AMENDMENT (β), see below. With it: xPS₁ ∈ K(f₀) ⊆ F₁ contradicts.
- xS₃, xPS₃: from hxS₃/hxPS₃ (∉ G ⊇ K(f₀)) + internal degree bounds.
- x(M'ᵢ): from step 1's image-avoidance (∉ K(f₀)) + degree bound
  d(xM') ∣ lcm(degrees of PSᵢ-coords, S₃-coords) < ℓ.
- R₃-family ∈ G'': coords ∈ K(ℓ) resp. K(lcm(g_Q,ℓ)), both ⊆ K(ℓf₀).
- Existing hsetup3 conclusions (xR₃,xQR₃,xS₃,xPS₃ ∉ G): via
  degree ∤ [G] (ℓ > [G]) resp. the existing avoidances.

## AMENDMENT (β) — REQUIRED, adversarial counterexample without it

Without `xPS ∉ F` in IsWeilValue, an adversarial setup may have
deg x(P⊕S₁) ∣ g_Q (small) while keeping xS₁ ∉ F₁ (xS₁ then has degree
2e with e ∣ f₁, 2e ∤ f₁ — consistent because y-degrees only double).
Then xPS₁ lies in EVERY candidate G'' ⊇ QR₃-coords-field, and no valid
G'' exists. Fix: add the conjunct `xPS ∉ F` to the IsWeilValue
predicate (precedent: amendment (α) added `xQR ∉ F'`). Consumers to
update: the predicate definition, hexval (the constructor — its
S-choice must additionally avoid the xOf-image of F under (−P + ·),
the exact trick already used for other avoidances), and every
destructuring site of the predicate (arity bump: hz₁.2/hz₂.2 in
huniqval, any others found by grep on the obtain patterns).

## ktoolkit requirements beyond the dispatched spec

- Every finite subfield F of 𝔽̄_q equals K(n) where |F| = q^n
  (cardinality is a q-power; F ⊆ K(n) by little Fermat; equality by
  cardinality of K(n) = q^n).
- Monotonicity K(a) ⊆ K(b) ↔ a ∣ b, membership-degree dictionary,
  d(y) ∣ 2 d(x) for curve points (quadratic over 𝔽_q(x)),
  d(coords of P⊕Q) ∣ lcm(d-of-inputs) (addX/addY/slope are rational
  expressions over the prime field),
  existence of E-points with both coords in K(ℓ), x ∉ K(1), avoiding a
  finite set, for ℓ prime with q^ℓ large (counting).

## Order of implementation

1. (orchestrator, WeilPairing.lean) Amendment (β) + hexval update +
   destructure arity bumps — INDEPENDENT of the toolkit, do first.
2. (after ktoolkit lands) hsetup3 strengthening per above.
3. Discharge the sorried G''-obtain at ~7873 from the hsetup3'
   package.
