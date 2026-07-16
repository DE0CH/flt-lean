/-
MazurTorsion.lean — own work for the Fermat project (not vendored from the
FLT project).

Decomposition of `FreyPackage.mazur` (irreducibility of the mod-`p` Galois
representation on the `p`-torsion of the Frey curve) into two explicit
sorry nodes, following Serre's argument (Duke Math. J. 54 (1987), §4.1):

* `FreyPackage.exists_torsion_embedding_of_not_isIrreducible` (sorry node):
  **Serre's reducible-case analysis.** If the mod-`p` representation of the
  Frey curve `E` is not irreducible, then there is a Galois-stable line in
  `E[p]` (the `p`-torsion is `2`-dimensional over `𝔽_p`, so a proper nonzero
  invariant submodule is a line), i.e. a rational subgroup `C ⊆ E` of order
  `p`, giving an extension `0 → χ₁ → E[p] → χ₂ → 0` of characters with
  `χ₁ χ₂ = ω̄` (mod-`p` cyclotomic, by the Weil pairing). The Frey curve is
  semistable, so both characters are unramified away from `p` (unipotent
  inertia at multiplicative primes, triviality at good primes), and at `p`
  one of them is unramified (the supersingular case is excluded because
  inertia at `p` then acts irreducibly, contradicting reducibility). An
  everywhere-unramified character of `Gal(ℚ̄/ℚ)` is trivial (Minkowski: `ℚ`
  has no unramified extension). If `χ₁ = 1` then `E` has a rational point
  of order `p`; if `χ₂ = 1` then the quotient curve `E' = E/C` (a `ℚ`-rational
  quotient by a rational subgroup, Vélu) has one, namely the image of `E[p]`.
  Whichever curve carries the point of order `p` also carries full rational
  `2`-torsion: `E` visibly (`y² = x(x − aᵖ)(x + bᵖ)` has `(0,0)`, `(aᵖ,0)`,
  `(−bᵖ,0)`), and `E/C` because the quotient isogeny has odd degree `p`
  (so is injective on `E[2]`) and is defined over `ℚ`. Since `p` is odd,
  `(ℤ/2)² × ℤ/p ≅ ℤ/2 × ℤ/2p`, so SOME elliptic curve over `ℚ` has a
  subgroup of rational points isomorphic to `ℤ/2 × ℤ/2p`. The statement
  folds the quotient-curve construction (not yet available in mathlib) into
  an existential over Weierstrass models; a later layer must construct
  quotients by finite rational subgroups and split this node accordingly.

* `WeierstrassCurve.mazur_classification` (sorry node): **Mazur's torsion
  theorem** (Mazur, 1977/1978), stated faithfully: the torsion subgroup of
  the rational points of an elliptic curve over `ℚ` is isomorphic to one of
  the fifteen groups `ℤ/n` for `n ∈ {1, …, 10, 12}` or `ℤ/2 × ℤ/2m` for
  `m ∈ {1, 2, 3, 4}`.

* `WeierstrassCurve.mazur_torsion_bound` (PROVEN from the classification):
  **Mazur's torsion theorem, weak form.** No elliptic curve over `ℚ` has a
  subgroup of rational points isomorphic to `ℤ/2 × ℤ/2p` for a prime
  `p ≥ 5`. Derivation: the image of an injective homomorphism
  `ℤ/2 × ℤ/2p →+ E(ℚ)` consists of torsion points (every element of the
  finite source has finite additive order), so the homomorphism corestricts
  to an injection into the torsion subgroup; by the classification the
  torsion subgroup is finite of order at most `16`, while the source has
  order `4p ≥ 20`.

Given the two nodes, `FreyPackage.mazur` is immediate: if the representation
were reducible, the first node produces a curve whose rational points contain
`ℤ/2 × ℤ/2p`, which the second node forbids.
-/
module

public import Fermat.FLT.FreyCurve.Basic
public import Fermat.FLT.EllipticCurve.Torsion

@[expose] public section

open WeierstrassCurve WeierstrassCurve.Affine

set_option warn.sorry false in
/-- **Mazur's torsion theorem** (sorry node): the torsion subgroup of the
rational points of an elliptic curve over `ℚ` is isomorphic to one of the
fifteen groups `ℤ/n` with `n ∈ {1, …, 10, 12}` or `ℤ/2 × ℤ/2m` with
`m ∈ {1, 2, 3, 4}`. Mazur, "Modular curves and the Eisenstein ideal"
(Publ. Math. IHÉS 47, 1977) and "Rational isogenies of prime degree"
(Invent. Math. 44, 1978). -/
theorem WeierstrassCurve.mazur_classification (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    (∃ n ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12} : Finset ℕ),
      Nonempty ((Submodule.torsion ℤ (E⁄ℚ).Point) ≃+ ZMod n)) ∨
    (∃ m ∈ ({1, 2, 3, 4} : Finset ℕ),
      Nonempty ((Submodule.torsion ℤ (E⁄ℚ).Point) ≃+ (ZMod 2 × ZMod (2 * m)))) :=
  sorry

/-- **Mazur's torsion theorem, weak form**: the rational points of an
elliptic curve over `ℚ` contain no subgroup isomorphic to `ℤ/2 × ℤ/2p` for
any `p ≥ 5` (primality is not needed: the order comparison `4p ≥ 20 > 16`
alone suffices) — equivalently, no additive homomorphism
`ℤ/2 × ℤ/2p →+ E(ℚ)` is injective. Derived from `mazur_classification`:
the image consists of torsion points, so the homomorphism corestricts to an
injection into the torsion subgroup, which by the classification is finite
of order at most `16 < 4p`. -/
theorem WeierstrassCurve.mazur_torsion_bound (E : WeierstrassCurve ℚ) [E.IsElliptic]
    {p : ℕ} (h5 : 5 ≤ p)
    (φ : (ZMod 2 × ZMod (2 * p)) →+ (E⁄ℚ).Point) :
    ¬ Function.Injective φ := by
  intro hφ
  haveI : NeZero (2 * p) := ⟨by omega⟩
  -- every image point is torsion: `x` has finite additive order in the
  -- finite group `ℤ/2 × ℤ/2p`, and `φ` transports the annihilation
  have hmem : ∀ x : ZMod 2 × ZMod (2 * p),
      φ x ∈ Submodule.torsion ℤ (E⁄ℚ).Point := by
    intro x
    rw [Submodule.mem_torsion_iff]
    refine ⟨⟨(addOrderOf x : ℤ),
      mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast (addOrderOf_pos x).ne')⟩, ?_⟩
    show (addOrderOf x : ℤ) • φ x = 0
    rw [natCast_zsmul, ← map_nsmul, addOrderOf_nsmul_eq_zero, map_zero]
  -- corestrict to the torsion subgroup, preserving injectivity
  let φ' : (ZMod 2 × ZMod (2 * p)) →+ (Submodule.torsion ℤ (E⁄ℚ).Point) :=
    φ.codRestrict (Submodule.torsion ℤ (E⁄ℚ).Point) hmem
  have hφ' : Function.Injective φ' := fun a b hab => hφ (Subtype.ext_iff.mp hab)
  -- compare cardinalities against the fifteen groups
  rcases E.mazur_classification with ⟨n, hn, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩
  · have hn12 : 1 ≤ n ∧ n ≤ 12 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      omega
    haveI : NeZero n := ⟨by omega⟩
    haveI : Finite (Submodule.torsion ℤ (E⁄ℚ).Point) :=
      Finite.of_equiv (ZMod n) e.symm.toEquiv
    have hcard := Nat.card_le_card_of_injective φ' hφ'
    rw [Nat.card_prod, Nat.card_zmod, Nat.card_zmod,
      Nat.card_congr e.toEquiv, Nat.card_zmod] at hcard
    omega
  · have hm4 : 1 ≤ m ∧ m ≤ 4 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      omega
    haveI : NeZero (2 * m) := ⟨by omega⟩
    haveI : Finite (Submodule.torsion ℤ (E⁄ℚ).Point) :=
      Finite.of_equiv (ZMod 2 × ZMod (2 * m)) e.symm.toEquiv
    have hcard := Nat.card_le_card_of_injective φ' hφ'
    rw [Nat.card_prod, Nat.card_zmod, Nat.card_zmod, Nat.card_congr e.toEquiv,
      Nat.card_prod, Nat.card_zmod, Nat.card_zmod] at hcard
    omega

set_option warn.sorry false in
/-- **Serre's reducible-case analysis for the Frey curve** (sorry node): if
the mod-`p` Galois representation on the `p`-torsion of the Frey curve is
not irreducible, then some elliptic curve over `ℚ` (the Frey curve itself or
its quotient by the resulting rational subgroup of order `p`) has full
rational `2`-torsion — an injective `(ℤ/2)² →+ E'(ℚ)` — together with a
rational point of order exactly `p`. Serre, Duke 1987, §4.1: semistability
forces one of the two characters of the reducible representation to be
everywhere unramified, hence trivial (Minkowski), so `E` or `E/C` has a
rational point of order `p`; both curves have full rational `2`-torsion
(the Frey curve visibly — its untransformed model is
`y² = x(x - aᵖ)(x + bᵖ)` — and `E/C` because the quotient isogeny has odd
degree `p`, hence is injective on `E[2]`, and is defined over `ℚ`). The
quotient-curve construction (Vélu) is not yet available in mathlib, so the
statement quantifies existentially over Weierstrass models; a later layer
must construct quotients by finite rational subgroups and split this node
accordingly. -/
theorem FreyPackage.exists_two_torsion_and_p_point_of_not_isIrreducible
    (P : FreyPackage)
    (h : ¬ (let E := P.freyCurve
            let p := P.p
            have : Fact p.Prime := ⟨P.pp⟩
            GaloisRep.IsIrreducible (E.galoisRep p P.hppos))) :
    ∃ (E' : WeierstrassCurve ℚ) (_ : E'.IsElliptic)
      (φ₂ : (ZMod 2 × ZMod 2) →+ (E'⁄ℚ).Point) (_ : Function.Injective φ₂)
      (Q : (E'⁄ℚ).Point), addOrderOf Q = P.p :=
  sorry

/-- **Assembly of coprime torsion** (PROVEN 2026-07-16): in an abelian
group, an injective `(ℤ/2)²` and an element of order exactly `p` (an odd
prime) combine into an injective `ℤ/2 × ℤ/2p`, via the Chinese remainder
isomorphism `ℤ/2p ≅ ℤ/2 × ℤ/p`. The two images intersect trivially
because their exponents `2` and `p` are coprime. -/
theorem embedding_assembly {A : Type*} [AddCommGroup A]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (φ₂ : (ZMod 2 × ZMod 2) →+ A) (hφ₂ : Function.Injective φ₂)
    (Q : A) (hQ : addOrderOf Q = p) :
    ∃ ψ : (ZMod 2 × ZMod (2 * p)) →+ A, Function.Injective ψ := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr
    (Ne.symm hp2)
  -- the CRT isomorphism `ℤ/2p ≅ ℤ/2 × ℤ/p`
  let e : ZMod (2 * p) ≃+ ZMod 2 × ZMod p :=
    (ZMod.chineseRemainder hcop).toAddEquiv
  -- the `p`-part: `ℤ/p →+ A` sending `1 ↦ Q`
  have hpQ : (zmultiplesHom A Q) (p : ℤ) = 0 := by
    show (p : ℤ) • Q = 0
    rw [natCast_zsmul, ← hQ, addOrderOf_nsmul_eq_zero]
  let fQ : ZMod p →+ A := ZMod.lift p ⟨zmultiplesHom A Q, hpQ⟩
  have hfQ : ∀ k : ZMod p, fQ k = k.val • Q := by
    intro k
    have h1 : fQ (((k.val : ℤ) : ZMod p)) = zmultiplesHom A Q (k.val : ℤ) :=
      ZMod.lift_coe p _ (k.val : ℤ)
    rw [show (((k.val : ℤ)) : ZMod p) = k by
      rw [Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id]] at h1
    rw [h1]
    show ((k.val : ℤ)) • Q = _
    rw [natCast_zsmul]
  have hfQker : ∀ k : ZMod p, fQ k = 0 → k = 0 := by
    intro k hk
    rw [hfQ k] at hk
    have hdvd : addOrderOf Q ∣ k.val := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hk
    rw [hQ] at hdvd
    have hval0 : k.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt k)
    exact (ZMod.val_eq_zero k).mp hval0
  -- annihilation facts for the two parts
  have h2ann : ∀ y : ZMod 2 × ZMod 2, (2 : ℕ) • y = 0 := by decide
  have hpann : ∀ k : ZMod p, (p : ℕ) • k = 0 := by
    intro k
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  -- the assembled homomorphism
  let ψ : (ZMod 2 × ZMod (2 * p)) →+ A :=
    { toFun := fun x => φ₂ (x.1, (e x.2).1) + fQ (e x.2).2
      map_zero' := by
        have h0 : e 0 = 0 := map_zero e
        show φ₂ ((0 : ZMod 2 × ZMod (2 * p)).1, (e (0 : ZMod 2 × ZMod (2 * p)).2).1)
          + fQ (e (0 : ZMod 2 × ZMod (2 * p)).2).2 = 0
        rw [show ((0 : ZMod 2 × ZMod (2 * p)).2) = 0 from rfl, h0]
        rw [show (((0 : ZMod 2 × ZMod (2 * p)).1, ((0 : ZMod 2 × ZMod p)).1))
          = (0 : ZMod 2 × ZMod 2) from rfl,
          show ((0 : ZMod 2 × ZMod p)).2 = 0 from rfl, map_zero, map_zero, add_zero]
      map_add' := by
        intro x y
        have he : e (x.2 + y.2) = e x.2 + e y.2 := map_add e _ _
        rw [Prod.fst_add, Prod.snd_add, he, Prod.fst_add, Prod.snd_add,
          show (x.1 + y.1, (e x.2).1 + (e y.2).1)
            = (x.1, (e x.2).1) + (y.1, (e y.2).1) from rfl,
          map_add, map_add]
        abel }
  refine ⟨ψ, (injective_iff_map_eq_zero ψ).mpr ?_⟩
  intro x hx
  -- split `ψ x = 0` into the 2-part and the `p`-part
  set u := φ₂ (x.1, (e x.2).1) with hu
  set v := fQ (e x.2).2 with hv
  have huv : u + v = 0 := hx
  have h2u : (2 : ℕ) • u = 0 := by
    rw [hu, ← map_nsmul, h2ann, map_zero]
  have hpv : (p : ℕ) • v = 0 := by
    rw [hv, ← map_nsmul, hpann, map_zero]
  -- `p` odd kills the 2-part: `p•u = u` while `p•u = -p•v = 0`
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
  have hpu : (p : ℕ) • u = u := by
    have hstep : (p : ℕ) • u = m • ((2 : ℕ) • u) + u := by
      rw [← mul_nsmul', ← succ_nsmul]
      congr 1
      omega
    rw [hstep, h2u, smul_zero, zero_add]
  have hpu0 : (p : ℕ) • u = 0 := by
    have h := congrArg (fun z => (p : ℕ) • z) huv
    simpa [smul_add, hpv] using h
  have hu0 : u = 0 := by rw [← hpu, hpu0]
  have hv0 : v = 0 := by
    have := huv
    rw [hu0, zero_add] at this
    exact this
  -- conclude componentwise
  have h1 : (x.1, (e x.2).1) = 0 :=
    (injective_iff_map_eq_zero φ₂).mp hφ₂ _ hu0
  have h2 : (e x.2).2 = 0 := hfQker _ hv0
  have hex : e x.2 = 0 := by
    have hfst : (e x.2).1 = 0 := congrArg Prod.snd h1
    exact Prod.ext hfst h2
  have hx2 : x.2 = 0 := e.injective (by rw [hex, map_zero])
  have hx1 : x.1 = 0 := congrArg Prod.fst h1
  exact Prod.ext hx1 hx2

/-- **Serre's reducible-case embedding** (DERIVED 2026-07-16 from
`exists_two_torsion_and_p_point_of_not_isIrreducible` and the PROVEN
`embedding_assembly`): if the mod-`p` representation of the Frey curve is
not irreducible, then some elliptic curve over `ℚ` has a subgroup of
rational points isomorphic to `ℤ/2 × ℤ/2p` — the full rational
`2`-torsion and the rational point of order `p` produced by Serre's
analysis, assembled through the Chinese remainder isomorphism. -/
theorem FreyPackage.exists_torsion_embedding_of_not_isIrreducible (P : FreyPackage)
    (h : ¬ (let E := P.freyCurve
            let p := P.p
            have : Fact p.Prime := ⟨P.pp⟩
            GaloisRep.IsIrreducible (E.galoisRep p P.hppos))) :
    ∃ (E' : WeierstrassCurve ℚ) (_ : E'.IsElliptic)
      (φ : (ZMod 2 × ZMod (2 * P.p)) →+ (E'⁄ℚ).Point), Function.Injective φ := by
  obtain ⟨E', hE', φ₂, hφ₂, Q, hQ⟩ :=
    P.exists_two_torsion_and_p_point_of_not_isIrreducible h
  have hp2 : P.p ≠ 2 := by
    have := P.hp5
    omega
  obtain ⟨ψ, hψ⟩ := embedding_assembly P.pp hp2 φ₂ hφ₂ Q hQ
  exact ⟨E', hE', ψ, hψ⟩
