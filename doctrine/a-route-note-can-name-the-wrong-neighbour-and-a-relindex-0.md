## A ROUTE NOTE CAN NAME THE WRONG NEIGHBOUR — AND A `relIndex ≠ 0` CONCLUSION *IS* A FINITENESS STATEMENT
(2026-08-02, `flt-lean-62`, closing `exists_narrowRayCharacters_ray_class` in
`GaloisRepresentation/HardlyRamified/ModThree.lean`.)  That leaf's route note is unusually
good — it correctly says the character half is free in the pin, names the four mathlib
declarations, and says "**what actually has to be built is the GROUP `H` and its
FINITENESS**".  Then it prices the finiteness through the wrong neighbour:
> `H := G ⧸ R` is finite, and the argument is ALREADY WRITTEN one leaf up in covering form:
> `exists_finset_forall_isNarrowRayEquivMod_ray_class` … what has to be added is only that a
> general coprime FRACTIONAL ideal is a quotient of two integral ones.
None of that is needed.  `relIndex_narrowRayGroup_ne_zero_ray_class`, PROVEN in the same file
two thousand lines further up, **IS** the finiteness of `H` — because
`Subgroup.relIndex H K = (H.subgroupOf K).index = Nat.card (K ⧸ H.subgroupOf K)` **by
definition**, so `P.relIndex Im ≠ 0` and `Finite (↥Im ⧸ P.subgroupOf Im)` are the same
sentence.  The whole finiteness step is one `Nat.finite_of_card_ne_zero`.
**Two checks, and both are one grep.**
* **A `relIndex`/`index`/`Nat.card … ≠ 0` conclusion is a finiteness statement about a
  quotient.**  Before building any finiteness of a quotient group, `grep -n 'relIndex' <the
  file>` and read what the hits are *about*.  This development states ray-class finiteness
  that way throughout, and the shape does not look like `Finite` to a reader scanning for it.
* **A theorem quantified over an ARBITRARY function pinned only by a hypothesis is usually
  the general form of exactly what you want.**  `relIndex_narrowRayGroup_ne_zero_ray_class`
  takes an arbitrary `d : 𝓞 F → Div` with `hd` saying "`d δ` is the divisor of `δ`", and an
  arbitrary `Im` with `hIm` saying what its members are.  Instantiating it at the honest
  divisor map is the entire geometric content of the leaf; the route note read it as being
  about somebody else's `d` and looked elsewhere.  **When a route note says the argument you
  need is "written in <other> form" somewhere, check whether some sibling states it in
  ABSTRACT form — the abstract one is the one you can use.**
### The three pieces that WERE owed, and the one worth stealing
* **The `Finsupp`-valued divisor of a fractional ideal.**  The pin has
  `FractionalIdeal.count` and `FractionalIdeal.finite_factors (I) : ∀ᶠ v in cofinite,
  count K v I = 0` and *nothing that assembles them*.  Three lines:
  `⟨(Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors I)).toFinset,
  fun v => count F v I, by simp⟩`.  Grep for it before re-deriving; it is the inverse of this
  file's `divisorFractionalIdeal_ray_class`.
* **`Subgroup.closure S = {a * b⁻¹ : a, b ∈ S}` WHEN `S` IS A SUBMONOID OF A COMMUTATIVE
  GROUP, and you only ever need `≤`.**  This is the piece a formalisation is most likely to
  attack by induction over words, and it is three lines the other way: build the ratio set as
  an honest `Subgroup` (`one_mem` from `1 ∈ S`, `mul_mem` from `S` closed under `*` plus
  `mul_mul_mul_comm`, `inv_mem` by swapping the two witnesses) and hit it with
  `Subgroup.closure_le`.  Every "the narrow principal ideals are the ratios of narrow
  generators"-shaped step in class field theory is this lemma.
* **The identification of the project's equivalence relation with equality of classes.**
  Both directions go through the divisor map; the only arithmetic in either is that a
  `δ ≡ 1 (mod mm)` is a unit at every prime of `mm` (a prime containing `δ` and `mm` contains
  `1 = δ - (δ - 1)`).
### `MulChar` DUALITY IS FOR AN ARBITRARY FINITE COMMUTATIVE MONOID — but its `conj` lemma is not
`Mathlib/NumberTheory/MulChar/Duality.lean` is stated for `[CommMonoid M] [Finite M]
[HasEnoughRootsOfUnity R (Monoid.exponent Mˣ)]`, so it applies to a finite commutative GROUP
verbatim, and `DirichletCharacter.sum_characters_eq`'s proof transcribes with `ZMod n`
replaced by that group — about forty lines, and it is worth stating as a standalone theorem
about an arbitrary finite commutative group (here `exists_characters_orthogonality_ray_class`)
so that the arithmetic and the character theory never meet.
**The one thing that does NOT transcribe: `MulChar.star_apply'` / `star_eq_inv`
(`conj (χ a) = χ⁻¹ a`) live in a `section Ring` with `[CommRing R]` on the SOURCE.**  For a
group source they are unavailable and the substitute is three lines:
`(χ a) ^ Fintype.card H = χ (a ^ card H) = 1` gives `‖χ a‖ = 1`
(`Complex.norm_eq_one_of_pow_eq_one`), then `Complex.inv_eq_conj` and
`inv_eq_of_mul_eq_one_right (by rw [← map_mul, mul_inv_cancel, map_one])`.  Getting
`HasEnoughRootsOfUnity ℂ (Monoid.exponent Hˣ)` is one `haveI : NeZero ((Monoid.exponent Hˣ :
ℕ) : ℂ) := ⟨by exact_mod_cast Monoid.exponent_ne_zero_of_finite⟩`; the instance is then found
through `IsSepClosed.hasEnoughRootsOfUnity`.
### A JUNK VALUE IS SAFE EXACTLY WHEN THE GOOD SET IS INVARIANT UNDER THE UNCONDITIONAL CLAUSES
A leaf routinely asks for a function on ALL objects while constraining it only on a sub-class
(here: nonzero fractional ideals coprime to `mm`).  Defining it by `dite` with a junk value is
right, and the check is mechanical: **list the clauses that do NOT carry the sub-class
hypothesis, and verify the sub-class is invariant under whatever they quantify over.**  Here
exactly one clause is unconditional — `IsNarrowRayEquivMod mm I J → χ i I = χ i J` — and it
survives because the relation is both coprimality-invariant and zero-invariant, so equivalent
ideals are junk together or good together.  Had either failed, the junk value would have made
the leaf unprovable and the failure would have shown up only at the last clause.
### Mechanical notes, each of which cost a round trip
* **`Multiplicative.toAdd_mul` DOES NOT EXIST.**  `toAdd (a * b) = toAdd a + toAdd b` is `rfl`,
  so the way to use it is not `simp` but stating the target type explicitly and letting
  `congrArg (fun x => Multiplicative.toAdd x v) h` be checked against it up to defeq.
* **A scope walk beats guessing which `open`s are live.**  `ModThree.lean` has 111 `open`
  lines; a twenty-line python walk over comment-masked source, pushing on
  `namespace`/`section` and popping on `end`, showed that **exactly one** was live at the
  insertion point.  Mirror that one in the scratch and the scratch is testing the real
  environment; guessing costs an hour-long build per wrong guess.
* The `refine ⟨fun i I => …, …⟩` beta-redex trap fires here too — every branch needs a `show`
  with the beta-reduced goal before `rw` will match.  (Already recorded above; this is the
  third instance.)
