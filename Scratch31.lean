module

public import Fermat.FLT.ModularCurve.X0

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace Scratch31

open Fermat

/-- `∏_{p ∣ n, p ∤ N} p ^ v_p(n)` — the largest divisor of `n` all of whose prime
factors avoid `N`. -/
def coprimeCore (N n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ∣ N), p ^ n.factorization p

theorem coprimeCore_coprime (N n : ℕ) : Nat.Coprime (coprimeCore N n) N := by
  refine Nat.Coprime.prod_left ?_
  intro p hp
  simp only [Finset.mem_filter, Nat.mem_primeFactors] at hp
  exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp.1.1).mpr hp.2)

theorem coprimeCore_dvd (N n : ℕ) : coprimeCore N n ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [coprimeCore]
  · calc coprimeCore N n ∣ ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
        Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
      _ = n := by
        rw [← Nat.support_factorization]
        exact Nat.prod_factorization_pow_eq_self hn

theorem coprimeCore_eq_self {N n : ℕ} (hn : n ≠ 0) (h : Nat.Coprime n N) :
    coprimeCore N n = n := by
  have hfil : n.primeFactors.filter (fun p => ¬ p ∣ N) = n.primeFactors := by
    refine Finset.filter_true_of_mem ?_
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    exact (Nat.Prime.coprime_iff_not_dvd hp.1).mp (Nat.Coprime.coprime_dvd_left hp.2.1 h)
  rw [coprimeCore, hfil, ← Nat.support_factorization]
  exact Nat.prod_factorization_pow_eq_self hn

theorem coprimeCore_mul {m n : ℕ} (N : ℕ) (h : Nat.Coprime m n) :
    coprimeCore N (m * n) = coprimeCore N m * coprimeCore N n := by
  rcases eq_or_ne m 0 with rfl | hm
  · have hn : n = 1 := Nat.coprime_zero_left n |>.mp h
    subst hn
    simp [coprimeCore]
  rcases eq_or_ne n 0 with rfl | hn
  · have hm1 : m = 1 := Nat.coprime_zero_right m |>.mp h
    subst hm1
    simp [coprimeCore]
  have hdisj : Disjoint m.primeFactors n.primeFactors := Nat.Coprime.disjoint_primeFactors h
  rw [coprimeCore, coprimeCore, coprimeCore, Nat.primeFactors_mul hm hn,
    Finset.filter_union, Finset.prod_union (hdisj.mono (Finset.filter_subset _ _)
      (Finset.filter_subset _ _))]
  congr 1
  · refine Finset.prod_congr rfl ?_
    intro p hp
    simp only [Finset.mem_filter] at hp
    rw [Nat.factorization_mul hm hn]
    simp only [Finsupp.coe_add, Pi.add_apply]
    have : n.factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd
        (fun hpn => (Nat.Prime.coprime_iff_not_dvd (Nat.prime_of_mem_primeFactors hp.1)).mp
          (Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp.1) h) hpn)
    rw [this, add_zero]
  · refine Finset.prod_congr rfl ?_
    intro p hp
    simp only [Finset.mem_filter] at hp
    rw [Nat.factorization_mul hm hn]
    simp only [Finsupp.coe_add, Pi.add_apply]
    have : m.factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd
        (fun hpm => (Nat.Prime.coprime_iff_not_dvd (Nat.prime_of_mem_primeFactors hp.1)).mp
          (Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp.1) h.symm) hpm)
    rw [this, zero_add]

/-- The largest divisor of `n` coprime to `N`, with the coprime case forced to be
the identity even at `n = 0` (which is coprime to `N` exactly when `N = 1`). -/
noncomputable def coprimePart (N n : ℕ) : ℕ :=
  if Nat.Coprime n N then n else coprimeCore N n

theorem coprimePart_eq_self {N n : ℕ} (h : Nat.Coprime n N) : coprimePart N n = n :=
  if_pos h

theorem coprimePart_coprime (N n : ℕ) : Nat.Coprime (coprimePart N n) N := by
  unfold coprimePart
  split
  · assumption
  · exact coprimeCore_coprime N n

theorem coprimePart_dvd (N n : ℕ) : coprimePart N n ∣ n := by
  unfold coprimePart
  split
  · exact dvd_rfl
  · exact coprimeCore_dvd N n

theorem coprimePart_one (N : ℕ) : coprimePart N 1 = 1 :=
  coprimePart_eq_self (Nat.coprime_one_left N)

theorem coprimePart_mul {m n : ℕ} (N : ℕ) (h : Nat.Coprime m n) :
    coprimePart N (m * n) = coprimePart N m * coprimePart N n := by
  by_cases hmn : Nat.Coprime (m * n) N
  · have hm : Nat.Coprime m N := Nat.Coprime.coprime_dvd_left ⟨n, rfl⟩ hmn
    have hn : Nat.Coprime n N := Nat.Coprime.coprime_dvd_left ⟨m, mul_comm m n ▸ rfl⟩ hmn
    rw [coprimePart_eq_self hmn, coprimePart_eq_self hm, coprimePart_eq_self hn]
  · have hcore : ∀ k : ℕ, k ∣ m * n → coprimePart N k = coprimeCore N k := by
      intro k hk
      by_cases hkN : Nat.Coprime k N
      · have hk0 : k ≠ 0 := by
          rintro rfl
          exact hmn (by simpa using (Nat.coprime_zero_left N).mp hkN ▸
            (Nat.coprime_one_right (m * n)))
        rw [coprimePart_eq_self hkN, coprimeCore_eq_self hk0 hkN]
      · exact if_neg hkN
    rw [hcore (m * n) dvd_rfl, hcore m ⟨n, rfl⟩, hcore n ⟨m, mul_comm m n⟩,
      coprimeCore_mul N h]


theorem exists_atkinLehnerDescent_of_factorwise' (N : ℕ) {X Y J : Scheme.{0}}
    {strX : X ⟶ SpecQ} {strY : Y ⟶ SpecQ} {jY : Y ⟶ X}
    (hX : IsX0Compactification N strX strY jY) {jstr : J ⟶ SpecQ}
    {ab : AbelianSchemeStruct jstr} {o : RelPoint strX (𝟙 SpecQ)}
    (jac : IsJacobianOf strX ab o) (wJ : J ⟶ J) (hwJ : wJ ≫ jstr = jstr)
    (D : IsHeckeIsotypicDecomposition N hX jac)
    (F : IsAtkinLehnerFactorwise D wJ hwJ) :
    ∃ D' : IsHeckeIsotypicDecomposition N hX jac, Nonempty (IsAtkinLehnerDescent D' wJ hwJ) := by
  classical
  obtain ⟨SS⟩ : Nonempty (∀ i : D.idx,
      IsInvolutionSignSplitting (D.abA i) (F.wA i) (F.wA_comp i)) :=
    ⟨fun i => Classical.choice (exists_involutionSignSplitting (D.abA i) (F.wA i)
      (F.wA_comp i) (F.wA_add i) (F.wA_invol i))⟩
  -- the descent equation for the anemic Hecke operators
  have hdesc : ∀ (i : D.idx) (b : Bool) (n : ℕ), Nat.Coprime n N →
      D.S i n ≫ (SS i).p b = (SS i).p b ≫ (SS i).desc b (D.S i n) :=
    fun i b n hn => (SS i).desc_spec b (D.S i n) (D.S_comp i n) (F.hecke_comm i n hn)
  -- ISOTYPY, in the form that only needs the descent equation
  have key : ∀ (i : D.idx) (b : Bool) (n : ℕ), Nat.Coprime n N →
      ∀ (s : (SS i).P b ⟶ (SS i).P b) (hs : s ≫ (SS i).pstr b = (SS i).pstr b),
        D.S i n ≫ (SS i).p b = (SS i).p b ≫ s →
      ∀ {T'' : Scheme.{0}} (g : T'' ⟶ SpecQ) (x : RelPoint ((SS i).pstr b) g),
        letI := ((SS i).abP b).addCommGroup g
        ∑ k ∈ Finset.range ((minpoly ℤ (D.coeff i n)).natDegree + 1),
          (minpoly ℤ (D.coeff i n)).coeff k •
            ((fun y : RelPoint ((SS i).pstr b) g => RelPoint.post s hs y)^[k] x) = 0 := by
    intro i b n hn s hs hds T'' g x
    letI := ((SS i).abP b).addCommGroup g
    letI := ((SS i).abP b).addCommGroup ((SS i).pstr b)
    letI := ((SS i).abP b).addCommGroup (D.astr i)
    letI := (D.abA i).addCommGroup (D.astr i)
    -- the universal points
    set x₀ : RelPoint ((SS i).pstr b) ((SS i).pstr b) :=
      ⟨𝟙 ((SS i).P b), Category.id_comp _⟩ with hx₀def
    set y₀ : RelPoint (D.astr i) (D.astr i) := ⟨𝟙 (D.A i), Category.id_comp _⟩ with hy₀def
    -- `p b` intertwines `S i n` with `s`
    have hπcomm : ∀ y : RelPoint (D.astr i) (D.astr i),
        RelPoint.post ((SS i).p b) ((SS i).p_comp b)
            (RelPoint.post (D.S i n) (D.S_comp i n) y)
          = RelPoint.post s hs (RelPoint.post ((SS i).p b) ((SS i).p_comp b) y) := by
      intro y
      refine Subtype.ext ?_
      show (y.1 ≫ D.S i n) ≫ (SS i).p b = (y.1 ≫ (SS i).p b) ≫ s
      rw [Category.assoc, Category.assoc, hds]
    have hx₀p : RelPoint.pre ((SS i).p b) ((SS i).p_comp b) x₀
        = RelPoint.post ((SS i).p b) ((SS i).p_comp b) y₀ := by
      refine Subtype.ext ?_
      show (SS i).p b ≫ 𝟙 ((SS i).P b) = 𝟙 (D.A i) ≫ (SS i).p b
      rw [Category.comp_id, Category.id_comp]
    -- STEP 1: the identity at the universal point of `P b`
    have hZ : (∑ k ∈ Finset.range ((minpoly ℤ (D.coeff i n)).natDegree + 1),
          (minpoly ℤ (D.coeff i n)).coeff k •
            ((fun y : RelPoint ((SS i).pstr b) ((SS i).pstr b) =>
              RelPoint.post s hs y)^[k] x₀))
        = ((SS i).abP b).zero ((SS i).pstr b) := by
      haveI := (SS i).p_epi b
      have hρ : RelPoint.pre ((SS i).p b) ((SS i).p_comp b)
            (∑ k ∈ Finset.range ((minpoly ℤ (D.coeff i n)).natDegree + 1),
              (minpoly ℤ (D.coeff i n)).coeff k •
                ((fun y : RelPoint ((SS i).pstr b) ((SS i).pstr b) =>
                  RelPoint.post s hs y)^[k] x₀))
          = ((SS i).abP b).zero (D.astr i) := by
        calc RelPoint.pre ((SS i).p b) ((SS i).p_comp b)
              (∑ k ∈ Finset.range ((minpoly ℤ (D.coeff i n)).natDegree + 1),
                (minpoly ℤ (D.coeff i n)).coeff k •
                  ((fun y : RelPoint ((SS i).pstr b) ((SS i).pstr b) =>
                    RelPoint.post s hs y)^[k] x₀))
            = ∑ k ∈ Finset.range ((minpoly ℤ (D.coeff i n)).natDegree + 1),
                (minpoly ℤ (D.coeff i n)).coeff k •
                  ((fun y : RelPoint ((SS i).pstr b) (D.astr i) =>
                    RelPoint.post s hs y)^[k]
                    (RelPoint.pre ((SS i).p b) ((SS i).p_comp b) x₀)) :=
              sum_zsmul_iterate_map _
                (((SS i).abP b).pre_add ((SS i).p b) ((SS i).p_comp b))
                (fun y => RelPoint.post s hs y) (fun y => RelPoint.post s hs y)
                (fun z => (RelPoint.post_pre s hs ((SS i).p b) ((SS i).p_comp b) z).symm)
                (fun k => (minpoly ℤ (D.coeff i n)).coeff k) _ x₀
          _ = ∑ k ∈ Finset.range ((minpoly ℤ (D.coeff i n)).natDegree + 1),
                (minpoly ℤ (D.coeff i n)).coeff k •
                  ((fun y : RelPoint ((SS i).pstr b) (D.astr i) =>
                    RelPoint.post s hs y)^[k]
                    (RelPoint.post ((SS i).p b) ((SS i).p_comp b) y₀)) := by rw [hx₀p]
          _ = RelPoint.post ((SS i).p b) ((SS i).p_comp b)
                (∑ k ∈ Finset.range ((minpoly ℤ (D.coeff i n)).natDegree + 1),
                  (minpoly ℤ (D.coeff i n)).coeff k •
                    ((fun y : RelPoint (D.astr i) (D.astr i) =>
                      RelPoint.post (D.S i n) (D.S_comp i n) y)^[k] y₀)) :=
              (sum_zsmul_iterate_map _ ((SS i).p_add b)
                (fun y => RelPoint.post (D.S i n) (D.S_comp i n) y)
                (fun y => RelPoint.post s hs y) hπcomm
                (fun k => (minpoly ℤ (D.coeff i n)).coeff k) _ y₀).symm
          _ = RelPoint.post ((SS i).p b) ((SS i).p_comp b) ((D.abA i).zero (D.astr i)) :=
              congrArg _ (D.isotypic i n hn (D.astr i) y₀)
          _ = ((SS i).abP b).zero (D.astr i) := IsAdditiveOn.post_zero ((SS i).p_add b) _
      have hρ' := hρ.trans (((SS i).abP b).pre_zero ((SS i).p b) ((SS i).p_comp b)).symm
      have hval := congrArg Subtype.val hρ'
      exact Subtype.ext ((cancel_epi ((SS i).p b)).mp hval)
    -- STEP 2: pull it back to an arbitrary point
    have hx : RelPoint.pre x.1 x.2 x₀ = x := Subtype.ext (Category.comp_id _)
    calc (∑ k ∈ Finset.range ((minpoly ℤ (D.coeff i n)).natDegree + 1),
            (minpoly ℤ (D.coeff i n)).coeff k •
              ((fun y : RelPoint ((SS i).pstr b) g => RelPoint.post s hs y)^[k] x))
        = ∑ k ∈ Finset.range ((minpoly ℤ (D.coeff i n)).natDegree + 1),
            (minpoly ℤ (D.coeff i n)).coeff k •
              ((fun y : RelPoint ((SS i).pstr b) g => RelPoint.post s hs y)^[k]
                (RelPoint.pre x.1 x.2 x₀)) := by rw [hx]
      _ = RelPoint.pre x.1 x.2
            (∑ k ∈ Finset.range ((minpoly ℤ (D.coeff i n)).natDegree + 1),
              (minpoly ℤ (D.coeff i n)).coeff k •
                ((fun y : RelPoint ((SS i).pstr b) ((SS i).pstr b) =>
                  RelPoint.post s hs y)^[k] x₀)) :=
          (sum_zsmul_iterate_map _ (((SS i).abP b).pre_add x.1 x.2)
            (fun y => RelPoint.post s hs y) (fun y => RelPoint.post s hs y)
            (fun z => (RelPoint.post_pre s hs x.1 x.2 z).symm)
            (fun k => (minpoly ℤ (D.coeff i n)).coeff k) _ x₀).symm
      _ = RelPoint.pre x.1 x.2 (((SS i).abP b).zero ((SS i).pstr b)) := congrArg _ hZ
      _ = 0 := ((SS i).abP b).pre_zero x.1 x.2
  refine ⟨{
      T := fun n => D.T (coprimePart N n)
      T_comp := fun n => D.T_comp (coprimePart N n)
      T_add := fun n => D.T_add (coprimePart N n)
      heckeModuli := ?_
      idx := D.idx × Bool
      fintypeIdx := ?_
      A := fun j => (SS j.1).P j.2
      astr := fun j => (SS j.1).pstr j.2
      abA := fun j => (SS j.1).abP j.2
      u := fun j => D.u j.1 ≫ (SS j.1).p j.2
      u_comp := ?_
      u_add := ?_
      u_surj := ?_
      form := fun j => D.form j.1
      coeff := fun j => D.coeff j.1
      isEigen := fun j => D.isEigen j.1
      S := fun j n => (SS j.1).desc j.2 (D.S j.1 (coprimePart N n))
      S_comp := fun j n => (SS j.1).desc_comp j.2 _
      S_add := fun j n => (SS j.1).desc_add j.2 _
      equivariant := ?_
      integral := fun j n => D.integral j.1 n
      isotypic := ?_
      cover := ?_
      finite_ker := ?_ }, ⟨{
      Plus := fun j => j.2 = true
      descend_plus := ?_
      descend_minus := ?_ }⟩⟩
  · -- heckeModuli
    refine ⟨?_, ?_, ?_, ?_⟩
    · show D.T (coprimePart N 1) = 𝟙 J
      rw [coprimePart_one]; exact D.heckeModuli.1
    · intro m n hmn
      show D.T (coprimePart N (m * n))
        = D.T (coprimePart N m) ≫ D.T (coprimePart N n)
      rw [coprimePart_mul N hmn]
      exact D.heckeModuli.2.1 _ _
        (Nat.Coprime.coprime_dvd_left (coprimePart_dvd N m)
          (Nat.Coprime.coprime_dvd_right (coprimePart_dvd N n) hmn))
    · intro l k hl hlN T'' g x
      have hlc : Nat.Coprime l N := (Nat.Prime.coprime_iff_not_dvd hl).mpr hlN
      have e2 : coprimePart N (l ^ (k + 2)) = l ^ (k + 2) :=
        coprimePart_eq_self (Nat.Coprime.pow_left _ hlc)
      have e1 : coprimePart N (l ^ (k + 1)) = l ^ (k + 1) :=
        coprimePart_eq_self (Nat.Coprime.pow_left _ hlc)
      have e0 : coprimePart N (l ^ k) = l ^ k :=
        coprimePart_eq_self (Nat.Coprime.pow_left _ hlc)
      have el : coprimePart N l = l := coprimePart_eq_self hlc
      simp only [e0, e1, e2, el]
      exact D.heckeModuli.2.2.1 l k hl hlN g x
    · intro l hl hlN d m dq iso hinj hsurj
      have hlc : Nat.Coprime l N := (Nat.Prime.coprime_iff_not_dvd hl).mpr hlN
      exact (RelPoint.post_congr (congrArg D.T (coprimePart_eq_self hlc)) _).trans
        (D.heckeModuli.2.2.2 l hl hlN d m dq iso hinj hsurj)
  · -- fintypeIdx
    letI := D.fintypeIdx
    exact inferInstance
  · -- u_comp
    intro j
    rw [Category.assoc, (SS j.1).p_comp j.2, D.u_comp j.1]
  · -- u_add
    intro j
    exact IsAdditiveOn.comp (D.u_add j.1) ((SS j.1).p_add j.2)
  · -- u_surj
    intro j
    haveI := D.u_surj j.1
    haveI := (SS j.1).p_surj j.2
    exact inferInstance
  · -- equivariant
    intro j n
    rw [← Category.assoc, D.equivariant j.1 (coprimePart N n), Category.assoc,
      hdesc j.1 j.2 (coprimePart N n) (coprimePart_coprime N n), ← Category.assoc]
  · -- isotypic
    rintro ⟨i, b⟩ n hn T'' g x
    exact key i b n hn _ _ (by rw [coprimePart_eq_self hn]; exact hdesc i b n hn) g x
  · -- cover
    intro f a hf
    obtain ⟨i, hi⟩ := D.cover f a hf
    exact ⟨(i, true), hi⟩
  · -- finite_ker
    letI : ∀ i : D.idx, AddCommGroup (RelPoint (D.astr i) (𝟙 SpecQ)) :=
      fun i => (D.abA i).addCommGroup (𝟙 SpecQ)
    letI := ab.addCommGroup (𝟙 SpecQ)
    letI := D.fintypeIdx
    have hK : ∀ i : D.idx, {y : RelPoint (D.astr i) (𝟙 SpecQ) |
        ∀ b, RelPoint.post ((SS i).p b) ((SS i).p_comp b) y
          = ((SS i).abP b).zero (𝟙 SpecQ)}.Finite := fun i => (SS i).ker_finite
    have hbig := finite_preimage_of_finite_ker
      (fun x : RelPoint jstr (𝟙 SpecQ) =>
        fun i : D.idx => RelPoint.post (D.u i) (D.u_comp i) x)
      (fun x y => funext fun i => D.u_add i x y)
      (Set.Finite.subset D.finite_ker (fun x hx i => congrFun hx i))
      (Set.Finite.pi hK)
    refine Set.Finite.subset hbig ?_
    intro x hx
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, Set.mem_setOf_eq, forall_true_left]
    intro i b
    rw [← RelPoint.post_comp (D.u i) (D.u_comp i) ((SS i).p b) ((SS i).p_comp b)]
    exact hx (i, b)
  · -- descend_plus
    rintro ⟨i, b⟩ hb T g x
    simp only at hb
    subst hb
    rw [RelPoint.post_comp (D.u i) (D.u_comp i) ((SS i).p true) ((SS i).p_comp true),
      RelPoint.post_comp (D.u i) (D.u_comp i) ((SS i).p true) ((SS i).p_comp true),
      F.descend i x, (SS i).sign_plus]
  · -- descend_minus
    rintro ⟨i, b⟩ hb T g x
    simp only at hb
    have hb' : b = false := by
      cases b
      · rfl
      · exact absurd rfl hb
    subst hb'
    rw [RelPoint.post_comp (D.u i) (D.u_comp i) ((SS i).p false) ((SS i).p_comp false),
      RelPoint.post_comp (D.u i) (D.u_comp i) ((SS i).p false) ((SS i).p_comp false),
      F.descend i x, (SS i).sign_minus]


end Scratch31
