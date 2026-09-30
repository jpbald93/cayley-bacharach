import CayleyBacharach.Theorem

/-!
# The general-position hypotheses from "no common factor"

If two cubics `F, G` through eight pairwise non-proportional points have no common linear
factor and no common conic factor, then the eight points satisfy the general-position
criterion: no four (in particular no five) are collinear, and they do not all lie on a
nonzero conic. Consequently Cayley–Bacharach holds under the no-common-factor hypothesis.
-/

open Matrix

namespace PlaneCubic

variable {K : Type*} [Field K]

/-- Four of the points on a line force the line into every cubic through the points. -/
theorem divides_of_four [AtLeastThree K] {n : ℕ} (P : Fin n → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0) {ℓ : Fin 3 → K} (hℓ : ℓ ≠ 0)
    (s : Finset (Fin n)) (hs : ∀ i ∈ s, ℓ ⬝ᵥ P i = 0) (h4 : 4 ≤ s.card)
    (F : PlaneCubic K) (hF : ∀ i, eval F (P i) = 0) : ∃ q, F = mulLin ℓ q := by
  classical
  obtain ⟨t, hts, ht⟩ := Finset.exists_subset_card_eq h4
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_four.mp ht
  exact cubic_four hℓ (hP a b hab) (hP a c hac) (hP b c hbc) (hP a d had) (hP b d hbd)
    (hP c d hcd) (hs a (hts (by simp))) (hs b (hts (by simp))) (hs c (hts (by simp)))
    (hs d (hts (by simp))) (hF a) (hF b) (hF c) (hF d)

/-- No three collinear ⇒ no four collinear (the first three indices distinct suffice). -/
theorem not_col4_of_no3 {n : ℕ} {P : Fin n → Fin 3 → K}
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0)
    (hno3 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → P i ⨯₃ P j ⬝ᵥ P k ≠ 0)
    {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ Col4 (P a) (P b) (P c) (P d) := by
  rintro ⟨M, hM, ha, hb, hc, -⟩
  obtain ⟨c', rfl⟩ := lin_two (hP a b hab) ha hb
  have hc0 : c' ≠ 0 := by rintro rfl; exact hM (zero_smul _ _)
  rw [smul_dotProduct, smul_eq_mul] at hc
  exact hno3 a b c hab hac hbc ((mul_eq_zero.mp hc).resolve_left hc0)

/-- Eight points with no three collinear: the cubics through them have dimension `≤ 3`. -/
theorem finrank_le_three_of_no3 [AtLeastThree K] (P : Fin 8 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0)
    (hno3 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → P i ⨯₃ P j ⬝ᵥ P k ≠ 0) :
    Module.finrank K (cubicsThrough (Set.range P)) ≤ 3 := by
  classical
  set u := P 0
  set v := P 1
  have huv : u ⨯₃ v ≠ 0 := hP 0 1 (by decide)
  obtain ⟨t, ht⟩ := AtLeastThree.exists_ne (K := K)
  set Q1 := u + v
  set Q2 := u + t • v
  have e1 : u ⨯₃ Q1 ≠ 0 := by rw [cross_add_right]; exact huv
  have e2 : v ⨯₃ Q1 ≠ 0 := by rw [cross_add_right']; exact neg_ne_zero.mpr huv
  have e3 : u ⨯₃ Q2 ≠ 0 := by
    have : u ⨯₃ Q2 = t • (u ⨯₃ v) := by
      ext i; fin_cases i <;> simp [Q2, cross_apply] <;> ring
    rw [this]; exact smul_ne_zero ht.1 huv
  have e4 : v ⨯₃ Q2 ≠ 0 := by
    have : v ⨯₃ Q2 = -(u ⨯₃ v) := by
      ext i; fin_cases i <;> simp [Q2, cross_apply] <;> ring
    rw [this]; exact neg_ne_zero.mpr huv
  have e5 : Q1 ⨯₃ Q2 ≠ 0 := by
    have : Q1 ⨯₃ Q2 = (t - 1) • (u ⨯₃ v) := by
      ext i; fin_cases i <;> simp [Q1, Q2, cross_apply] <;> ring
    rw [this]; exact smul_ne_zero (sub_ne_zero.mpr ht.2) huv
  set ℓ := u ⨯₃ v
  have l1 : ℓ ⬝ᵥ Q1 = 0 := cross_add_dot u v
  have l2 : ℓ ⬝ᵥ Q2 = 0 := by
    rw [dotProduct_add, dotProduct_smul, cross_dot_left, cross_dot_right]; simp
  set S := Set.range P
  set S' := insert Q1 (insert Q2 S)
  have hS'1 : Module.finrank K (cubicsThrough (insert Q2 S)) ≤
      Module.finrank K (cubicsThrough S') + 1 := cubics_insert Q1 (insert Q2 S)
  have hS'2 := cubics_insert Q2 S
  have hr := cubics_resid huv huv e1 e2 e3 e4 e5 (cross_dot_left u v) (cross_dot_right u v)
    l1 l2 S' (by simp [S', S, u]) (by simp [S', S, v]) (by simp [S']) (by simp [S'])
  have mem : ∀ k : Fin 8, 2 ≤ k.val → P k ∈ {x | x ∈ S' ∧ ℓ ⬝ᵥ x ≠ 0} := fun k hk =>
    ⟨Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_range_self k)),
      hno3 0 1 k (by decide) (by intro h; subst h; simp at hk)
        (by intro h; subst h; simp at hk)⟩
  have h1 := conics_le_one _ (mem 2 (by decide)) (mem 3 (by decide)) (mem 4 (by decide))
    (mem 5 (by decide)) (mem 6 (by decide))
    (hP 2 3 (by decide)) (hP 2 4 (by decide)) (hP 2 5 (by decide)) (hP 2 6 (by decide))
    (hP 3 4 (by decide)) (hP 3 5 (by decide)) (hP 3 6 (by decide))
    (hP 4 5 (by decide)) (hP 4 6 (by decide)) (hP 5 6 (by decide))
    (not_col4_of_no3 hP hno3 (d := 5) (by decide) (by decide) (by decide))
    (not_col4_of_no3 hP hno3 (d := 6) (by decide) (by decide) (by decide))
    (not_col4_of_no3 hP hno3 (d := 6) (by decide) (by decide) (by decide))
    (not_col4_of_no3 hP hno3 (d := 6) (by decide) (by decide) (by decide))
    (not_col4_of_no3 hP hno3 (d := 6) (by decide) (by decide) (by decide))
  omega

/-- **No common factor ⇒ general position.** Let `F, G` be cubics through eight pairwise
non-proportional points with no common linear factor and no common conic factor. Then no
four of the points are collinear and the points do not all lie on a nonzero conic. -/
theorem general_position_of_no_common_factor [AtLeastThree K] (P : Fin 8 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0) (F G : PlaneCubic K)
    (hF : ∀ i, eval F (P i) = 0) (hG : ∀ i, eval G (P i) = 0)
    (hlin : ¬ ∃ ℓ q q', ℓ ≠ 0 ∧ F = mulLin ℓ q ∧ G = mulLin ℓ q')
    (hcon : ¬ ∃ q m m', q ≠ 0 ∧ F = mulLin m q ∧ G = mulLin m' q) :
    (∀ ℓ : Fin 3 → K, ℓ ≠ 0 → ∀ s : Finset (Fin 8), (∀ i ∈ s, ℓ ⬝ᵥ P i = 0) →
      s.card ≤ 3) ∧
    (∀ q : Fin 6 → K, (∀ i, evalC q (P i) = 0) → q = 0) := by
  classical
  have h4 : ∀ ℓ : Fin 3 → K, ℓ ≠ 0 → ∀ s : Finset (Fin 8), (∀ i ∈ s, ℓ ⬝ᵥ P i = 0) →
      s.card ≤ 3 := by
    intro ℓ hℓ s hs
    by_contra hc
    obtain ⟨q, hq⟩ := divides_of_four P hP hℓ s hs (by omega) F hF
    obtain ⟨q', hq'⟩ := divides_of_four P hP hℓ s hs (by omega) G hG
    exact hlin ⟨ℓ, q, q', hℓ, hq, hq'⟩
  refine ⟨h4, fun q hq => ?_⟩
  by_contra hq0
  by_cases hc : ∃ i j k : Fin 8, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ P i ⨯₃ P j ⬝ᵥ P k = 0
  · obtain ⟨i, j, k, hij, hik, hjk, hc⟩ := hc
    set ℓ := P i ⨯₃ P j
    obtain ⟨m, hm⟩ := conic_three (hP i j hij) (hP i j hij) (hP i k hik) (hP j k hjk)
      (cross_dot_left _ _) (cross_dot_right _ _) hc (hq i) (hq j) (hq k)
    have hm0 : m ≠ 0 := by
      rintro rfl; apply hq0; rw [hm]; ext x; fin_cases x <;> simp [linMul]
    have cover : (Finset.univ : Finset (Fin 8)) ⊆
        (Finset.univ.filter fun x => ℓ ⬝ᵥ P x = 0) ∪
          (Finset.univ.filter fun x => m ⬝ᵥ P x = 0) := by
      intro x _
      have := hq x
      rw [hm, evalC_linMul] at this
      rcases mul_eq_zero.mp this with h | h <;> simp [ℓ, h]
    have c1 := h4 ℓ (hP i j hij) (Finset.univ.filter fun x => ℓ ⬝ᵥ P x = 0)
      (fun x hx => (Finset.mem_filter.mp hx).2)
    have c2 := h4 m hm0 (Finset.univ.filter fun x => m ⬝ᵥ P x = 0)
      (fun x hx => (Finset.mem_filter.mp hx).2)
    have := (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  · push Not at hc
    have hdim := finrank_le_three_of_no3 P hP hc
    have hle : LinearMap.range (mulConicLin q) ≤ cubicsThrough (Set.range P) := by
      rintro _ ⟨m, rfl⟩ _ ⟨i, rfl⟩
      simp only [mulConicLin, LinearMap.coe_mk, AddHom.coe_mk, eval_mulLin]
      rw [show conicEval q (P i) = 0 from hq i, mul_zero]
    have h3 : Module.finrank K (LinearMap.range (mulConicLin q)) = 3 := by
      rw [LinearMap.finrank_range_of_inj (mulConicLin_injective hq0)]
      simp
    have heq := Submodule.eq_of_le_of_finrank_le hle (by rw [h3]; exact hdim)
    have hFm : F ∈ LinearMap.range (mulConicLin q) := by
      rw [heq]; rintro _ ⟨i, rfl⟩; exact hF i
    have hGm : G ∈ LinearMap.range (mulConicLin q) := by
      rw [heq]; rintro _ ⟨i, rfl⟩; exact hG i
    obtain ⟨m, hm⟩ := hFm
    obtain ⟨m', hm'⟩ := hGm
    exact hcon ⟨q, m, m', hq0, hm.symm, hm'.symm⟩

/-- **Cayley–Bacharach, no-common-factor form.** Let `F, G` be linearly independent cubics
through nine pairwise non-proportional points `P 0, …, P 8`, with no common linear factor
and no common conic factor. Every cubic through `P 0, …, P 7` passes through `P 8`. -/
theorem cayley_bacharach_of_no_common_factor [AtLeastThree K] (P : Fin 9 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0)
    (F G : PlaneCubic K) (hFG : LinearIndependent K ![F, G])
    (hF : ∀ i, eval F (P i) = 0) (hG : ∀ i, eval G (P i) = 0)
    (hlin : ¬ ∃ ℓ q q', ℓ ≠ 0 ∧ F = mulLin ℓ q ∧ G = mulLin ℓ q')
    (hcon : ¬ ∃ q m m', q ≠ 0 ∧ F = mulLin m q ∧ G = mulLin m' q)
    (H : PlaneCubic K) (hH : ∀ i : Fin 8, eval H (P (Fin.castSucc i)) = 0) :
    eval H (P 8) = 0 := by
  have hP' : ∀ i j : Fin 8, i ≠ j → P (Fin.castSucc i) ⨯₃ P (Fin.castSucc j) ≠ 0 :=
    fun i j hij => hP _ _ (fun h => hij (Fin.castSucc_injective _ h))
  obtain ⟨h4, hconic⟩ := general_position_of_no_common_factor (fun i => P (Fin.castSucc i))
    hP' F G (fun i => hF _) (fun i => hG _) hlin hcon
  exact cayley_bacharach P hP (fun ℓ hℓ s hs => (h4 ℓ hℓ s hs).trans (by decide)) hconic
    F G hFG hF hG H hH

end PlaneCubic
