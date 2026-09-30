import CayleyBacharach.Hard

/-!
# The general-position criterion (hard direction)

Eight pairwise non-proportional points, no five collinear and not all on a nonzero conic,
impose independent conditions on plane cubics: the cubics through them form a space of
dimension exactly `2`.
-/

open Matrix

namespace PlaneCubic

variable {K : Type*} [Field K]

section Dec

variable [DecidableEq K]

/-- Indices of the points lying on the line `ℓ = 0`. -/
def onLine {n : ℕ} (P : Fin n → Fin 3 → K) (ℓ : Fin 3 → K) : Finset (Fin n) :=
  Finset.univ.filter fun i => ℓ ⬝ᵥ P i = 0

theorem mem_onLine {n : ℕ} {P : Fin n → Fin 3 → K} {ℓ : Fin 3 → K} {i : Fin n} :
    i ∈ onLine P ℓ ↔ ℓ ⬝ᵥ P i = 0 := by simp [onLine]

theorem card_offLine {n : ℕ} (P : Fin n → Fin 3 → K) (ℓ : Fin 3 → K) :
    (Finset.univ.filter fun i => ¬ ℓ ⬝ᵥ P i = 0).card = n - (onLine P ℓ).card := by
  have := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun i : Fin n => ℓ ⬝ᵥ P i = 0)
  simp only [Finset.card_univ, Fintype.card_fin] at this
  unfold onLine
  omega

/-- If no line carries four of the points, no four distinct ones are collinear. -/
theorem not_col4 {n : ℕ} {P : Fin n → Fin 3 → K}
    (h3 : ∀ ℓ : Fin 3 → K, ℓ ≠ 0 → (onLine P ℓ).card ≤ 3) {a b c d : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ¬ Col4 (P a) (P b) (P c) (P d) := by
  rintro ⟨M, hM, ha, hb, hc, hd⟩
  have hsub : ({a, b, c, d} : Finset (Fin n)) ⊆ onLine P M := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [mem_onLine, *]
  have h4 : ({a, b, c, d} : Finset (Fin n)).card = 4 :=
    Finset.card_eq_four.mpr ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩
  have := Finset.card_le_card hsub
  have := h3 M hM
  omega

/-- **Case A.** Some line carries exactly four of the eight points. -/
theorem caseA [AtLeastThree K] (P : Fin 8 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0)
    (hconic : ∀ q : Fin 6 → K, (∀ i, evalC q (P i) = 0) → q = 0)
    {ℓ : Fin 3 → K} (hℓ : ℓ ≠ 0) (hA : (onLine P ℓ).card = 4) :
    Module.finrank K (cubicsThrough (Set.range P)) ≤ 2 := by
  obtain ⟨i, j, k, m, hij, hik, him, hjk, hjm, hkm, hA'⟩ := Finset.card_eq_four.mp hA
  have hi : ℓ ⬝ᵥ P i = 0 := mem_onLine.mp (by rw [hA']; simp)
  have hj : ℓ ⬝ᵥ P j = 0 := mem_onLine.mp (by rw [hA']; simp)
  have hk : ℓ ⬝ᵥ P k = 0 := mem_onLine.mp (by rw [hA']; simp)
  have hm : ℓ ⬝ᵥ P m = 0 := mem_onLine.mp (by rw [hA']; simp)
  have hB : (Finset.univ.filter fun x => ¬ ℓ ⬝ᵥ P x = 0).card = 4 := by
    rw [card_offLine, hA]
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hB'⟩ := Finset.card_eq_four.mp hB
  have memB : ∀ x, x ∈ (Finset.univ.filter fun x => ¬ ℓ ⬝ᵥ P x = 0) ↔ ℓ ⬝ᵥ P x ≠ 0 :=
    fun x => by simp
  have ha : ℓ ⬝ᵥ P a ≠ 0 := (memB a).mp (by rw [hB']; simp)
  have hb : ℓ ⬝ᵥ P b ≠ 0 := (memB b).mp (by rw [hB']; simp)
  have hc : ℓ ⬝ᵥ P c ≠ 0 := (memB c).mp (by rw [hB']; simp)
  have hd : ℓ ⬝ᵥ P d ≠ 0 := (memB d).mp (by rw [hB']; simp)
  have hS := cubics_resid hℓ (hP i j hij) (hP i k hik) (hP j k hjk) (hP i m him)
    (hP j m hjm) (hP k m hkm) hi hj hk hm (Set.range P) (Set.mem_range_self i)
    (Set.mem_range_self j) (Set.mem_range_self k) (Set.mem_range_self m)
  refine hS.trans ?_
  refine conics_le_two _ (u := P a) (v := P b) (w := P c) (z := P d)
    ⟨Set.mem_range_self a, ha⟩ ⟨Set.mem_range_self b, hb⟩ ⟨Set.mem_range_self c, hc⟩
    ⟨Set.mem_range_self d, hd⟩ (hP a b hab) (hP a c hac) (hP b c hbc) (hP a d had)
    (hP b d hbd) (hP c d hcd) ?_
  intro M hM Ma Mb Mc Md
  apply hM
  apply linMul_eq_zero hℓ
  apply hconic
  intro x
  rw [evalC_linMul]
  by_cases hx : ℓ ⬝ᵥ P x = 0
  · simp [hx]
  · have hxB := (memB x).mpr hx
    rw [hB'] at hxB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxB
    rcases hxB with rfl | rfl | rfl | rfl <;> simp [*]

/-- **Case B.** No line carries four points, but three of them are collinear. -/
theorem caseB [AtLeastThree K] (P : Fin 8 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0)
    (h3 : ∀ ℓ : Fin 3 → K, ℓ ≠ 0 → (onLine P ℓ).card ≤ 3)
    {i j k : Fin 8} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hcol : P i ⨯₃ P j ⬝ᵥ P k = 0)
    (hd : 3 ≤ Module.finrank K (cubicsThrough (Set.range P))) : False := by
  have hY := conics_off_line_ge_two (Set.mem_range_self i) (Set.mem_range_self j)
    (Set.mem_range_self k) (hP i j hij) (hP i k hik) (hP j k hjk) hcol hd
  set ℓ := P i ⨯₃ P j
  have hB : 5 ≤ (Finset.univ.filter fun x => ¬ ℓ ⬝ᵥ P x = 0).card := by
    rw [card_offLine]
    have := h3 ℓ (hP i j hij)
    omega
  obtain ⟨t, htB, ht⟩ := Finset.exists_subset_card_eq hB
  obtain ⟨a, t', hat', hins, ht'⟩ := Finset.card_eq_succ.mp (show t.card = 4 + 1 from ht)
  obtain ⟨b, c, d, e, hbc, hbd, hbe, hcd, hce, hde, ht''⟩ := Finset.card_eq_four.mp ht'
  have mem : ∀ x, x ∈ t → P x ∈ {v | v ∈ Set.range P ∧ ℓ ⬝ᵥ v ≠ 0} := fun x hx => by
    have := htB hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact ⟨Set.mem_range_self x, this⟩
  have ta : a ∈ t := by rw [← hins]; simp
  have tb : b ∈ t := by rw [← hins, ht'']; simp
  have tc : c ∈ t := by rw [← hins, ht'']; simp
  have td : d ∈ t := by rw [← hins, ht'']; simp
  have te : e ∈ t := by rw [← hins, ht'']; simp
  have hab : a ≠ b := fun h => hat' (by rw [ht'', h]; simp)
  have hac : a ≠ c := fun h => hat' (by rw [ht'', h]; simp)
  have had : a ≠ d := fun h => hat' (by rw [ht'', h]; simp)
  have hae : a ≠ e := fun h => hat' (by rw [ht'', h]; simp)
  have h1 := conics_le_one _ (mem a ta) (mem b tb) (mem c tc) (mem d td) (mem e te)
    (hP a b hab) (hP a c hac) (hP a d had) (hP a e hae) (hP b c hbc) (hP b d hbd)
    (hP b e hbe) (hP c d hcd) (hP c e hce) (hP d e hde)
    (not_col4 h3 hab hac had hbc hbd hcd) (not_col4 h3 hab hac hae hbc hbe hce)
    (not_col4 h3 hab had hae hbd hbe hde) (not_col4 h3 hac had hae hcd hce hde)
    (not_col4 h3 hbc hbd hbe hcd hce hde)
  omega

/-- **Case C.** No three of the points are collinear. -/
theorem caseC [AtLeastThree K] (P : Fin 8 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0)
    (h3 : ∀ ℓ : Fin 3 → K, ℓ ≠ 0 → (onLine P ℓ).card ≤ 3)
    (hno3 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → P i ⨯₃ P j ⬝ᵥ P k ≠ 0)
    (hconic : ∀ q : Fin 6 → K, (∀ i, evalC q (P i) = 0) → q = 0)
    (hd : 3 ≤ Module.finrank K (cubicsThrough (Set.range P))) : False := by
  have X : ∀ i j : Fin 8, i ≠ j → ∃ q : Fin 6 → K, q ≠ 0 ∧
      ∀ k, i ≠ k → j ≠ k → evalC q (P k) = 0 := by
    intro i j hij
    obtain ⟨q, hq0, hq⟩ := exists_conic_off_line (Set.mem_range_self i)
      (Set.mem_range_self j) (hP i j hij) hd
    exact ⟨q, hq0, fun k hik hjk => hq _ (Set.mem_range_self k) (hno3 i j k hij hik hjk)⟩
  obtain ⟨q1, h10, h1⟩ := X 0 1 (by decide)
  obtain ⟨q2, h20, h2⟩ := X 0 2 (by decide)
  obtain ⟨q3, h30, h3'⟩ := X 1 2 (by decide)
  set W := conicsThrough ({P 3, P 4, P 5, P 6, P 7} : Set (Fin 3 → K))
  have hW : Module.finrank K W ≤ 1 :=
    conics_le_one _ (by simp) (by simp) (by simp) (by simp) (by simp)
      (hP 3 4 (by decide)) (hP 3 5 (by decide)) (hP 3 6 (by decide)) (hP 3 7 (by decide))
      (hP 4 5 (by decide)) (hP 4 6 (by decide)) (hP 4 7 (by decide))
      (hP 5 6 (by decide)) (hP 5 7 (by decide)) (hP 6 7 (by decide))
      (not_col4 h3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (not_col4 h3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (not_col4 h3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (not_col4 h3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (not_col4 h3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have inW : ∀ q : Fin 6 → K, (∀ k : Fin 8, 3 ≤ k.val → evalC q (P k) = 0) → q ∈ W := by
    intro q hq v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl <;> exact hq _ (by decide)
  have g1 : ∀ k : Fin 8, 3 ≤ k.val → evalC q1 (P k) = 0 := fun k hk =>
    h1 k (by intro h; subst h; simp at hk) (by intro h; subst h; simp at hk)
  have g2 : ∀ k : Fin 8, 3 ≤ k.val → evalC q2 (P k) = 0 := fun k hk =>
    h2 k (by intro h; subst h; simp at hk) (by intro h; subst h; simp at hk)
  have g3 : ∀ k : Fin 8, 3 ≤ k.val → evalC q3 (P k) = 0 := fun k hk =>
    h3' k (by intro h; subst h; simp at hk) (by intro h; subst h; simp at hk)
  obtain ⟨c, -, hc⟩ := proportional hW (inW q1 g1) (inW q2 g2) h10 h20
  obtain ⟨c', -, hc'⟩ := proportional hW (inW q1 g1) (inW q3 g3) h10 h30
  apply h10
  apply hconic
  intro k
  by_cases hk0 : k = 0
  · subst hk0
    rw [hc', evalC_smul, h3' 0 (by decide) (by decide), mul_zero]
  by_cases hk1 : k = 1
  · subst hk1
    rw [hc, evalC_smul, h2 1 (by decide) (by decide), mul_zero]
  exact h1 k (Ne.symm hk0) (Ne.symm hk1)

end Dec

/-- **Hard direction of the criterion.** Eight pairwise non-proportional points, no five of
them collinear, not all on a nonzero conic: the cubics through them have dimension `≤ 2`. -/
theorem finrank_cubicsThrough_le_two [AtLeastThree K] (P : Fin 8 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0)
    (h5 : ∀ ℓ : Fin 3 → K, ℓ ≠ 0 → ∀ s : Finset (Fin 8), (∀ i ∈ s, ℓ ⬝ᵥ P i = 0) →
      s.card ≤ 4)
    (hconic : ∀ q : Fin 6 → K, (∀ i, evalC q (P i) = 0) → q = 0) :
    Module.finrank K (cubicsThrough (Set.range P)) ≤ 2 := by
  classical
  by_cases h4 : ∃ ℓ : Fin 3 → K, ℓ ≠ 0 ∧ 4 ≤ (onLine P ℓ).card
  · obtain ⟨ℓ, hℓ, h⟩ := h4
    have := h5 ℓ hℓ (onLine P ℓ) (fun i hi => mem_onLine.mp hi)
    exact caseA P hP hconic hℓ (by omega)
  push Not at h4
  have h3 : ∀ ℓ : Fin 3 → K, ℓ ≠ 0 → (onLine P ℓ).card ≤ 3 := fun ℓ hℓ => by
    have := h4 ℓ hℓ; omega
  by_contra hd
  push Not at hd
  by_cases hc : ∃ i j k : Fin 8, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ P i ⨯₃ P j ⬝ᵥ P k = 0
  · obtain ⟨i, j, k, hij, hik, hjk, hc⟩ := hc
    exact caseB P hP h3 hij hik hjk hc hd
  · push Not at hc
    exact caseC P hP h3 hc hconic hd

/-- **The general-position criterion.** Under the same hypotheses, the kernel of the
evaluation map on cubics has dimension exactly `2`. -/
theorem finrank_ker_evalMap_eq_two [AtLeastThree K] (P : Fin 8 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0)
    (h5 : ∀ ℓ : Fin 3 → K, ℓ ≠ 0 → ∀ s : Finset (Fin 8), (∀ i ∈ s, ℓ ⬝ᵥ P i = 0) →
      s.card ≤ 4)
    (hconic : ∀ q : Fin 6 → K, (∀ i, evalC q (P i) = 0) → q = 0) :
    Module.finrank K (LinearMap.ker (evalMap P)) = 2 := by
  have hle := finrank_cubicsThrough_le_two P hP h5 hconic
  have h1 := LinearMap.finrank_range_add_finrank_ker (evalMap P)
  have h2 : Module.finrank K (LinearMap.range (evalMap P)) ≤ 8 := by
    simpa using Submodule.finrank_le (LinearMap.range (evalMap P))
  simp only [Module.finrank_fin_fun] at h1
  rw [ker_evalMap_eq] at h1 ⊢
  omega

end PlaneCubic
