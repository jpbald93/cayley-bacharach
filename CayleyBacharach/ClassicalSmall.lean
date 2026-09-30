import CayleyBacharach.ClassicalFinite

/-!
# The classical form over finite fields with at least 8 elements

`ClassicalFinite.lean` proves the classical ("exactly nine common zeros") form of
Cayley–Bacharach for `|K| ≥ 11`, by crude counting. Here the counting is made exact:

* a line has exactly `|K| + 1` pairwise non-proportional points (`line_points`);
* a conic with two distinct zeros and no line component has at least `|K| + 1` pairwise
  non-proportional zeros (`conic_points`: projection from a zero `u`, one point for each of
  the `|K| + 1` lines through `u`, the tangent line giving `u` itself).

With `|K| ≥ 8` this gives at least `9` common zeros on a common line (resp. on the residual
conic of a common conic factor), so **all nine** points lie on it, and then every cubic
through eight of them contains the line (resp. the conic). This proves the classical form
for every finite field with `|K| ≥ 8` (`cayley_bacharach_classical_card8`). The bound is
sharp from above in the sense that the statement is false for `|K| = 4, 5, 7`
(counterexamples in `code/stage9/`); there is no field with `10` elements, so `8 ≤ |K|`
covers exactly `𝔽₈, 𝔽₉` and `|K| ≥ 11`.
-/

open Matrix

namespace PlaneCubic

variable {K : Type*} [Field K]

/-! ### Exact point counts -/

/-- A family indexed by `Option K`, pairwise non-proportional, consists of nonzero vectors. -/
theorem ne_zero_of_pairwise_option {g : Option K → Fin 3 → K}
    (hg : ∀ a b, a ≠ b → g a ⨯₃ g b ≠ 0) (a : Option K) : g a ≠ 0 := by
  intro h
  obtain ⟨b, hb⟩ : ∃ b : Option K, b ≠ a := by
    cases a with
    | none => exact ⟨some 0, by simp⟩
    | some t => exact ⟨none, by simp⟩
  exact hg b a hb (by rw [h]; simp)

/-- **The `|K| + 1` points of a line.** -/
theorem line_points (ℓ : Fin 3 → K) :
    ∃ g : Option K → Fin 3 → K, (∀ a, ℓ ⬝ᵥ g a = 0) ∧ ∀ a b, a ≠ b → g a ⨯₃ g b ≠ 0 := by
  obtain ⟨u, w, hu, hw, huw⟩ := exists_line_basis ℓ
  refine ⟨fun a => a.elim w (fun t => u + t • w), ?_, ?_⟩
  · rintro (_ | t)
    · exact hw
    · show ℓ ⬝ᵥ (u + t • w) = 0
      simp [dotProduct_add, dotProduct_smul, hu, hw]
  · rintro (_ | s) (_ | t) hab
    · exact absurd rfl hab
    · show w ⨯₃ (u + t • w) ≠ 0
      rw [cross_add_smul']; exact neg_ne_zero.mpr huw
    · show (u + s • w) ⨯₃ w ≠ 0
      rw [← cross_anticomm, cross_add_smul', neg_neg]; exact huw
    · show (u + s • w) ⨯₃ (u + t • w) ≠ 0
      have hst : s ≠ t := fun h => hab (by rw [h])
      rw [cross_add_smul]; exact smul_ne_zero (sub_ne_zero.mpr (Ne.symm hst)) huw

/-- **Counting.** `|K| + 1` pairwise non-proportional vectors, each proportional to some
`P i` with `i ∈ s`, force `|K| + 1 ≤ |s|`. -/
theorem card_add_one_le [Fintype K] {n : ℕ} {P : Fin n → Fin 3 → K} (hP0 : ∀ i, P i ≠ 0)
    (g : Option K → Fin 3 → K) (hg : ∀ a b, a ≠ b → g a ⨯₃ g b ≠ 0)
    (s : Finset (Fin n)) (hs : ∀ a, ∃ i ∈ s, g a ⨯₃ P i = 0) :
    Fintype.card K + 1 ≤ s.card := by
  choose f hfs hf using hs
  have hinj : Function.Injective (fun a => (⟨f a, hfs a⟩ : s)) := by
    intro a b hab
    by_contra hne
    have he : f a = f b := congrArg Subtype.val hab
    have h2 := hf b
    rw [← he] at h2
    exact hg a b hne (cross_eq_zero_of_cross_eq_zero (hP0 _) (hf a) h2)
  have := Fintype.card_le_of_injective _ hinj
  simpa [Fintype.card_option] using this

theorem eq_smul_of_cross_eq_zero {v w : Fin 3 → K} (hv : v ≠ 0) (h : v ⨯₃ w = 0) :
    ∃ c : K, w = c • v := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
  have hk' : v k ≠ 0 := hk
  have e := smul_eq_smul_of_cross_eq_zero h k
  refine ⟨w k / v k, ?_⟩
  calc w = (v k)⁻¹ • (v k • w) := by rw [smul_smul, inv_mul_cancel₀ hk', one_smul]
    _ = (v k)⁻¹ • (w k • v) := by rw [e]
    _ = (w k / v k) • v := by rw [smul_smul, div_eq_inv_mul]

theorem dot_eq_zero_of_prop {l v w : Fin 3 → K} (hv : v ≠ 0) (h : v ⨯₃ w = 0)
    (hl : l ⬝ᵥ v = 0) : l ⬝ᵥ w = 0 := by
  obtain ⟨c, rfl⟩ := eq_smul_of_cross_eq_zero hv h
  rw [dotProduct_smul, hl, smul_zero]

theorem evalC_eq_zero_of_prop {q : Fin 6 → K} {v w : Fin 3 → K} (hv : v ≠ 0)
    (h : v ⨯₃ w = 0) (hq : evalC q v = 0) : evalC q w = 0 := by
  obtain ⟨c, rfl⟩ := eq_smul_of_cross_eq_zero hv h
  rw [evalC_smul_vec, hq, mul_zero]

/-! ### Conics: at least `|K| + 1` zeros -/

theorem mulLin_linMul (m ℓ n : Fin 3 → K) : mulLin m (linMul ℓ n) = mulLin ℓ (linMul m n) := by
  ext i; fin_cases i <;> simp [mulLin, linMul] <;> ring

theorem mulLin_smul_left (c : K) (ℓ : Fin 3 → K) (q : Fin 6 → K) :
    mulLin (c • ℓ) q = mulLin ℓ (c • q) := by
  ext i; fin_cases i <;> simp [mulLin] <;> ring

/-- If `q` vanishes at `u, d` and `B(u, d) = 0`, the whole line `ud` lies on `q`. -/
theorem line_comp_of_polar {q : Fin 6 → K} {u d : Fin 3 → K} (hud : u ⨯₃ d ≠ 0)
    (hu : evalC q u = 0) (hd : evalC q d = 0) (hB : polarC q u d = 0) :
    ∃ m, q = linMul (u ⨯₃ d) m := by
  apply conic_line_lemma q _ hud
  intro x hx
  obtain ⟨s, t, rfl⟩ := on_line hud hud (cross_dot_left u d) (cross_dot_right u d) hx
  rw [evalC_smul_add_smul', hu, hd, hB]; ring

theorem smul_add_smul_ne_zero {u d : Fin 3 → K} (hud : u ⨯₃ d ≠ 0) {a b : K}
    (h : ¬ (a = 0 ∧ b = 0)) : a • u + b • d ≠ 0 := by
  intro h0
  apply h
  have i1 : (a • u + b • d) ⨯₃ d = a • (u ⨯₃ d) := by
    simp [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, cross_self]
  have i2 : u ⨯₃ (a • u + b • d) = b • (u ⨯₃ d) := by
    simp [map_add, map_smul, cross_self]
  rw [h0] at i1 i2
  simp only [map_zero, LinearMap.zero_apply] at i1 i2
  exact ⟨(smul_eq_zero.mp i1.symm).resolve_right hud, (smul_eq_zero.mp i2.symm).resolve_right hud⟩

/-- Two points `a u + b d`, `A u + B e` on distinct lines through `u` are non-proportional
unless both equal `u` (`b = B = 0`). -/
theorem proj_cross_ne {u d e : Fin 3 → K} (hT : d ⨯₃ e ⬝ᵥ u ≠ 0) {a b A B : K}
    (h1 : a • u + b • d ≠ 0) (h2 : A • u + B • e ≠ 0) (hbB : ¬ (b = 0 ∧ B = 0)) :
    (a • u + b • d) ⨯₃ (A • u + B • e) ≠ 0 := by
  intro h0
  have i1 : (a • u + b • d) ⨯₃ (A • u + B • e) ⬝ᵥ u = b * B * (d ⨯₃ e ⬝ᵥ u) := by
    simp [cross_apply, dotProduct, Fin.sum_univ_succ]; ring
  have i2 : (a • u + b • d) ⨯₃ (A • u + B • e) ⬝ᵥ d = -(a * B * (d ⨯₃ e ⬝ᵥ u)) := by
    simp [cross_apply, dotProduct, Fin.sum_univ_succ]; ring
  have i3 : (a • u + b • d) ⨯₃ (A • u + B • e) ⬝ᵥ e = -(b * A * (d ⨯₃ e ⬝ᵥ u)) := by
    simp [cross_apply, dotProduct, Fin.sum_univ_succ]; ring
  rw [h0, zero_dotProduct] at i1 i2 i3
  by_cases hb : b = 0
  · have hB : B ≠ 0 := fun hB => hbB ⟨hb, hB⟩
    have ha : a = 0 := by
      have : a * B * (d ⨯₃ e ⬝ᵥ u) = 0 := by linear_combination i2
      simpa [hB, hT] using this
    exact h1 (by rw [ha, hb]; simp)
  · have hB : B = 0 := by
      have : b * B * (d ⨯₃ e ⬝ᵥ u) = 0 := by linear_combination -i1
      simpa [hb, hT] using this
    have hA : A = 0 := by
      have : b * A * (d ⨯₃ e ⬝ᵥ u) = 0 := by linear_combination i3
      simpa [hb, hT] using this
    exact h2 (by rw [hA, hB]; simp)

/-- **The `|K| + 1` points of a conic.** A conic with two non-proportional zeros and no line
component has `|K| + 1` pairwise non-proportional zeros: projection from the zero `u`, one
zero on each of the `|K| + 1` lines through `u`. -/
theorem conic_points {q : Fin 6 → K} {u v : Fin 3 → K} (huv : u ⨯₃ v ≠ 0)
    (hu : evalC q u = 0) (hv : evalC q v = 0) (hno : ∀ ℓ m, ℓ ≠ 0 → q ≠ linMul ℓ m) :
    ∃ g : Option K → Fin 3 → K, (∀ a, evalC q (g a) = 0) ∧ ∀ a b, a ≠ b → g a ⨯₃ g b ≠ 0 := by
  obtain ⟨z, hz⟩ := exists_off_line huv
  obtain ⟨D, hDn, hDs⟩ : ∃ D : Option K → Fin 3 → K, D none = z ∧ ∀ t, D (some t) = v + t • z :=
    ⟨fun a => a.elim z (fun t => v + t • z), rfl, fun _ => rfl⟩
  have hlc : ∀ d, u ⨯₃ d ≠ 0 → evalC q d = 0 → polarC q u d = 0 → False := fun d hud hd hB => by
    obtain ⟨m, hm⟩ := line_comp_of_polar hud hu hd hB
    exact hno _ m hud hm
  have hD1 : ∀ a, u ⨯₃ D a ≠ 0 := by
    rintro (_ | t)
    · rw [hDn]
      intro h
      have i : u ⨯₃ z ⬝ᵥ v = -(u ⨯₃ v ⬝ᵥ z) := by
        simp [cross_apply, dotProduct, Fin.sum_univ_succ]; ring
      rw [h, zero_dotProduct] at i
      exact hz (by linear_combination i)
    · rw [hDs]
      intro h
      have i : u ⨯₃ (v + t • z) ⬝ᵥ z = u ⨯₃ v ⬝ᵥ z := by
        simp [cross_apply, dotProduct, Fin.sum_univ_succ]; ring
      rw [h, zero_dotProduct] at i
      exact hz i.symm
  have hD2 : ∀ a b, a ≠ b → D a ⨯₃ D b ⬝ᵥ u ≠ 0 := by
    rintro (_ | s) (_ | t) hab
    · exact absurd rfl hab
    · rw [hDn, hDs]
      have i : z ⨯₃ (v + t • z) ⬝ᵥ u = -(u ⨯₃ v ⬝ᵥ z) := by
        simp [cross_apply, dotProduct, Fin.sum_univ_succ]; ring
      rw [i]; exact neg_ne_zero.mpr hz
    · rw [hDn, hDs]
      have i : (v + s • z) ⨯₃ z ⬝ᵥ u = u ⨯₃ v ⬝ᵥ z := by
        simp [cross_apply, dotProduct, Fin.sum_univ_succ]; ring
      rw [i]; exact hz
    · rw [hDs, hDs]
      have hst : s ≠ t := fun h => hab (by rw [h])
      have i : (v + s • z) ⨯₃ (v + t • z) ⬝ᵥ u = (t - s) * (u ⨯₃ v ⬝ᵥ z) := by
        simp [cross_apply, dotProduct, Fin.sum_univ_succ]; ring
      rw [i]; exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm hst)) hz
  have hD3 : ∀ a b, a ≠ b → ¬ (polarC q u (D a) = 0 ∧ polarC q u (D b) = 0) := by
    rintro (_ | s) (_ | t) hab ⟨h1, h2⟩
    · exact hab rfl
    · rw [hDn] at h1
      rw [hDs, polarC_add_smul, h1, mul_zero, add_zero] at h2
      exact hlc v huv hv h2
    · rw [hDn] at h2
      rw [hDs, polarC_add_smul, h2, mul_zero, add_zero] at h1
      exact hlc v huv hv h1
    · rw [hDs, polarC_add_smul] at h1 h2
      have hst : s ≠ t := fun h => hab (by rw [h])
      have hz0 : polarC q u z = 0 := by
        have : (s - t) * polarC q u z = 0 := by linear_combination h1 - h2
        exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hst)
      rw [hz0, mul_zero, add_zero] at h1
      exact hlc v huv hv h1
  have hne : ∀ a, evalC q (D a) • u + (-polarC q u (D a)) • D a ≠ 0 := fun a =>
    smul_add_smul_ne_zero (hD1 a) (fun h => hlc _ (hD1 a) h.1 (neg_eq_zero.mp h.2))
  refine ⟨fun a => evalC q (D a) • u + (-polarC q u (D a)) • D a, fun a => ?_,
    fun a b hab => ?_⟩
  · show evalC q (_ • u + _ • _) = 0
    rw [evalC_smul_add_smul', hu]; ring
  · exact proj_cross_ne (hD2 a b hab) (hne a) (hne b)
      (fun h => hD3 a b hab ⟨neg_eq_zero.mp h.1, neg_eq_zero.mp h.2⟩)

/-! ### The classical form for `|K| ≥ 8` -/

/-- **Common line.** If every point of the line `ℓ = 0` is proportional to one of the nine
`P i` and `|K| ≥ 8`, then all nine points are on the line (`|K| + 1 ≥ 9`), and a cubic
through eight of them contains the line. -/
theorem classical_line_case [Fintype K] (hK : 8 ≤ Fintype.card K) (P : Fin 9 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0) {ℓ : Fin 3 → K} (hℓ : ℓ ≠ 0)
    (hZ : ∀ v, v ≠ 0 → ℓ ⬝ᵥ v = 0 → ∃ i, v ⨯₃ P i = 0)
    (H : PlaneCubic K) (hH : ∀ i : Fin 8, eval H (P (Fin.castSucc i)) = 0) :
    eval H (P 8) = 0 := by
  classical
  have : AtLeastThree K := AtLeastThree.of_card (by omega)
  have hP0 : ∀ i, P i ≠ 0 := ne_zero_of_pairwise (n := 7) hP
  obtain ⟨g, hgℓ, hg⟩ := line_points ℓ
  have hg0 := ne_zero_of_pairwise_option hg
  set s := Finset.univ.filter fun i => ℓ ⬝ᵥ P i = 0
  have hs : ∀ a, ∃ i ∈ s, g a ⨯₃ P i = 0 := fun a => by
    obtain ⟨i, hi⟩ := hZ (g a) (hg0 a) (hgℓ a)
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, dot_eq_zero_of_prop (hg0 a) hi (hgℓ a)⟩, hi⟩
  have hc := card_add_one_le hP0 g hg s hs
  have hsu : s = Finset.univ := Finset.eq_univ_of_card s (by
    have := Finset.card_le_univ s
    simp only [Fintype.card_fin] at this ⊢
    omega)
  have hall : ∀ i, ℓ ⬝ᵥ P i = 0 := fun i => by
    have : i ∈ s := by rw [hsu]; exact Finset.mem_univ i
    exact (Finset.mem_filter.mp this).2
  have hP' : ∀ i j : Fin 8, i ≠ j → P (Fin.castSucc i) ⨯₃ P (Fin.castSucc j) ≠ 0 :=
    fun i j hij => hP _ _ (fun h => hij (Fin.castSucc_injective _ h))
  obtain ⟨r, hr⟩ := divides_of_four (fun i : Fin 8 => P (Fin.castSucc i)) hP' hℓ Finset.univ
    (fun i _ => hall _) (by simp) H hH
  rw [hr]
  exact eval_mulLin_of_dot_eq_zero _ _ _ (hall 8)

/-- **Common irreducible conic.** If `q` has two non-proportional zeros, no line component,
and all its zeros are proportional to one of the nine `P i`, then for `|K| ≥ 8` all nine
points are on `q`; no three of them are collinear, so the cubics through eight of them are
exactly the multiples of `q`. -/
theorem classical_conic_case [Fintype K] (hK : 8 ≤ Fintype.card K) (P : Fin 9 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0) {q : Fin 6 → K}
    (hno : ∀ ℓ m, ℓ ≠ 0 → q ≠ linMul ℓ m) {u v : Fin 3 → K} (huv : u ⨯₃ v ≠ 0)
    (hu : evalC q u = 0) (hv : evalC q v = 0)
    (hZ : ∀ w, w ≠ 0 → evalC q w = 0 → ∃ i, w ⨯₃ P i = 0)
    (H : PlaneCubic K) (hH : ∀ i : Fin 8, eval H (P (Fin.castSucc i)) = 0) :
    eval H (P 8) = 0 := by
  classical
  have : AtLeastThree K := AtLeastThree.of_card (by omega)
  have hP0 : ∀ i, P i ≠ 0 := ne_zero_of_pairwise (n := 7) hP
  obtain ⟨g, hgq, hg⟩ := conic_points huv hu hv hno
  have hg0 := ne_zero_of_pairwise_option hg
  set s := Finset.univ.filter fun i => evalC q (P i) = 0
  have hs : ∀ a, ∃ i ∈ s, g a ⨯₃ P i = 0 := fun a => by
    obtain ⟨i, hi⟩ := hZ (g a) (hg0 a) (hgq a)
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, evalC_eq_zero_of_prop (hg0 a) hi (hgq a)⟩, hi⟩
  have hc := card_add_one_le hP0 g hg s hs
  have hsu : s = Finset.univ := Finset.eq_univ_of_card s (by
    have := Finset.card_le_univ s
    simp only [Fintype.card_fin] at this ⊢
    omega)
  have hall : ∀ i, evalC q (P i) = 0 := fun i => by
    have : i ∈ s := by rw [hsu]; exact Finset.mem_univ i
    exact (Finset.mem_filter.mp this).2
  set P' : Fin 8 → Fin 3 → K := fun i => P (Fin.castSucc i)
  have hP' : ∀ i j : Fin 8, i ≠ j → P' i ⨯₃ P' j ≠ 0 :=
    fun i j hij => hP _ _ (fun h => hij (Fin.castSucc_injective _ h))
  have hno3 : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → P' i ⨯₃ P' j ⬝ᵥ P' k ≠ 0 := by
    intro i j k hij hik hjk hc
    obtain ⟨m, hm⟩ := conic_three (hP' i j hij) (hP' i j hij) (hP' i k hik) (hP' j k hjk)
      (cross_dot_left _ _) (cross_dot_right _ _) hc (hall _) (hall _) (hall _)
    exact hno _ m (hP' i j hij) hm
  have hq0 : q ≠ 0 := by
    rintro rfl
    apply hno _ 0 huv
    ext i; fin_cases i <;> simp [linMul]
  have hdim := finrank_le_three_of_no3 P' hP' hno3
  have hle : LinearMap.range (mulConicLin q) ≤ cubicsThrough (Set.range P') := by
    rintro _ ⟨m, rfl⟩ _ ⟨i, rfl⟩
    simp only [mulConicLin, LinearMap.coe_mk, AddHom.coe_mk, eval_mulLin]
    rw [show conicEval q (P' i) = 0 from hall _, mul_zero]
  have h3 : Module.finrank K (LinearMap.range (mulConicLin q)) = 3 := by
    rw [LinearMap.finrank_range_of_inj (mulConicLin_injective hq0)]
    simp
  have heq := Submodule.eq_of_le_of_finrank_le hle (by rw [h3]; exact hdim)
  have hHm : H ∈ LinearMap.range (mulConicLin q) := by
    rw [heq]; rintro _ ⟨i, rfl⟩; exact hH i
  obtain ⟨r, hr⟩ := hHm
  rw [← hr]
  simp only [mulConicLin, LinearMap.coe_mk, AddHom.coe_mk, eval_mulLin]
  rw [show conicEval q (P 8) = 0 from hall 8, mul_zero]

/-- **Cayley–Bacharach, classical form, over any finite field with at least 8 elements.**
Two linearly independent cubics whose common zeros are exactly nine pairwise
non-proportional points: every cubic through eight of them passes through the ninth.
(There is no field with 10 elements, so this covers `𝔽₈`, `𝔽₉` and all `|K| ≥ 11`; the
statement is false over `𝔽₄, 𝔽₅, 𝔽₇`.) -/
theorem cayley_bacharach_classical_card8 [Fintype K] (hK : 8 ≤ Fintype.card K)
    (P : Fin 9 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0)
    (F G : PlaneCubic K) (hFG : LinearIndependent K ![F, G])
    (hex : ExactlyMeetIn F G P)
    (H : PlaneCubic K) (hH : ∀ i : Fin 8, eval H (P (Fin.castSucc i)) = 0) :
    eval H (P 8) = 0 := by
  have : AtLeastThree K := AtLeastThree.of_card (by omega)
  obtain ⟨hPZ, hZ⟩ := hex
  have hF : ∀ i, eval F (P i) = 0 := fun i => (hPZ i).2.1
  have hG : ∀ i, eval G (P i) = 0 := fun i => (hPZ i).2.2
  have hex' : ∀ v, v ≠ 0 → eval F v = 0 → eval G v = 0 → ∃ i, v ⨯₃ P i = 0 :=
    fun v hv h1 h2 => hZ v ⟨hv, h1, h2⟩
  by_cases hlin : ∃ ℓ q q', ℓ ≠ 0 ∧ F = mulLin ℓ q ∧ G = mulLin ℓ q'
  · obtain ⟨ℓ, q, q', hℓ, hFe, hGe⟩ := hlin
    refine classical_line_case hK P hP hℓ (fun v hv hl => hex' v hv ?_ ?_) H hH
    · rw [hFe]; exact eval_mulLin_of_dot_eq_zero _ _ _ hl
    · rw [hGe]; exact eval_mulLin_of_dot_eq_zero _ _ _ hl
  by_cases hcon : ∃ q m m', q ≠ 0 ∧ F = mulLin m q ∧ G = mulLin m' q
  swap
  · exact cayley_bacharach_of_no_common_factor P hP F G hFG hF hG hlin hcon H hH
  obtain ⟨q, m, m', -, hFe, hGe⟩ := hcon
  by_cases hql : ∃ ℓ n, ℓ ≠ 0 ∧ q = linMul ℓ n
  · obtain ⟨ℓ, n, hℓ, hqe⟩ := hql
    exact absurd ⟨ℓ, linMul m n, linMul m' n, hℓ, by rw [hFe, hqe, mulLin_linMul],
      by rw [hGe, hqe, mulLin_linMul]⟩ hlin
  have hno : ∀ ℓ n, ℓ ≠ 0 → q ≠ linMul ℓ n := fun ℓ n hℓ h => hql ⟨ℓ, n, hℓ, h⟩
  have hZq : ∀ w, w ≠ 0 → evalC q w = 0 → ∃ i, w ⨯₃ P i = 0 := fun w hw h =>
    hex' w hw (by rw [hFe, eval_mulLin, show conicEval q w = 0 from h, mul_zero])
      (by rw [hGe, eval_mulLin, show conicEval q w = 0 from h, mul_zero])
  have hmm : ∀ i, evalC q (P i) ≠ 0 → m ⬝ᵥ P i = 0 ∧ m' ⬝ᵥ P i = 0 := fun i hi => by
    have h1 := hF i
    have h2 := hG i
    rw [hFe, eval_mulLin] at h1
    rw [hGe, eval_mulLin] at h2
    exact ⟨(mul_eq_zero.mp h1).resolve_right hi, (mul_eq_zero.mp h2).resolve_right hi⟩
  have key : ∀ a b, a ≠ b → evalC q (P a) ≠ 0 → evalC q (P b) ≠ 0 → False := by
    intro a b hab ha hb
    obtain ⟨c, hc⟩ := lin_two (hP a b hab) (hmm a ha).1 (hmm b hb).1
    obtain ⟨c', hc'⟩ := lin_two (hP a b hab) (hmm a ha).2 (hmm b hb).2
    exact hlin ⟨P a ⨯₃ P b, c • q, c' • q, hP a b hab, by rw [hFe, hc, mulLin_smul_left],
      by rw [hGe, hc', mulLin_smul_left]⟩
  have pair : ∀ a b, a ≠ b → evalC q (P a) = 0 → evalC q (P b) = 0 → eval H (P 8) = 0 :=
    fun a b hab ha hb => classical_conic_case hK P hP hno (hP a b hab) ha hb hZq H hH
  by_cases h0 : evalC q (P 0) = 0
  · by_cases h1 : evalC q (P 1) = 0
    · exact pair 0 1 (by decide) h0 h1
    · by_cases h2 : evalC q (P 2) = 0
      · exact pair 0 2 (by decide) h0 h2
      · exact (key 1 2 (by decide) h1 h2).elim
  · by_cases h1 : evalC q (P 1) = 0
    · by_cases h2 : evalC q (P 2) = 0
      · exact pair 1 2 (by decide) h1 h2
      · exact (key 0 2 (by decide) h0 h2).elim
    · exact (key 0 1 (by decide) h0 h1).elim

end PlaneCubic
