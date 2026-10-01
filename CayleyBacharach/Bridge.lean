import CayleyBacharach.ClassicalF3

/-!
# Bridge lemmas: the local definitions are the standard notions

Nothing in this file is used elsewhere and no new results are proved; these lemmas only
document that the coefficient-vector encodings used in the development mean what they
should:

* `eval_smul_smul`, `evalC_smul_smul`, `vanishesAt_smul_smul_iff`: evaluation is linear in
  the form and homogeneous (degree 3, resp. 2) in the point, so vanishing is well defined on
  projective points and on forms up to a nonzero scalar.
* `mem_onLine_iff_mem_ker`: `onLine` is membership in the kernel of the linear form `ℓ`.
* `col4_iff_exists_mulVec`, `col4_iff_rank_le_two`, `col4_iff_minors`: four points are
  collinear iff the `4 × 3` matrix of their coordinates has a nonzero kernel vector, iff it
  has rank `≤ 2`, iff all four of its `3 × 3` minors vanish.
* `polarC_eq`, `polarC_self`, `polarC_comm`, `polarC_eq_bilin`: `polarC` is the polar
  bilinear form `q(x+y) - q(x) - q(y)`, given by the symmetric matrix with diagonal `2qᵢᵢ`
  (no division; valid in every characteristic).
* `vanishesAt_iff`, `commonZero_iff`, `cross_eq_zero_iff_eq_smul`, `exactlyMeetIn_iff`:
  readings of `VanishesAt`, `CommonZero` and `ExactlyMeetIn` via `eval`, with
  "up to scaling" made explicit.
-/

open Matrix

namespace PlaneCubic

section CommRing

variable {R : Type*} [CommRing R]

/-- Evaluation is linear in the form and cubic in the point. -/
theorem eval_smul_smul (a c : R) (F : PlaneCubic R) (v : Fin 3 → R) :
    eval (a • F) (c • v) = a * c ^ 3 * eval F v := by
  rw [eval_smul, eval_smul_vec, mul_assoc]

/-- Conic evaluation is linear in the form and quadratic in the point. -/
theorem evalC_smul_smul (a c : R) (q : Fin 6 → R) (v : Fin 3 → R) :
    evalC (a • q) (c • v) = a * c ^ 2 * evalC q v := by
  rw [evalC_smul, evalC_smul_vec, mul_assoc]

/-- `VanishesAt` is the vanishing of `eval`. -/
theorem vanishesAt_iff (F : PlaneCubic R) (v : Fin 3 → R) : VanishesAt F v ↔ eval F v = 0 :=
  Iff.rfl

/-- Vanishing is well defined on forms and points up to nonzero scalars. -/
theorem vanishesAt_smul_smul_iff [IsDomain R] {a c : R} (ha : a ≠ 0) (hc : c ≠ 0)
    (F : PlaneCubic R) (v : Fin 3 → R) : VanishesAt (a • F) (c • v) ↔ VanishesAt F v := by
  simp [VanishesAt, eval_smul_smul, ha, hc]

/-- `polarC` is `q(x+y) - q(x) - q(y)` (its definition). -/
theorem polarC_eq {K : Type*} [Field K] (q : Fin 6 → K) (x y : Fin 3 → K) :
    polarC q x y = evalC q (x + y) - evalC q x - evalC q y := rfl

end CommRing

variable {K : Type*} [Field K]

theorem polarC_self (q : Fin 6 → K) (x : Fin 3 → K) : polarC q x x = 2 * evalC q x := by
  simp only [polarC, evalC_expand, Pi.add_apply]; ring

theorem polarC_comm (q : Fin 6 → K) (x y : Fin 3 → K) : polarC q x y = polarC q y x := by
  simp only [polarC, evalC_expand, Pi.add_apply]; ring

/-- `polarC q` is the symmetric bilinear form with matrix having diagonal `2qᵢᵢ` and
off-diagonal entries the mixed coefficients (no division; every characteristic). -/
theorem polarC_eq_bilin (q : Fin 6 → K) (x y : Fin 3 → K) :
    polarC q x y = x ⬝ᵥ (!![2 * q 0, q 1, q 2; q 1, 2 * q 3, q 4; q 2, q 4, 2 * q 5] *ᵥ y) := by
  simp only [polarC, evalC_expand, Pi.add_apply]
  simp [dotProduct, mulVec, Fin.sum_univ_succ]; ring

/-- `onLine P ℓ` is the set of indices of points in the kernel of the linear form `ℓ`. -/
theorem mem_onLine_iff_mem_ker [DecidableEq K] {n : ℕ} (P : Fin n → Fin 3 → K)
    (ℓ : Fin 3 → K) (i : Fin n) :
    i ∈ onLine P ℓ ↔ P i ∈ LinearMap.ker (dotProductBilin K K ℓ) := by
  simp [mem_onLine]

/-- `Col4`: the `4 × 3` coordinate matrix has a nonzero kernel vector. -/
theorem col4_iff_exists_mulVec (x y z w : Fin 3 → K) :
    Col4 x y z w ↔ ∃ ℓ : Fin 3 → K, ℓ ≠ 0 ∧ Matrix.of ![x, y, z, w] *ᵥ ℓ = 0 := by
  unfold Col4
  refine exists_congr fun ℓ => and_congr Iff.rfl ?_
  simp only [funext_iff, Fin.forall_fin_succ, Pi.zero_apply, mulVec, of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_succ, IsEmpty.forall_iff]
  simp [dotProduct_comm ℓ]

/-- `Col4`: the `4 × 3` coordinate matrix has rank at most 2. -/
theorem col4_iff_rank_le_two (x y z w : Fin 3 → K) :
    Col4 x y z w ↔ (Matrix.of ![x, y, z, w]).rank ≤ 2 := by
  rw [col4_iff_exists_mulVec]
  set M := Matrix.of ![x, y, z, w]
  have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fin_fun] at h
  rw [Matrix.rank]
  have e : (∃ ℓ : Fin 3 → K, ℓ ≠ 0 ∧ M *ᵥ ℓ = 0) ↔ LinearMap.ker M.mulVecLin ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]; simp [and_comm]
  rw [e, Ne, ← Submodule.finrank_eq_zero]
  omega

private theorem det_of_cross {a b c : Fin 3 → K} : a ⨯₃ b ⬝ᵥ c = det ![a, b, c] := by
  rw [dotProduct_comm, triple_product_permutation c a b, triple_product_eq_det]

private theorem col_of_cross {a b c d : Fin 3 → K} (hab : a ⨯₃ b ≠ 0)
    (hc : det ![a, b, c] = 0) (hd : det ![a, b, d] = 0) :
    ∃ ℓ : Fin 3 → K, ℓ ≠ 0 ∧ ℓ ⬝ᵥ a = 0 ∧ ℓ ⬝ᵥ b = 0 ∧ ℓ ⬝ᵥ c = 0 ∧ ℓ ⬝ᵥ d = 0 :=
  ⟨_, hab, cross_dot_left a b, cross_dot_right a b, det_of_cross.trans hc,
    det_of_cross.trans hd⟩

private theorem exists_cross_single_ne {p : Fin 3 → K} (hp : p ≠ 0) :
    ∃ k : Fin 3, p ⨯₃ Pi.single k 1 ≠ 0 := by
  by_contra h
  push Not at h
  apply hp
  have h0 := congrFun (h 0) 1; have h1 := congrFun (h 0) 2; have h2 := congrFun (h 1) 2
  simp [cross_apply] at h0 h1 h2
  funext i; fin_cases i <;> simp [*]

private theorem col_of_prop {p x y z w : Fin 3 → K} (hp : p ≠ 0) (hx : p ⨯₃ x = 0)
    (hy : p ⨯₃ y = 0) (hz : p ⨯₃ z = 0) (hw : p ⨯₃ w = 0) : Col4 x y z w := by
  obtain ⟨k, hk⟩ := exists_cross_single_ne hp
  have hl : p ⨯₃ Pi.single k 1 ⬝ᵥ p = 0 := cross_dot_left _ _
  exact ⟨_, hk, dot_eq_zero_of_prop hp hx hl, dot_eq_zero_of_prop hp hy hl,
    dot_eq_zero_of_prop hp hz hl, dot_eq_zero_of_prop hp hw hl⟩

private theorem det_sw (a b c : Fin 3 → K) : det ![a, b, c] = -det ![a, c, b] := by
  rw [← triple_product_eq_det, ← triple_product_eq_det, ← cross_anticomm, dotProduct_neg]

private theorem sw0 {a b c : Fin 3 → K} (h : det ![a, c, b] = 0) : det ![a, b, c] = 0 := by
  rw [det_sw, h, neg_zero]

private theorem det_rep1 (a b : Fin 3 → K) : det ![a, b, a] = 0 := by
  rw [← triple_product_eq_det, dot_cross_self]

private theorem det_rep2 (a b : Fin 3 → K) : det ![a, b, b] = 0 := by
  rw [← triple_product_eq_det, cross_self, dotProduct_zero]

/-- `Col4`: all four `3 × 3` minors of the coordinate matrix vanish. -/
theorem col4_iff_minors (x y z w : Fin 3 → K) :
    Col4 x y z w ↔ det ![x, y, z] = 0 ∧ det ![x, y, w] = 0 ∧ det ![x, z, w] = 0 ∧
      det ![y, z, w] = 0 := by
  unfold Col4
  constructor
  · rintro ⟨ℓ, hℓ, hx, hy, hz, hw⟩
    have key : ∀ a b c : Fin 3 → K, ℓ ⬝ᵥ a = 0 → ℓ ⬝ᵥ b = 0 → ℓ ⬝ᵥ c = 0 →
        det ![a, b, c] = 0 := by
      intro a b c ha hb hc
      refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨ℓ, hℓ, ?_⟩
      funext i; fin_cases i <;> simp [mulVec, dotProduct_comm _ ℓ, *]
    exact ⟨key _ _ _ hx hy hz, key _ _ _ hx hy hw, key _ _ _ hx hz hw, key _ _ _ hy hz hw⟩
  · rintro ⟨h1, h2, h3, h4⟩
    by_cases hxy : x ⨯₃ y = 0
    swap; · exact col_of_cross hxy h1 h2
    by_cases hxz : x ⨯₃ z = 0
    swap
    · obtain ⟨ℓ, a, b, c, d, e⟩ := col_of_cross hxz (sw0 h1) h3
      exact ⟨ℓ, a, b, d, c, e⟩
    by_cases hxw : x ⨯₃ w = 0
    swap
    · obtain ⟨ℓ, a, b, c, d, e⟩ := col_of_cross hxw (sw0 h2) (sw0 h3)
      exact ⟨ℓ, a, b, d, e, c⟩
    by_cases hx : x ≠ 0
    · exact col_of_prop hx (cross_self x) hxy hxz hxw
    push Not at hx; subst hx
    by_cases hyz : y ⨯₃ z = 0
    swap
    · obtain ⟨ℓ, a, b, c, -, e⟩ := col_of_cross hyz (det_rep1 y z) h4
      exact ⟨ℓ, a, by simp, b, c, e⟩
    by_cases hyw : y ⨯₃ w = 0
    swap
    · obtain ⟨ℓ, a, b, c, d, -⟩ := col_of_cross hyw (sw0 h4) (det_rep1 y w)
      exact ⟨ℓ, a, by simp, b, d, c⟩
    by_cases hy : y ≠ 0
    · exact col_of_prop hy (by simp) (cross_self y) hyz hyw
    push Not at hy; subst hy
    by_cases hzw : z ⨯₃ w = 0
    swap
    · obtain ⟨ℓ, a, b, c, -, -⟩ := col_of_cross hzw (det_rep1 z w) (det_rep2 z w)
      exact ⟨ℓ, a, by simp, by simp, b, c⟩
    by_cases hz : z ≠ 0
    · exact col_of_prop hz (by simp) (by simp) (cross_self z) hzw
    push Not at hz; subst hz
    by_cases hw : w ≠ 0
    · exact col_of_prop hw (by simp) (by simp) (by simp) (cross_self w)
    push Not at hw; subst hw
    exact ⟨Pi.single 0 1, by simp, by simp, by simp, by simp, by simp⟩

/-- `VanishesAt`-reading of `CommonZero`. -/
theorem commonZero_iff (F G : PlaneCubic K) (v : Fin 3 → K) :
    CommonZero F G v ↔ v ≠ 0 ∧ VanishesAt F v ∧ VanishesAt G v := Iff.rfl

/-- For a nonzero `p`, `v ⨯₃ p = 0` says `v` is a scalar multiple of `p`. -/
theorem cross_eq_zero_iff_eq_smul {v p : Fin 3 → K} (hp : p ≠ 0) :
    v ⨯₃ p = 0 ↔ ∃ c : K, v = c • p := by
  constructor
  · intro h
    exact eq_smul_of_cross_eq_zero hp (by rw [← cross_anticomm, h, neg_zero])
  · rintro ⟨c, rfl⟩
    simp [cross_self]

/-- `ExactlyMeetIn F G P`: every `P i` is a nonzero common zero of `F` and `G`, and every
nonzero common zero is a scalar multiple of some `P i`. -/
theorem exactlyMeetIn_iff {ι : Type*} (F G : PlaneCubic K) (P : ι → Fin 3 → K) :
    ExactlyMeetIn F G P ↔ (∀ i, P i ≠ 0 ∧ eval F (P i) = 0 ∧ eval G (P i) = 0) ∧
      ∀ v, v ≠ 0 → eval F v = 0 → eval G v = 0 → ∃ i, ∃ c : K, v = c • P i := by
  unfold ExactlyMeetIn CommonZero
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun v hv hF hG => ?_⟩
    obtain ⟨i, hi⟩ := h2 v ⟨hv, hF, hG⟩
    exact ⟨i, (cross_eq_zero_iff_eq_smul (h1 i).1).1 hi⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun v ⟨hv, hF, hG⟩ => ?_⟩
    obtain ⟨i, hi⟩ := h2 v hv hF hG
    exact ⟨i, (cross_eq_zero_iff_eq_smul (h1 i).1).2 hi⟩

end PlaneCubic
