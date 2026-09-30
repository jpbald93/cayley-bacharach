import CayleyBacharach.Line

/-!
# Conics: products of linear forms and the conic line lemma

Conics are coefficient vectors `Fin 6 → R` in the order `x², xy, xz, y², yz, z²`
(the order of `PlaneCubic.conicMono`).

* `PlaneCubic.evalC`: conic evaluation (= `conicEval`).
* `PlaneCubic.linMul ℓ m`: the conic `ℓ · m` for two linear forms, with `evalC_linMul`.
* `PlaneCubic.conic_line_lemma`: over an infinite field, a conic vanishing on the whole
  line `ℓ = 0` (`ℓ ≠ 0`) is `ℓ · m` for a linear form `m`.
* `PlaneCubic.conic_line_not_square`: the stronger claim "`q = c • ℓ²`" is false
  (`xy` vanishes on `x = 0`).
-/

namespace PlaneCubic

section CommRing

variable {R : Type*} [CommRing R]

/-- Conic evaluation at `v`, in the monomial order `x², xy, xz, y², yz, z²`. -/
abbrev evalC (q : Fin 6 → R) (v : Fin 3 → R) : R := conicEval q v

theorem evalC_expand (q : Fin 6 → R) (v : Fin 3 → R) :
    evalC q v = q 0 * v 0 ^ 2 + q 1 * (v 0 * v 1) + q 2 * (v 0 * v 2) + q 3 * v 1 ^ 2
      + q 4 * (v 1 * v 2) + q 5 * v 2 ^ 2 := by
  simp [evalC, conicEval, conicMono, Fin.sum_univ_succ]
  ring

/-- The conic `ℓ · m`, product of two linear forms. -/
def linMul (ℓ m : Fin 3 → R) : Fin 6 → R :=
  ![(ℓ 0)*(m 0), (ℓ 0)*(m 1) + (ℓ 1)*(m 0), (ℓ 0)*(m 2) + (ℓ 2)*(m 0), (ℓ 1)*(m 1),
    (ℓ 1)*(m 2) + (ℓ 2)*(m 1), (ℓ 2)*(m 2)]

/-- The square `ℓ ⊗ ℓ` of a linear form, as a conic. -/
def linearFormSquare (ℓ : Fin 3 → R) : Fin 6 → R := linMul ℓ ℓ

theorem evalC_linMul (ℓ m : Fin 3 → R) (v : Fin 3 → R) :
    evalC (linMul ℓ m) v = (ℓ ⬝ᵥ v) * (m ⬝ᵥ v) := by
  simp [evalC_expand, linMul, dotProduct, Fin.sum_univ_succ]
  ring

theorem linMul_smul (ℓ : Fin 3 → R) (c : R) (m : Fin 3 → R) :
    linMul ℓ (c • m) = c • linMul ℓ m := by
  ext i
  fin_cases i <;> simp [linMul] <;> ring

theorem evalC_add (q r : Fin 6 → R) (v : Fin 3 → R) : evalC (q + r) v = evalC q v + evalC r v := by
  simp [evalC, conicEval, add_mul, Finset.sum_add_distrib]

theorem evalC_smul (c : R) (q : Fin 6 → R) (v : Fin 3 → R) : evalC (c • q) v = c * evalC q v := by
  simp [evalC, conicEval, Finset.mul_sum, mul_assoc]

theorem evalC_smul_vec (q : Fin 6 → R) (c : R) (v : Fin 3 → R) :
    evalC q (c • v) = c ^ 2 * evalC q v := by
  simp only [evalC_expand, Pi.smul_apply, smul_eq_mul]
  ring

end CommRing

section Field

variable {K : Type*} [Field K]

/-- A quadratic `b t² + c t + d` with `b = 0` vanishing at `t = 0, 1` is zero (any field). -/
theorem quad_coeffs_eq_zero_of_forall' {b c d : K} (hb : b = 0)
    (h : ∀ t : K, b * t ^ 2 + c * t + d = 0) : b = 0 ∧ c = 0 ∧ d = 0 := by
  have e0 := h 0
  have e1 := h 1
  subst hb
  have hd : d = 0 := by simpa using e0
  subst hd
  exact ⟨rfl, by simpa using e1, rfl⟩

theorem quad_coeffs_eq_zero_of_forall [Infinite K] {b c d : K}
    (h : ∀ t : K, b * t ^ 2 + c * t + d = 0) : b = 0 ∧ c = 0 ∧ d = 0 := by
  obtain ⟨-, h2, h1, h0⟩ := coeffs_eq_zero_of_forall (a := 0) (b := b) (c := c) (d := d)
    (fun t => by simpa using h t)
  exact ⟨h2, h1, h0⟩

theorem conic_line_lemma_aux0 (q : Fin 6 → K) (ℓ : Fin 3 → K) (hk : ℓ 0 ≠ 0)
    (hq : ∀ v : Fin 3 → K, ℓ ⬝ᵥ v = 0 → evalC q v = 0) :
    ∃ m : Fin 3 → K, q = linMul ℓ m := by
  have key : ∀ t : K, ((ℓ 0)^2*(q 3) - (ℓ 0)*(ℓ 1)*(q 1) + (ℓ 1)^2*(q 0)) * t ^ 2
      + ((ℓ 0)^2*(q 4) - (ℓ 0)*(ℓ 1)*(q 2) - (ℓ 0)*(ℓ 2)*(q 1) + 2*(ℓ 1)*(ℓ 2)*(q 0)) * t
      + ((ℓ 0)^2*(q 5) - (ℓ 0)*(ℓ 2)*(q 2) + (ℓ 2)^2*(q 0)) = 0 := by
    intro t
    have hv := hq ![-(ℓ 1)*t - (ℓ 2), (ℓ 0)*t, (ℓ 0)]
      (by simp [dotProduct, Fin.sum_univ_succ]; ring)
    rw [evalC_expand] at hv
    simp at hv
    linear_combination hv
  have hinf := hq ![-(ℓ 1), (ℓ 0), 0] (by simp [dotProduct, Fin.sum_univ_succ]; ring)
  rw [evalC_expand] at hinf
  simp at hinf
  obtain ⟨h2, h1, h0⟩ := quad_coeffs_eq_zero_of_forall' (by linear_combination hinf) key
  refine ⟨(ℓ 0 ^ 2)⁻¹ • ![(ℓ 0)*(q 0), (ℓ 0)*(q 1) - (ℓ 1)*(q 0), (ℓ 0)*(q 2) - (ℓ 2)*(q 0)], ?_⟩
  rw [linMul_smul, eq_inv_smul_iff₀ (pow_ne_zero 2 hk)]
  funext i
  fin_cases i <;> simp [linMul]
  · linear_combination
  · linear_combination
  · linear_combination
  · linear_combination h2
  · linear_combination h1
  · linear_combination h0

theorem conic_line_lemma_aux1 (q : Fin 6 → K) (ℓ : Fin 3 → K) (hk : ℓ 1 ≠ 0)
    (hq : ∀ v : Fin 3 → K, ℓ ⬝ᵥ v = 0 → evalC q v = 0) :
    ∃ m : Fin 3 → K, q = linMul ℓ m := by
  have key : ∀ t : K, ((ℓ 0)^2*(q 3) - (ℓ 0)*(ℓ 1)*(q 1) + (ℓ 1)^2*(q 0)) * t ^ 2
      + (-(ℓ 0)*(ℓ 1)*(q 4) + 2*(ℓ 0)*(ℓ 2)*(q 3) + (ℓ 1)^2*(q 2) - (ℓ 1)*(ℓ 2)*(q 1)) * t
      + ((ℓ 1)^2*(q 5) - (ℓ 1)*(ℓ 2)*(q 4) + (ℓ 2)^2*(q 3)) = 0 := by
    intro t
    have hv := hq ![(ℓ 1)*t, -(ℓ 0)*t - (ℓ 2), (ℓ 1)]
      (by simp [dotProduct, Fin.sum_univ_succ]; ring)
    rw [evalC_expand] at hv
    simp at hv
    linear_combination hv
  have hinf := hq ![(ℓ 1), -(ℓ 0), 0] (by simp [dotProduct, Fin.sum_univ_succ]; ring)
  rw [evalC_expand] at hinf
  simp at hinf
  obtain ⟨h2, h1, h0⟩ := quad_coeffs_eq_zero_of_forall' (by linear_combination hinf) key
  refine ⟨(ℓ 1 ^ 2)⁻¹ • ![-(ℓ 0)*(q 3) + (ℓ 1)*(q 1), (ℓ 1)*(q 3), (ℓ 1)*(q 4) - (ℓ 2)*(q 3)], ?_⟩
  rw [linMul_smul, eq_inv_smul_iff₀ (pow_ne_zero 2 hk)]
  funext i
  fin_cases i <;> simp [linMul]
  · linear_combination h2
  · linear_combination
  · linear_combination h1
  · linear_combination
  · linear_combination
  · linear_combination h0

theorem conic_line_lemma_aux2 (q : Fin 6 → K) (ℓ : Fin 3 → K) (hk : ℓ 2 ≠ 0)
    (hq : ∀ v : Fin 3 → K, ℓ ⬝ᵥ v = 0 → evalC q v = 0) :
    ∃ m : Fin 3 → K, q = linMul ℓ m := by
  have key : ∀ t : K, ((ℓ 0)^2*(q 5) - (ℓ 0)*(ℓ 2)*(q 2) + (ℓ 2)^2*(q 0)) * t ^ 2
      + (2*(ℓ 0)*(ℓ 1)*(q 5) - (ℓ 0)*(ℓ 2)*(q 4) - (ℓ 1)*(ℓ 2)*(q 2) + (ℓ 2)^2*(q 1)) * t
      + ((ℓ 1)^2*(q 5) - (ℓ 1)*(ℓ 2)*(q 4) + (ℓ 2)^2*(q 3)) = 0 := by
    intro t
    have hv := hq ![(ℓ 2)*t, (ℓ 2), -(ℓ 0)*t - (ℓ 1)]
      (by simp [dotProduct, Fin.sum_univ_succ]; ring)
    rw [evalC_expand] at hv
    simp at hv
    linear_combination hv
  have hinf := hq ![(ℓ 2), 0, -(ℓ 0)] (by simp [dotProduct, Fin.sum_univ_succ]; ring)
  rw [evalC_expand] at hinf
  simp at hinf
  obtain ⟨h2, h1, h0⟩ := quad_coeffs_eq_zero_of_forall' (by linear_combination hinf) key
  refine ⟨(ℓ 2 ^ 2)⁻¹ • ![-(ℓ 0)*(q 5) + (ℓ 2)*(q 2), -(ℓ 1)*(q 5) + (ℓ 2)*(q 4), (ℓ 2)*(q 5)], ?_⟩
  rw [linMul_smul, eq_inv_smul_iff₀ (pow_ne_zero 2 hk)]
  funext i
  fin_cases i <;> simp [linMul]
  · linear_combination h2
  · linear_combination h1
  · linear_combination
  · linear_combination h0
  · linear_combination
  · linear_combination

/-- **Conic line lemma.** Over any field (no size hypothesis: the line has `≥ 3` points
`0, ∞, 1`, which is exactly enough for a binary quadratic), a conic vanishing at every point
of the line `ℓ = 0` (`ℓ ≠ 0`) is `ℓ · m` for a linear form `m`. -/
theorem conic_line_lemma (q : Fin 6 → K) (ℓ : Fin 3 → K) (hℓ : ℓ ≠ 0)
    (hq : ∀ v : Fin 3 → K, ℓ ⬝ᵥ v = 0 → evalC q v = 0) :
    ∃ m : Fin 3 → K, q = linMul ℓ m := by
  by_cases h0 : ℓ 0 = 0
  · by_cases h1 : ℓ 1 = 0
    · have h2 : ℓ 2 ≠ 0 := by
        intro h2
        apply hℓ
        funext i
        fin_cases i <;> simp [h0, h1, h2]
      exact conic_line_lemma_aux2 q ℓ h2 hq
    · exact conic_line_lemma_aux1 q ℓ h1 hq
  · exact conic_line_lemma_aux0 q ℓ h0 hq

/-- The requested strengthening "`q = c • ℓ²`" is false: the conic `xy` vanishes on the
line `x = 0` but is not a multiple of `x²`. -/
theorem conic_line_not_square :
    (∀ v : Fin 3 → K, (![1, 0, 0] : Fin 3 → K) ⬝ᵥ v = 0 →
        evalC (![0, 1, 0, 0, 0, 0] : Fin 6 → K) v = 0) ∧
      ¬ ∃ c : K, (![0, 1, 0, 0, 0, 0] : Fin 6 → K) = c • linearFormSquare ![1, 0, 0] := by
  refine ⟨fun v hv => ?_, fun ⟨c, hc⟩ => ?_⟩
  · simp [dotProduct, Fin.sum_univ_succ] at hv
    simp [evalC_expand, hv]
  · have := congrFun hc 1
    simp [linearFormSquare, linMul] at this

end Field

end PlaneCubic
