import CayleyBacharach.Defs

/-!
# Restriction of a cubic to a line, and the line lemma

* `PlaneCubic.eval_add_smul`: `F(P + t•Q) = c₃ t³ + c₂ t² + c₁ t + c₀` with
  `c₀ = F(P)`, `c₃ = F(Q)` and `c₁, c₂` the mixed (polarisation) pieces.
* `PlaneCubic.line_lemma`: over an infinite field, a cubic vanishing on the whole line
  `{v | ℓ ⬝ᵥ v = 0}` (with `ℓ ≠ 0`) is `ℓ · q` for a conic `q`.

Conics (homogeneous quadratic forms) are coefficient vectors `Fin 6 → R` in the order
`x², xy, xz, y², yz, z²`.
-/

namespace PlaneCubic

section CommRing

variable {R : Type*} [CommRing R]

/-- Values of the monomials `x², xy, xz, y², yz, z²` at `v`. -/
def conicMono (v : Fin 3 → R) : Fin 6 → R :=
  ![v 0 ^ 2, v 0 * v 1, v 0 * v 2, v 1 ^ 2, v 1 * v 2, v 2 ^ 2]

/-- Evaluation of a conic (coefficient vector `Fin 6 → R`) at `v`. -/
def conicEval (q : Fin 6 → R) (v : Fin 3 → R) : R := ∑ j, q j * conicMono v j

/-- The cubic `ℓ · q`, for a linear form `ℓ` and a conic `q`. -/
def mulLin (ℓ : Fin 3 → R) (q : Fin 6 → R) : PlaneCubic R :=
  ![(ℓ 0)*(q 0), (ℓ 0)*(q 1) + (ℓ 1)*(q 0), (ℓ 0)*(q 2) + (ℓ 2)*(q 0), (ℓ 0)*(q 3) + (ℓ 1)*(q 1), (ℓ 0)*(q 4) + (ℓ 1)*(q 2) + (ℓ 2)*(q 1), (ℓ 0)*(q 5) + (ℓ 2)*(q 2), (ℓ 1)*(q 3), (ℓ 1)*(q 4) + (ℓ 2)*(q 3), (ℓ 1)*(q 5) + (ℓ 2)*(q 4), (ℓ 2)*(q 5)]

theorem eval_mulLin (ℓ : Fin 3 → R) (q : Fin 6 → R) (v : Fin 3 → R) :
    eval (mulLin ℓ q) v = (ℓ ⬝ᵥ v) * conicEval q v := by
  simp [eval_expand, mulLin, conicEval, conicMono, dotProduct, Fin.sum_univ_succ]
  ring

theorem mulLin_smul (ℓ : Fin 3 → R) (c : R) (q : Fin 6 → R) :
    mulLin ℓ (c • q) = c • mulLin ℓ q := by
  ext i
  fin_cases i <;> simp [mulLin] <;> ring

/-- `t`-linear coefficient of the monomials along `P + t • Q`. -/
def mono1 (P Q : Fin 3 → R) : Fin 10 → R :=
  ![3*(P 0)^2*(Q 0), (P 0)^2*(Q 1) + 2*(P 0)*(P 1)*(Q 0), (P 0)^2*(Q 2) + 2*(P 0)*(P 2)*(Q 0), 2*(P 0)*(P 1)*(Q 1) + (P 1)^2*(Q 0), (P 0)*(P 1)*(Q 2) + (P 0)*(P 2)*(Q 1) + (P 1)*(P 2)*(Q 0), 2*(P 0)*(P 2)*(Q 2) + (P 2)^2*(Q 0), 3*(P 1)^2*(Q 1), (P 1)^2*(Q 2) + 2*(P 1)*(P 2)*(Q 1), 2*(P 1)*(P 2)*(Q 2) + (P 2)^2*(Q 1), 3*(P 2)^2*(Q 2)]

/-- `t`-quadratic coefficient of the monomials along `P + t • Q`. -/
def mono2 (P Q : Fin 3 → R) : Fin 10 → R :=
  ![3*(P 0)*(Q 0)^2, 2*(P 0)*(Q 0)*(Q 1) + (P 1)*(Q 0)^2, 2*(P 0)*(Q 0)*(Q 2) + (P 2)*(Q 0)^2, (P 0)*(Q 1)^2 + 2*(P 1)*(Q 0)*(Q 1), (P 0)*(Q 1)*(Q 2) + (P 1)*(Q 0)*(Q 2) + (P 2)*(Q 0)*(Q 1), (P 0)*(Q 2)^2 + 2*(P 2)*(Q 0)*(Q 2), 3*(P 1)*(Q 1)^2, 2*(P 1)*(Q 1)*(Q 2) + (P 2)*(Q 1)^2, (P 1)*(Q 2)^2 + 2*(P 2)*(Q 1)*(Q 2), 3*(P 2)*(Q 2)^2]

/-- Restriction of `F` to the line through `P` (at `t = 0`) in direction `Q`. -/
noncomputable def restrict (F : PlaneCubic R) (P Q : Fin 3 → R) : Polynomial R :=
  Polynomial.C (eval F Q) * Polynomial.X ^ 3
    + Polynomial.C (∑ i, F i * mono2 P Q i) * Polynomial.X ^ 2
    + Polynomial.C (∑ i, F i * mono1 P Q i) * Polynomial.X + Polynomial.C (eval F P)

/-- Restriction of a cubic to a line: explicit cubic polynomial in `t`. -/
theorem eval_add_smul (F : PlaneCubic R) (P Q : Fin 3 → R) (t : R) :
    eval F (P + t • Q) = eval F Q * t ^ 3 + (∑ i, F i * mono2 P Q i) * t ^ 2
      + (∑ i, F i * mono1 P Q i) * t + eval F P := by
  simp [eval_expand, mono1, mono2, Fin.sum_univ_succ]
  ring

theorem restrict_eval (F : PlaneCubic R) (P Q : Fin 3 → R) (t : R) :
    (restrict F P Q).eval t = eval F (P + t • Q) := by
  simp only [restrict, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  rw [eval_add_smul]

theorem restrict_natDegree_le (F : PlaneCubic R) (P Q : Fin 3 → R) :
    (restrict F P Q).natDegree ≤ 3 := by
  unfold restrict
  compute_degree!

end CommRing

section Field

variable {K : Type*} [Field K]

/-- A polynomial identity `a t³ + b t² + c t + d = 0` for all `t` in an infinite field
forces all four coefficients to vanish. -/
theorem coeffs_eq_zero_of_forall [Infinite K] {a b c d : K}
    (h : ∀ t : K, a * t ^ 3 + b * t ^ 2 + c * t + d = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have hp : Polynomial.C a * Polynomial.X ^ 3 + Polynomial.C b * Polynomial.X ^ 2
      + Polynomial.C c * Polynomial.X + Polynomial.C d = 0 := by
    apply Polynomial.funext
    intro t
    simpa using h t
  have h3 := congrArg (fun p => Polynomial.coeff p 3) hp
  have h2 := congrArg (fun p => Polynomial.coeff p 2) hp
  have h1 := congrArg (fun p => Polynomial.coeff p 1) hp
  have h0 := congrArg (fun p => Polynomial.coeff p 0) hp
  simp [Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_X_pow] at h3 h2 h1 h0
  exact ⟨h3, h2, h1, h0⟩

/-- `K` has an element other than `0` and `1`, i.e. `K` has at least three elements.
This is the sharp hypothesis for the line lemma (see `line_lemma_false_zmod_two`). -/
class AtLeastThree (K : Type*) [Field K] : Prop where
  exists_ne : ∃ t : K, t ≠ 0 ∧ t ≠ 1

instance (priority := 100) AtLeastThree.of_infinite [Infinite K] : AtLeastThree K := by
  classical
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset ({(0 : K), 1} : Finset K)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
  exact ⟨t, ht⟩

/-- A field with at least three elements avoids any two prescribed values, one being `0`. -/
theorem AtLeastThree.exists_ne_zero_ne [AtLeastThree K] (c : K) : ∃ t : K, t ≠ 0 ∧ t ≠ c := by
  obtain ⟨t, ht0, ht1⟩ := AtLeastThree.exists_ne (K := K)
  by_cases hc : c = 1
  · exact ⟨t, ht0, hc ▸ ht1⟩
  · exact ⟨1, one_ne_zero, fun h => hc h.symm⟩

/-- Finite fields with at least three elements. -/
theorem AtLeastThree.of_card [Fintype K] (h : 3 ≤ Fintype.card K) : AtLeastThree K := by
  classical
  by_contra hK
  have hall : ∀ t : K, t ∈ ({0, 1} : Finset K) := fun t => by
    by_contra ht
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    exact hK ⟨⟨t, ht⟩⟩
  have hle : (Finset.univ : Finset K).card ≤ ({0, 1} : Finset K).card :=
    Finset.card_le_card fun t _ => hall t
  have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
  rw [Finset.card_univ] at hle
  omega

/-- Over a field with at least three elements, a cubic in `t` with zero leading coefficient
that vanishes identically has all coefficients zero (evaluate at `0, 1, t₀`). -/
theorem coeffs_eq_zero_of_forall_three [AtLeastThree K] {a b c d : K} (ha : a = 0)
    (h : ∀ t : K, a * t ^ 3 + b * t ^ 2 + c * t + d = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  obtain ⟨t, ht0, ht1⟩ := AtLeastThree.exists_ne (K := K)
  have e0 := h 0
  have e1 := h 1
  have et := h t
  subst ha
  have hd : d = 0 := by simpa using e0
  subst hd
  have hbc : b + c = 0 := by linear_combination e1
  have hb : b * (t * (t - 1)) = 0 := by linear_combination et - t * hbc
  have ht' : t * (t - 1) ≠ 0 := mul_ne_zero ht0 (sub_ne_zero.mpr ht1)
  have hb0 : b = 0 := (mul_eq_zero.mp hb).resolve_right ht'
  refine ⟨rfl, hb0, ?_, rfl⟩
  linear_combination hbc - hb0

/-- Line lemma, case `ℓ 0 ≠ 0`. -/
theorem line_lemma_aux0 [AtLeastThree K] (F : PlaneCubic K) (ℓ : Fin 3 → K) (hk : ℓ 0 ≠ 0)
    (hF : ∀ v : Fin 3 → K, ℓ ⬝ᵥ v = 0 → eval F v = 0) :
    ∃ q : Fin 6 → K, F = mulLin ℓ q := by
  have key : ∀ t : K, (-(F 0)*(ℓ 1)^3 + (F 1)*(ℓ 0)*(ℓ 1)^2 - (F 3)*(ℓ 0)^2*(ℓ 1) + (F 6)*(ℓ 0)^3) * t ^ 3 + (-3*(F 0)*(ℓ 1)^2*(ℓ 2) + 2*(F 1)*(ℓ 0)*(ℓ 1)*(ℓ 2) + (F 2)*(ℓ 0)*(ℓ 1)^2 - (F 3)*(ℓ 0)^2*(ℓ 2) - (F 4)*(ℓ 0)^2*(ℓ 1) + (F 7)*(ℓ 0)^3) * t ^ 2
      + (-3*(F 0)*(ℓ 1)*(ℓ 2)^2 + (F 1)*(ℓ 0)*(ℓ 2)^2 + 2*(F 2)*(ℓ 0)*(ℓ 1)*(ℓ 2) - (F 4)*(ℓ 0)^2*(ℓ 2) - (F 5)*(ℓ 0)^2*(ℓ 1) + (F 8)*(ℓ 0)^3) * t + (-(F 0)*(ℓ 2)^3 + (F 2)*(ℓ 0)*(ℓ 2)^2 - (F 5)*(ℓ 0)^2*(ℓ 2) + (F 9)*(ℓ 0)^3) = 0 := by
    intro t
    have hv := hF ![-(ℓ 1)*t - (ℓ 2), (ℓ 0)*t, (ℓ 0)]
      (by simp [dotProduct, Fin.sum_univ_succ]; ring)
    rw [eval_expand] at hv
    simp at hv
    linear_combination hv
  have hinf := hF ![-(ℓ 1), (ℓ 0), 0] (by simp [dotProduct, Fin.sum_univ_succ]; ring)
  rw [eval_expand] at hinf
  simp at hinf
  obtain ⟨h3, h2, h1, h0⟩ := coeffs_eq_zero_of_forall_three (by linear_combination hinf) key
  refine ⟨(ℓ 0 ^ 3)⁻¹ • ![(F 0)*(ℓ 0)^2, -(F 0)*(ℓ 0)*(ℓ 1) + (F 1)*(ℓ 0)^2, -(F 0)*(ℓ 0)*(ℓ 2) + (F 2)*(ℓ 0)^2, (F 0)*(ℓ 1)^2 - (F 1)*(ℓ 0)*(ℓ 1) + (F 3)*(ℓ 0)^2, 2*(F 0)*(ℓ 1)*(ℓ 2) - (F 1)*(ℓ 0)*(ℓ 2) - (F 2)*(ℓ 0)*(ℓ 1) + (F 4)*(ℓ 0)^2, (F 0)*(ℓ 2)^2 - (F 2)*(ℓ 0)*(ℓ 2) + (F 5)*(ℓ 0)^2], ?_⟩
  rw [mulLin_smul, eq_inv_smul_iff₀ (pow_ne_zero 3 hk)]
  funext i
  fin_cases i <;> simp [mulLin]
  · linear_combination
  · linear_combination
  · linear_combination
  · linear_combination
  · linear_combination
  · linear_combination
  · linear_combination h3
  · linear_combination h2
  · linear_combination h1
  · linear_combination h0

/-- Line lemma, case `ℓ 1 ≠ 0`. -/
theorem line_lemma_aux1 [AtLeastThree K] (F : PlaneCubic K) (ℓ : Fin 3 → K) (hk : ℓ 1 ≠ 0)
    (hF : ∀ v : Fin 3 → K, ℓ ⬝ᵥ v = 0 → eval F v = 0) :
    ∃ q : Fin 6 → K, F = mulLin ℓ q := by
  have key : ∀ t : K, ((F 0)*(ℓ 1)^3 - (F 1)*(ℓ 0)*(ℓ 1)^2 + (F 3)*(ℓ 0)^2*(ℓ 1) - (F 6)*(ℓ 0)^3) * t ^ 3 + (-(F 1)*(ℓ 1)^2*(ℓ 2) + (F 2)*(ℓ 1)^3 + 2*(F 3)*(ℓ 0)*(ℓ 1)*(ℓ 2) - (F 4)*(ℓ 0)*(ℓ 1)^2 - 3*(F 6)*(ℓ 0)^2*(ℓ 2) + (F 7)*(ℓ 0)^2*(ℓ 1)) * t ^ 2
      + ((F 3)*(ℓ 1)*(ℓ 2)^2 - (F 4)*(ℓ 1)^2*(ℓ 2) + (F 5)*(ℓ 1)^3 - 3*(F 6)*(ℓ 0)*(ℓ 2)^2 + 2*(F 7)*(ℓ 0)*(ℓ 1)*(ℓ 2) - (F 8)*(ℓ 0)*(ℓ 1)^2) * t + (-(F 6)*(ℓ 2)^3 + (F 7)*(ℓ 1)*(ℓ 2)^2 - (F 8)*(ℓ 1)^2*(ℓ 2) + (F 9)*(ℓ 1)^3) = 0 := by
    intro t
    have hv := hF ![(ℓ 1)*t, -(ℓ 0)*t - (ℓ 2), (ℓ 1)]
      (by simp [dotProduct, Fin.sum_univ_succ]; ring)
    rw [eval_expand] at hv
    simp at hv
    linear_combination hv
  have hinf := hF ![(ℓ 1), -(ℓ 0), 0] (by simp [dotProduct, Fin.sum_univ_succ]; ring)
  rw [eval_expand] at hinf
  simp at hinf
  obtain ⟨h3, h2, h1, h0⟩ := coeffs_eq_zero_of_forall_three (by linear_combination hinf) key
  refine ⟨(ℓ 1 ^ 3)⁻¹ • ![(F 1)*(ℓ 1)^2 - (F 3)*(ℓ 0)*(ℓ 1) + (F 6)*(ℓ 0)^2, (F 3)*(ℓ 1)^2 - (F 6)*(ℓ 0)*(ℓ 1), -(F 3)*(ℓ 1)*(ℓ 2) + (F 4)*(ℓ 1)^2 + 2*(F 6)*(ℓ 0)*(ℓ 2) - (F 7)*(ℓ 0)*(ℓ 1), (F 6)*(ℓ 1)^2, -(F 6)*(ℓ 1)*(ℓ 2) + (F 7)*(ℓ 1)^2, (F 6)*(ℓ 2)^2 - (F 7)*(ℓ 1)*(ℓ 2) + (F 8)*(ℓ 1)^2], ?_⟩
  rw [mulLin_smul, eq_inv_smul_iff₀ (pow_ne_zero 3 hk)]
  funext i
  fin_cases i <;> simp [mulLin]
  · linear_combination h3
  · linear_combination
  · linear_combination h2
  · linear_combination
  · linear_combination
  · linear_combination h1
  · linear_combination
  · linear_combination
  · linear_combination
  · linear_combination h0

/-- Line lemma, case `ℓ 2 ≠ 0`. -/
theorem line_lemma_aux2 [AtLeastThree K] (F : PlaneCubic K) (ℓ : Fin 3 → K) (hk : ℓ 2 ≠ 0)
    (hF : ∀ v : Fin 3 → K, ℓ ⬝ᵥ v = 0 → eval F v = 0) :
    ∃ q : Fin 6 → K, F = mulLin ℓ q := by
  have key : ∀ t : K, ((F 0)*(ℓ 2)^3 - (F 2)*(ℓ 0)*(ℓ 2)^2 + (F 5)*(ℓ 0)^2*(ℓ 2) - (F 9)*(ℓ 0)^3) * t ^ 3 + ((F 1)*(ℓ 2)^3 - (F 2)*(ℓ 1)*(ℓ 2)^2 - (F 4)*(ℓ 0)*(ℓ 2)^2 + 2*(F 5)*(ℓ 0)*(ℓ 1)*(ℓ 2) + (F 8)*(ℓ 0)^2*(ℓ 2) - 3*(F 9)*(ℓ 0)^2*(ℓ 1)) * t ^ 2
      + ((F 3)*(ℓ 2)^3 - (F 4)*(ℓ 1)*(ℓ 2)^2 + (F 5)*(ℓ 1)^2*(ℓ 2) - (F 7)*(ℓ 0)*(ℓ 2)^2 + 2*(F 8)*(ℓ 0)*(ℓ 1)*(ℓ 2) - 3*(F 9)*(ℓ 0)*(ℓ 1)^2) * t + ((F 6)*(ℓ 2)^3 - (F 7)*(ℓ 1)*(ℓ 2)^2 + (F 8)*(ℓ 1)^2*(ℓ 2) - (F 9)*(ℓ 1)^3) = 0 := by
    intro t
    have hv := hF ![(ℓ 2)*t, (ℓ 2), -(ℓ 0)*t - (ℓ 1)]
      (by simp [dotProduct, Fin.sum_univ_succ]; ring)
    rw [eval_expand] at hv
    simp at hv
    linear_combination hv
  have hinf := hF ![(ℓ 2), 0, -(ℓ 0)] (by simp [dotProduct, Fin.sum_univ_succ]; ring)
  rw [eval_expand] at hinf
  simp at hinf
  obtain ⟨h3, h2, h1, h0⟩ := coeffs_eq_zero_of_forall_three (by linear_combination hinf) key
  refine ⟨(ℓ 2 ^ 3)⁻¹ • ![(F 2)*(ℓ 2)^2 - (F 5)*(ℓ 0)*(ℓ 2) + (F 9)*(ℓ 0)^2, (F 4)*(ℓ 2)^2 - (F 5)*(ℓ 1)*(ℓ 2) - (F 8)*(ℓ 0)*(ℓ 2) + 2*(F 9)*(ℓ 0)*(ℓ 1), (F 5)*(ℓ 2)^2 - (F 9)*(ℓ 0)*(ℓ 2), (F 7)*(ℓ 2)^2 - (F 8)*(ℓ 1)*(ℓ 2) + (F 9)*(ℓ 1)^2, (F 8)*(ℓ 2)^2 - (F 9)*(ℓ 1)*(ℓ 2), (F 9)*(ℓ 2)^2], ?_⟩
  rw [mulLin_smul, eq_inv_smul_iff₀ (pow_ne_zero 3 hk)]
  funext i
  fin_cases i <;> simp [mulLin]
  · linear_combination h3
  · linear_combination h2
  · linear_combination
  · linear_combination h1
  · linear_combination
  · linear_combination
  · linear_combination h0
  · linear_combination
  · linear_combination
  · linear_combination

/-- **Line lemma.** Over a field `K` with at least three elements (`AtLeastThree K`,
automatic for infinite `K`), if a plane cubic `F` vanishes at every
point of the line `ℓ = 0` (with `ℓ ≠ 0`), then `F = ℓ · q` for some conic `q`.

The hypothesis is sharp: over `𝔽₂` the cubic `x²y + xy²` vanishes on every point of
`z = 0` without being divisible by `z` (`line_lemma_false_zmod_two`). -/
theorem line_lemma [AtLeastThree K] (F : PlaneCubic K) (ℓ : Fin 3 → K) (hℓ : ℓ ≠ 0)
    (hF : ∀ v : Fin 3 → K, ℓ ⬝ᵥ v = 0 → eval F v = 0) :
    ∃ q : Fin 6 → K, F = mulLin ℓ q := by
  by_cases h0 : ℓ 0 = 0
  · by_cases h1 : ℓ 1 = 0
    · have h2 : ℓ 2 ≠ 0 := by
        intro h2
        apply hℓ
        funext i
        fin_cases i <;> simp [h0, h1, h2]
      exact line_lemma_aux2 F ℓ h2 hF
    · exact line_lemma_aux1 F ℓ h1 hF
  · exact line_lemma_aux0 F ℓ h0 hF

/-- Converse: `ℓ · q` vanishes on the line `ℓ = 0`. -/
theorem eval_mulLin_of_dot_eq_zero (ℓ : Fin 3 → K) (q : Fin 6 → K) (v : Fin 3 → K)
    (hv : ℓ ⬝ᵥ v = 0) : eval (mulLin ℓ q) v = 0 := by
  simp [eval_mulLin, hv]

end Field

/-- **Sharpness of `AtLeastThree`.** Over `ZMod 2` the cubic `x²y + xy²` vanishes at every
point of the line `z = 0` but is not of the form `z · q`. -/
theorem line_lemma_false_zmod_two :
    (∀ v : Fin 3 → ZMod 2, (![0, 0, 1] : Fin 3 → ZMod 2) ⬝ᵥ v = 0 →
        eval (![0, 1, 0, 1, 0, 0, 0, 0, 0, 0] : PlaneCubic (ZMod 2)) v = 0) ∧
      ¬ ∃ q : Fin 6 → ZMod 2, (![0, 1, 0, 1, 0, 0, 0, 0, 0, 0] : PlaneCubic (ZMod 2)) =
        mulLin ![0, 0, 1] q := by
  refine ⟨fun v _ => ?_, fun ⟨q, hq⟩ => ?_⟩
  · have e0 : v 0 ^ 2 = v 0 := ZMod.pow_card (p := 2) (v 0)
    have e1 : v 1 ^ 2 = v 1 := ZMod.pow_card (p := 2) (v 1)
    rw [eval_expand]
    simp only [Matrix.cons_val, zero_mul, one_mul, add_zero, zero_add]
    rw [e0, e1, mul_comm (v 0) (v 1), CharTwo.add_self_eq_zero]
  · have := congrFun hq 1
    simp [mulLin] at this

end PlaneCubic
