import CayleyBacharach.Conic

/-!
# Restriction to the line through two points

For `a b : Fin 3 → K` with `n := a ⨯₃ b ≠ 0`, the line through `a, b` is `{v | n ⬝ᵥ v = 0}`.
-/

open Matrix

namespace PlaneCubic

section CommRing

variable {R : Type*} [CommRing R]

/-- Cramer's identity. -/
theorem cramer (a b v w : Fin 3 → R) :
    (a ⨯₃ b ⬝ᵥ w) • v = (a ⨯₃ b ⬝ᵥ v) • w - (w ⨯₃ b ⬝ᵥ v) • a - (a ⨯₃ w ⬝ᵥ v) • b := by
  ext i; fin_cases i <;> simp [cross_apply, dotProduct, Fin.sum_univ_succ] <;> ring

/-- Dual Cramer identity. -/
theorem dual_cramer (a b c l : Fin 3 → R) :
    (a ⨯₃ b ⬝ᵥ c) • l = (l ⬝ᵥ a) • (b ⨯₃ c) + (l ⬝ᵥ b) • (c ⨯₃ a) + (l ⬝ᵥ c) • (a ⨯₃ b) := by
  ext i; fin_cases i <;> simp [cross_apply, dotProduct, Fin.sum_univ_succ] <;> ring

/-- Binary expansion of a cubic along `s • a + t • b`. -/
theorem eval_smul_add_smul (F : PlaneCubic R) (a b : Fin 3 → R) (s t : R) :
    eval F (s • a + t • b) = s ^ 3 * eval F a + s ^ 2 * t * (∑ i, F i * mono1 a b i)
      + s * t ^ 2 * (∑ i, F i * mono2 a b i) + t ^ 3 * eval F b := by
  simp [eval_expand, mono1, mono2, Fin.sum_univ_succ]
  ring

/-- Mixed term of a conic along `s • a + t • b`. -/
def cmono1 (a b : Fin 3 → R) : Fin 6 → R :=
  ![2 * a 0 * b 0, a 0 * b 1 + a 1 * b 0, a 0 * b 2 + a 2 * b 0, 2 * a 1 * b 1,
    a 1 * b 2 + a 2 * b 1, 2 * a 2 * b 2]

theorem evalC_smul_add_smul (q : Fin 6 → R) (a b : Fin 3 → R) (s t : R) :
    evalC q (s • a + t • b) = s ^ 2 * evalC q a + s * t * (∑ j, q j * cmono1 a b j)
      + t ^ 2 * evalC q b := by
  simp [evalC_expand, cmono1, Fin.sum_univ_succ]
  ring

theorem cross_smul_add_smul (a b : Fin 3 → R) (s t s' t' : R) :
    (s • a + t • b) ⨯₃ (s' • a + t' • b) = (s * t' - s' * t) • (a ⨯₃ b) := by
  ext i; fin_cases i <;> simp [cross_apply] <;> ring

end CommRing

section Field

variable {K : Type*} [Field K]

/-- A point on the line through `a, b` (with `a ⨯₃ b ≠ 0`) is a combination of `a` and `b`. -/
theorem exists_smul_add_smul {a b v : Fin 3 → K} (hn : a ⨯₃ b ≠ 0) (hv : a ⨯₃ b ⬝ᵥ v = 0) :
    ∃ s t : K, v = s • a + t • b := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hn
  set w : Fin 3 → K := Pi.single k 1
  have hw : a ⨯₃ b ⬝ᵥ w = (a ⨯₃ b) k := by simp [w, dotProduct_single]
  have h := cramer a b v w
  rw [hv, hw, zero_smul, zero_sub] at h
  refine ⟨-((a ⨯₃ b) k)⁻¹ * (w ⨯₃ b ⬝ᵥ v), -((a ⨯₃ b) k)⁻¹ * (a ⨯₃ w ⬝ᵥ v), ?_⟩
  have h' := congrArg (fun x => ((a ⨯₃ b) k)⁻¹ • x) h
  simp only [smul_smul, inv_mul_cancel₀ hk, one_smul] at h'
  refine h'.trans ?_
  ext i
  simp [smul_eq_mul]
  ring

theorem cross_combo (a b : Fin 3 → K) (s t : K) :
    a ⨯₃ (s • a + t • b) = t • (a ⨯₃ b) ∧ b ⨯₃ (s • a + t • b) = (-s) • (a ⨯₃ b) := by
  constructor <;> (ext i; fin_cases i <;> simp [cross_apply] <;> ring)

/-- A linear form vanishing at two distinct points `u, v` is a multiple of `u ⨯₃ v`. -/
theorem lin_two {m u v : Fin 3 → K} (huv : u ⨯₃ v ≠ 0) (hu : m ⬝ᵥ u = 0) (hv : m ⬝ᵥ v = 0) :
    ∃ c : K, m = c • (u ⨯₃ v) := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp huv
  set w : Fin 3 → K := Pi.single k 1
  have hw : u ⨯₃ v ⬝ᵥ w = (u ⨯₃ v) k := by simp [w, dotProduct_single]
  have h := dual_cramer u v w m
  rw [hu, hv, hw, zero_smul, zero_smul, zero_add, zero_add] at h
  refine ⟨((u ⨯₃ v) k)⁻¹ * (m ⬝ᵥ w), ?_⟩
  have h' := congrArg (fun x => ((u ⨯₃ v) k)⁻¹ • x) h
  simp only [smul_smul, inv_mul_cancel₀ hk, one_smul] at h'
  exact h'

/-- A linear form vanishing at three non-collinear points is zero. -/
theorem lin_three {m u v w : Fin 3 → K} (h : u ⨯₃ v ⬝ᵥ w ≠ 0) (hu : m ⬝ᵥ u = 0)
    (hv : m ⬝ᵥ v = 0) (hw : m ⬝ᵥ w = 0) : m = 0 := by
  have e := dual_cramer u v w m
  rw [hu, hv, hw, zero_smul, zero_smul, zero_smul, zero_add, zero_add] at e
  exact (smul_eq_zero.mp e).resolve_left h

/-- If `ℓ ≠ 0` vanishes at distinct `u, v`, every point of `ℓ = 0` is `s • u + t • v`. -/
theorem on_line {ℓ u v x : Fin 3 → K} (hℓ : ℓ ≠ 0) (huv : u ⨯₃ v ≠ 0) (hu : ℓ ⬝ᵥ u = 0)
    (hv : ℓ ⬝ᵥ v = 0) (hx : ℓ ⬝ᵥ x = 0) : ∃ s t : K, x = s • u + t • v := by
  obtain ⟨c, hc⟩ := lin_two huv hu hv
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc; exact hℓ hc
  apply exists_smul_add_smul huv
  rw [hc, smul_dotProduct, smul_eq_mul] at hx
  exact (mul_eq_zero.mp hx).resolve_left hc0

/-- **Three points force a line into a conic.** -/
theorem conic_three {q : Fin 6 → K} {ℓ u v w : Fin 3 → K} (hℓ : ℓ ≠ 0)
    (huv : u ⨯₃ v ≠ 0) (huw : u ⨯₃ w ≠ 0) (hvw : v ⨯₃ w ≠ 0)
    (hu : ℓ ⬝ᵥ u = 0) (hv : ℓ ⬝ᵥ v = 0) (hw : ℓ ⬝ᵥ w = 0)
    (qu : evalC q u = 0) (qv : evalC q v = 0) (qw : evalC q w = 0) :
    ∃ m : Fin 3 → K, q = linMul ℓ m := by
  apply conic_line_lemma q ℓ hℓ
  intro x hx
  obtain ⟨s, t, rfl⟩ := on_line hℓ huv hu hv hx
  obtain ⟨s', t', rfl⟩ := on_line hℓ huv hu hv hw
  obtain ⟨c1, c2⟩ := cross_combo u v s' t'
  have ht : t' ≠ 0 := by rintro rfl; apply huw; rw [c1]; simp
  have hs : s' ≠ 0 := by rintro rfl; apply hvw; rw [c2]; simp
  rw [evalC_smul_add_smul, qu, qv] at qw ⊢
  have hB : (∑ j, q j * cmono1 u v j) = 0 := by
    have : s' * t' * (∑ j, q j * cmono1 u v j) = 0 := by linear_combination qw
    simpa [hs, ht] using this
  rw [hB]; ring

/-- **Four points force a line into a cubic.** -/
theorem cubic_four [AtLeastThree K] {F : PlaneCubic K} {ℓ u v w z : Fin 3 → K} (hℓ : ℓ ≠ 0)
    (huv : u ⨯₃ v ≠ 0) (huw : u ⨯₃ w ≠ 0) (hvw : v ⨯₃ w ≠ 0)
    (huz : u ⨯₃ z ≠ 0) (hvz : v ⨯₃ z ≠ 0) (hwz : w ⨯₃ z ≠ 0)
    (hu : ℓ ⬝ᵥ u = 0) (hv : ℓ ⬝ᵥ v = 0) (hw : ℓ ⬝ᵥ w = 0) (hz : ℓ ⬝ᵥ z = 0)
    (Fu : eval F u = 0) (Fv : eval F v = 0) (Fw : eval F w = 0) (Fz : eval F z = 0) :
    ∃ q : Fin 6 → K, F = mulLin ℓ q := by
  apply line_lemma F ℓ hℓ
  intro x hx
  obtain ⟨s, t, rfl⟩ := on_line hℓ huv hu hv hx
  obtain ⟨s1, t1, rfl⟩ := on_line hℓ huv hu hv hw
  obtain ⟨s2, t2, rfl⟩ := on_line hℓ huv hu hv hz
  obtain ⟨c1, c2⟩ := cross_combo u v s1 t1
  obtain ⟨d1, d2⟩ := cross_combo u v s2 t2
  have ht1 : t1 ≠ 0 := by rintro rfl; apply huw; rw [c1]; simp
  have hs1 : s1 ≠ 0 := by rintro rfl; apply hvw; rw [c2]; simp
  have ht2 : t2 ≠ 0 := by rintro rfl; apply huz; rw [d1]; simp
  have hs2 : s2 ≠ 0 := by rintro rfl; apply hvz; rw [d2]; simp
  have hwz' : s1 * t2 - s2 * t1 ≠ 0 := by
    intro h0; apply hwz
    rw [cross_smul_add_smul, h0, zero_smul]
  rw [eval_smul_add_smul, Fu, Fv] at Fw Fz ⊢
  set B1 := ∑ i, F i * mono1 u v i
  set B2 := ∑ i, F i * mono2 u v i
  have e1 : s1 * B1 + t1 * B2 = 0 := by
    have : (s1 * t1) * (s1 * B1 + t1 * B2) = 0 := by linear_combination Fw
    simpa [hs1, ht1] using this
  have e2 : s2 * B1 + t2 * B2 = 0 := by
    have : (s2 * t2) * (s2 * B1 + t2 * B2) = 0 := by linear_combination Fz
    simpa [hs2, ht2] using this
  have hB1 : B1 = 0 := by
    have : (s1 * t2 - s2 * t1) * B1 = 0 := by linear_combination t2 * e1 - t1 * e2
    simpa [hwz'] using this
  have hB2 : B2 = 0 := by
    have : (s1 * t2 - s2 * t1) * B2 = 0 := by linear_combination s1 * e2 - s2 * e1
    simpa [hwz'] using this
  rw [hB1, hB2]; ring

end Field

end PlaneCubic
