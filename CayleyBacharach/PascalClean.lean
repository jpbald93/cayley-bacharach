import CayleyBacharach.Pascal

/-!
# Pascal's theorem with only the natural hypotheses

Six pairwise non-proportional points `A₁, …, A₆` on a conic `q` that is not a product of two
linear forms. The side lines are `Lᵢⱼ = Aᵢ ⨯₃ Aⱼ` and the three "Pascal points" are the
explicit intersections `X = L₁₂ ⨯₃ L₄₅`, `Y = L₂₃ ⨯₃ L₅₆`, `Z = L₃₄ ⨯₃ L₆₁`.

All genericity hypotheses of `pascal_of_cayley_bacharach'` are derived:
* no three of the `Aᵢ` are collinear (`noncollinear_of_irreducible`, via `conic_three`);
* hence the nine side lines conditions `hL`, `X, Y, Z ≠ 0`, and the pairwise
  non-proportionality `hP` of all nine points (including `X, Y, Z` among themselves);
* also `X, Y, Z` are off the conic.
-/

open Matrix

namespace PlaneCubic

variable {K : Type*} [Field K]

theorem cross_ne_zero_symm {a b : Fin 3 → K} (h : a ⨯₃ b ≠ 0) : b ⨯₃ a ≠ 0 := by
  intro h'
  apply h
  rw [← cross_anticomm, h', neg_zero]

/-- If `v ≠ 0` and `w` is proportional to `v`, a linear form vanishing at `v` vanishes at `w`. -/
theorem dot_eq_zero_of_cross_eq_zero {l v w : Fin 3 → K} (hv : v ≠ 0) (h : v ⨯₃ w = 0)
    (hl : l ⬝ᵥ v = 0) : l ⬝ᵥ w = 0 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
  have e := smul_eq_smul_of_cross_eq_zero h k
  have e' := congrArg (fun x => l ⬝ᵥ x) e
  simp only [dotProduct_smul, smul_eq_mul, hl, mul_zero] at e'
  exact (mul_eq_zero.mp e'.symm).resolve_left hk

/-- A point on a line is not proportional to a point off it. -/
theorem cross_ne_zero_of_line {l v w : Fin 3 → K} (hv : v ≠ 0) (hl : l ⬝ᵥ v = 0)
    (hw : l ⬝ᵥ w ≠ 0) : v ⨯₃ w ≠ 0 :=
  fun h => hw (dot_eq_zero_of_cross_eq_zero hv h hl)

/-- The line `ab` differs from the line `cd` if `c` is not on `ab`. -/
theorem lines_ne_left {a b c d : Fin 3 → K} (hcd : c ⨯₃ d ≠ 0) (hc : a ⨯₃ b ⬝ᵥ c ≠ 0) :
    a ⨯₃ b ⨯₃ (c ⨯₃ d) ≠ 0 := by
  intro h
  have h' : c ⨯₃ d ⨯₃ (a ⨯₃ b) = 0 := by rw [← cross_anticomm, h, neg_zero]
  have := dot_eq_zero_of_cross_eq_zero (l := c) hcd h' (by rw [dotProduct_comm]; exact cross_dot_left _ _)
  exact hc (by rw [dotProduct_comm]; exact this)

/-- The line `ab` differs from the line `cd` if `d` is not on `ab`. -/
theorem lines_ne_right {a b c d : Fin 3 → K} (hcd : c ⨯₃ d ≠ 0) (hd : a ⨯₃ b ⬝ᵥ d ≠ 0) :
    a ⨯₃ b ⨯₃ (c ⨯₃ d) ≠ 0 := by
  intro h
  have h' : c ⨯₃ d ⨯₃ (a ⨯₃ b) = 0 := by rw [← cross_anticomm, h, neg_zero]
  have := dot_eq_zero_of_cross_eq_zero (l := d) hcd h' (by rw [dotProduct_comm]; exact cross_dot_right _ _)
  exact hd (by rw [dotProduct_comm]; exact this)

/-- **An irreducible conic meets a line in at most two points**: three pairwise
non-proportional points of a conic that is not a line pair are not collinear. -/
theorem noncollinear_of_irreducible {q : Fin 6 → K}
    (hirr : ∀ ℓ m : Fin 3 → K, q ≠ linMul ℓ m) {a b c : Fin 3 → K}
    (hab : a ⨯₃ b ≠ 0) (hac : a ⨯₃ c ≠ 0) (hbc : b ⨯₃ c ≠ 0)
    (qa : evalC q a = 0) (qb : evalC q b = 0) (qc : evalC q c = 0) :
    a ⨯₃ b ⬝ᵥ c ≠ 0 := by
  intro h
  obtain ⟨m, hm⟩ := conic_three hab hab hac hbc (cross_dot_left _ _) (cross_dot_right _ _) h
    qa qb qc
  exact hirr _ _ hm

/-- A point of the line `ab` other than `a, b` is off an irreducible conic through `a, b`. -/
theorem evalC_ne_zero_of_line {q : Fin 6 → K}
    (hirr : ∀ ℓ m : Fin 3 → K, q ≠ linMul ℓ m) {a b v : Fin 3 → K}
    (hab : a ⨯₃ b ≠ 0) (hav : a ⨯₃ v ≠ 0) (hbv : b ⨯₃ v ≠ 0) (hv : a ⨯₃ b ⬝ᵥ v = 0)
    (qa : evalC q a = 0) (qb : evalC q b = 0) : evalC q v ≠ 0 := fun qv =>
  noncollinear_of_irreducible hirr hab hav hbv qa qb qv hv

end PlaneCubic

namespace PlaneCubic

variable {K : Type*} [Field K]

/-- Pairwise non-proportionality of a list of nine vectors from the 36 facts `i < j`. -/
theorem pairwise9 {B0 B1 B2 B3 B4 B5 B6 B7 B8 : Fin 3 → K}
    (h01 : B0 ⨯₃ B1 ≠ 0) (h02 : B0 ⨯₃ B2 ≠ 0) (h03 : B0 ⨯₃ B3 ≠ 0) (h04 : B0 ⨯₃ B4 ≠ 0) (h05 :
    B0 ⨯₃ B5 ≠ 0) (h06 : B0 ⨯₃ B6 ≠ 0) (h07 : B0 ⨯₃ B7 ≠ 0) (h08 : B0 ⨯₃ B8 ≠ 0) (h12 : B1 ⨯₃
    B2 ≠ 0) (h13 : B1 ⨯₃ B3 ≠ 0) (h14 : B1 ⨯₃ B4 ≠ 0) (h15 : B1 ⨯₃ B5 ≠ 0) (h16 : B1 ⨯₃ B6 ≠
    0) (h17 : B1 ⨯₃ B7 ≠ 0) (h18 : B1 ⨯₃ B8 ≠ 0) (h23 : B2 ⨯₃ B3 ≠ 0) (h24 : B2 ⨯₃ B4 ≠ 0)
    (h25 : B2 ⨯₃ B5 ≠ 0) (h26 : B2 ⨯₃ B6 ≠ 0) (h27 : B2 ⨯₃ B7 ≠ 0) (h28 : B2 ⨯₃ B8 ≠ 0) (h34 :
    B3 ⨯₃ B4 ≠ 0) (h35 : B3 ⨯₃ B5 ≠ 0) (h36 : B3 ⨯₃ B6 ≠ 0) (h37 : B3 ⨯₃ B7 ≠ 0) (h38 : B3 ⨯₃
    B8 ≠ 0) (h45 : B4 ⨯₃ B5 ≠ 0) (h46 : B4 ⨯₃ B6 ≠ 0) (h47 : B4 ⨯₃ B7 ≠ 0) (h48 : B4 ⨯₃ B8 ≠
    0) (h56 : B5 ⨯₃ B6 ≠ 0) (h57 : B5 ⨯₃ B7 ≠ 0) (h58 : B5 ⨯₃ B8 ≠ 0) (h67 : B6 ⨯₃ B7 ≠ 0)
    (h68 : B6 ⨯₃ B8 ≠ 0) (h78 : B7 ⨯₃ B8 ≠ 0) :
    ∀ i j, i ≠ j → ![B0, B1, B2, B3, B4, B5, B6, B7, B8] i ⨯₃ ![B0, B1, B2, B3, B4, B5, B6, B7, B8] j ≠ 0 := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact h01
  · exact h02
  · exact h03
  · exact h04
  · exact h05
  · exact h06
  · exact h07
  · exact h08
  · exact cross_ne_zero_symm h01
  · exact absurd rfl hij
  · exact h12
  · exact h13
  · exact h14
  · exact h15
  · exact h16
  · exact h17
  · exact h18
  · exact cross_ne_zero_symm h02
  · exact cross_ne_zero_symm h12
  · exact absurd rfl hij
  · exact h23
  · exact h24
  · exact h25
  · exact h26
  · exact h27
  · exact h28
  · exact cross_ne_zero_symm h03
  · exact cross_ne_zero_symm h13
  · exact cross_ne_zero_symm h23
  · exact absurd rfl hij
  · exact h34
  · exact h35
  · exact h36
  · exact h37
  · exact h38
  · exact cross_ne_zero_symm h04
  · exact cross_ne_zero_symm h14
  · exact cross_ne_zero_symm h24
  · exact cross_ne_zero_symm h34
  · exact absurd rfl hij
  · exact h45
  · exact h46
  · exact h47
  · exact h48
  · exact cross_ne_zero_symm h05
  · exact cross_ne_zero_symm h15
  · exact cross_ne_zero_symm h25
  · exact cross_ne_zero_symm h35
  · exact cross_ne_zero_symm h45
  · exact absurd rfl hij
  · exact h56
  · exact h57
  · exact h58
  · exact cross_ne_zero_symm h06
  · exact cross_ne_zero_symm h16
  · exact cross_ne_zero_symm h26
  · exact cross_ne_zero_symm h36
  · exact cross_ne_zero_symm h46
  · exact cross_ne_zero_symm h56
  · exact absurd rfl hij
  · exact h67
  · exact h68
  · exact cross_ne_zero_symm h07
  · exact cross_ne_zero_symm h17
  · exact cross_ne_zero_symm h27
  · exact cross_ne_zero_symm h37
  · exact cross_ne_zero_symm h47
  · exact cross_ne_zero_symm h57
  · exact cross_ne_zero_symm h67
  · exact absurd rfl hij
  · exact h78
  · exact cross_ne_zero_symm h08
  · exact cross_ne_zero_symm h18
  · exact cross_ne_zero_symm h28
  · exact cross_ne_zero_symm h38
  · exact cross_ne_zero_symm h48
  · exact cross_ne_zero_symm h58
  · exact cross_ne_zero_symm h68
  · exact cross_ne_zero_symm h78
  · exact absurd rfl hij

/-- Nine side-line conditions from the nine facts. -/
theorem lines9 {f₀ f₁ f₂ g₀ g₁ g₂ : Fin 3 → K}
    (h00 : f₀ ⨯₃ g₀ ≠ 0) (h01 : f₀ ⨯₃ g₁ ≠ 0) (h02 : f₀ ⨯₃ g₂ ≠ 0)
    (h10 : f₁ ⨯₃ g₀ ≠ 0) (h11 : f₁ ⨯₃ g₁ ≠ 0) (h12 : f₁ ⨯₃ g₂ ≠ 0)
    (h20 : f₂ ⨯₃ g₀ ≠ 0) (h21 : f₂ ⨯₃ g₁ ≠ 0) (h22 : f₂ ⨯₃ g₂ ≠ 0) :
    ∀ i j : Fin 3, ![f₀, f₁, f₂] i ⨯₃ ![g₀, g₁, g₂] j ≠ 0 := by
  intro i j
  fin_cases i <;> fin_cases j
  exacts [h00, h01, h02, h10, h11, h12, h20, h21, h22]

/-- **Genericity for free.** Six pairwise non-proportional points on a conic that is not a
line pair, with `X = L₁₂ ⨯₃ L₄₅`, `Y = L₂₃ ⨯₃ L₅₆`, `Z = L₃₄ ⨯₃ L₆₁`: the hypotheses `hP`
(all nine points pairwise non-proportional) and `hL` (nine side-line conditions) of
`pascal_of_cayley_bacharach'` hold. -/
theorem pascal_generic (A₁ A₂ A₃ A₄ A₅ A₆ X Y Z : Fin 3 → K)
    (hA : ∀ i j, i ≠ j → ![A₁, A₂, A₃, A₄, A₅, A₆] i ⨯₃ ![A₁, A₂, A₃, A₄, A₅, A₆] j ≠ 0)
    (q : Fin 6 → K) (hirr : ∀ ℓ m : Fin 3 → K, q ≠ linMul ℓ m)
    (hq₁ : evalC q A₁ = 0) (hq₂ : evalC q A₂ = 0) (hq₃ : evalC q A₃ = 0)
    (hq₄ : evalC q A₄ = 0) (hq₅ : evalC q A₅ = 0) (hq₆ : evalC q A₆ = 0)
    (hX : X = A₁ ⨯₃ A₂ ⨯₃ (A₄ ⨯₃ A₅)) (hY : Y = A₂ ⨯₃ A₃ ⨯₃ (A₅ ⨯₃ A₆))
    (hZ : Z = A₃ ⨯₃ A₄ ⨯₃ (A₆ ⨯₃ A₁)) :
    (∀ i j, i ≠ j →
      ![A₁, A₂, A₃, A₄, A₅, A₆, X, Y, Z] i ⨯₃ ![A₁, A₂, A₃, A₄, A₅, A₆, X, Y, Z] j ≠ 0) ∧
    (∀ i j : Fin 3,
      ![A₁ ⨯₃ A₂, A₃ ⨯₃ A₄, A₅ ⨯₃ A₆] i ⨯₃ ![A₂ ⨯₃ A₃, A₄ ⨯₃ A₅, A₆ ⨯₃ A₁] j ≠ 0) := by
  have a12 : A₁ ⨯₃ A₂ ≠ 0 := hA 0 1 (by decide)
  have a13 : A₁ ⨯₃ A₃ ≠ 0 := hA 0 2 (by decide)
  have a14 : A₁ ⨯₃ A₄ ≠ 0 := hA 0 3 (by decide)
  have a15 : A₁ ⨯₃ A₅ ≠ 0 := hA 0 4 (by decide)
  have a16 : A₁ ⨯₃ A₆ ≠ 0 := hA 0 5 (by decide)
  have a23 : A₂ ⨯₃ A₃ ≠ 0 := hA 1 2 (by decide)
  have a24 : A₂ ⨯₃ A₄ ≠ 0 := hA 1 3 (by decide)
  have a25 : A₂ ⨯₃ A₅ ≠ 0 := hA 1 4 (by decide)
  have a26 : A₂ ⨯₃ A₆ ≠ 0 := hA 1 5 (by decide)
  have a34 : A₃ ⨯₃ A₄ ≠ 0 := hA 2 3 (by decide)
  have a35 : A₃ ⨯₃ A₅ ≠ 0 := hA 2 4 (by decide)
  have a36 : A₃ ⨯₃ A₆ ≠ 0 := hA 2 5 (by decide)
  have a45 : A₄ ⨯₃ A₅ ≠ 0 := hA 3 4 (by decide)
  have a46 : A₄ ⨯₃ A₆ ≠ 0 := hA 3 5 (by decide)
  have a56 : A₅ ⨯₃ A₆ ≠ 0 := hA 4 5 (by decide)
  have a21 : A₂ ⨯₃ A₁ ≠ 0 := cross_ne_zero_symm a12
  have a31 : A₃ ⨯₃ A₁ ≠ 0 := cross_ne_zero_symm a13
  have a32 : A₃ ⨯₃ A₂ ≠ 0 := cross_ne_zero_symm a23
  have a41 : A₄ ⨯₃ A₁ ≠ 0 := cross_ne_zero_symm a14
  have a42 : A₄ ⨯₃ A₂ ≠ 0 := cross_ne_zero_symm a24
  have a43 : A₄ ⨯₃ A₃ ≠ 0 := cross_ne_zero_symm a34
  have a51 : A₅ ⨯₃ A₁ ≠ 0 := cross_ne_zero_symm a15
  have a52 : A₅ ⨯₃ A₂ ≠ 0 := cross_ne_zero_symm a25
  have a53 : A₅ ⨯₃ A₃ ≠ 0 := cross_ne_zero_symm a35
  have a54 : A₅ ⨯₃ A₄ ≠ 0 := cross_ne_zero_symm a45
  have a61 : A₆ ⨯₃ A₁ ≠ 0 := cross_ne_zero_symm a16
  have a62 : A₆ ⨯₃ A₂ ≠ 0 := cross_ne_zero_symm a26
  have a63 : A₆ ⨯₃ A₃ ≠ 0 := cross_ne_zero_symm a36
  have a64 : A₆ ⨯₃ A₄ ≠ 0 := cross_ne_zero_symm a46
  have a65 : A₆ ⨯₃ A₅ ≠ 0 := cross_ne_zero_symm a56
  have t123 : A₁ ⨯₃ A₂ ⬝ᵥ A₃ ≠ 0 :=
    noncollinear_of_irreducible hirr a12 a13 a23 hq₁ hq₂ hq₃
  have l11 : A₁ ⨯₃ A₂ ⨯₃ (A₂ ⨯₃ A₃) ≠ 0 :=
    lines_ne_right a23 t123
  have t124 : A₁ ⨯₃ A₂ ⬝ᵥ A₄ ≠ 0 :=
    noncollinear_of_irreducible hirr a12 a14 a24 hq₁ hq₂ hq₄
  have l12 : A₁ ⨯₃ A₂ ⨯₃ (A₄ ⨯₃ A₅) ≠ 0 :=
    lines_ne_left a45 t124
  have t126 : A₁ ⨯₃ A₂ ⬝ᵥ A₆ ≠ 0 :=
    noncollinear_of_irreducible hirr a12 a16 a26 hq₁ hq₂ hq₆
  have l13 : A₁ ⨯₃ A₂ ⨯₃ (A₆ ⨯₃ A₁) ≠ 0 :=
    lines_ne_left a61 t126
  have t342 : A₃ ⨯₃ A₄ ⬝ᵥ A₂ ≠ 0 :=
    noncollinear_of_irreducible hirr a34 a32 a42 hq₃ hq₄ hq₂
  have l21 : A₃ ⨯₃ A₄ ⨯₃ (A₂ ⨯₃ A₃) ≠ 0 :=
    lines_ne_left a23 t342
  have t345 : A₃ ⨯₃ A₄ ⬝ᵥ A₅ ≠ 0 :=
    noncollinear_of_irreducible hirr a34 a35 a45 hq₃ hq₄ hq₅
  have l22 : A₃ ⨯₃ A₄ ⨯₃ (A₄ ⨯₃ A₅) ≠ 0 :=
    lines_ne_right a45 t345
  have t346 : A₃ ⨯₃ A₄ ⬝ᵥ A₆ ≠ 0 :=
    noncollinear_of_irreducible hirr a34 a36 a46 hq₃ hq₄ hq₆
  have l23 : A₃ ⨯₃ A₄ ⨯₃ (A₆ ⨯₃ A₁) ≠ 0 :=
    lines_ne_left a61 t346
  have t562 : A₅ ⨯₃ A₆ ⬝ᵥ A₂ ≠ 0 :=
    noncollinear_of_irreducible hirr a56 a52 a62 hq₅ hq₆ hq₂
  have l31 : A₅ ⨯₃ A₆ ⨯₃ (A₂ ⨯₃ A₃) ≠ 0 :=
    lines_ne_left a23 t562
  have t564 : A₅ ⨯₃ A₆ ⬝ᵥ A₄ ≠ 0 :=
    noncollinear_of_irreducible hirr a56 a54 a64 hq₅ hq₆ hq₄
  have l32 : A₅ ⨯₃ A₆ ⨯₃ (A₄ ⨯₃ A₅) ≠ 0 :=
    lines_ne_left a45 t564
  have t561 : A₅ ⨯₃ A₆ ⬝ᵥ A₁ ≠ 0 :=
    noncollinear_of_irreducible hirr a56 a51 a61 hq₅ hq₆ hq₁
  have l33 : A₅ ⨯₃ A₆ ⨯₃ (A₆ ⨯₃ A₁) ≠ 0 :=
    lines_ne_right a61 t561
  have hX0 : X ≠ 0 := hX ▸ l12
  have hY0 : Y ≠ 0 := hY ▸ cross_ne_zero_symm l31
  have hZ0 : Z ≠ 0 := hZ ▸ l23
  have hX1 : A₁ ⨯₃ A₂ ⬝ᵥ X = 0 := by rw [hX]; exact dot_self_cross _ _
  have hX2 : A₄ ⨯₃ A₅ ⬝ᵥ X = 0 := by rw [hX]; exact dot_cross_self _ _
  have hY1 : A₂ ⨯₃ A₃ ⬝ᵥ Y = 0 := by rw [hY]; exact dot_self_cross _ _
  have hY2 : A₅ ⨯₃ A₆ ⬝ᵥ Y = 0 := by rw [hY]; exact dot_cross_self _ _
  have hZ1 : A₃ ⨯₃ A₄ ⬝ᵥ Z = 0 := by rw [hZ]; exact dot_self_cross _ _
  have hZ2 : A₆ ⨯₃ A₁ ⬝ᵥ Z = 0 := by rw [hZ]; exact dot_cross_self _ _
  have t451 : A₄ ⨯₃ A₅ ⬝ᵥ A₁ ≠ 0 :=
    noncollinear_of_irreducible hirr a45 a41 a51 hq₄ hq₅ hq₁
  have xa1 : X ⨯₃ A₁ ≠ 0 := cross_ne_zero_of_line hX0 hX2 t451
  have t452 : A₄ ⨯₃ A₅ ⬝ᵥ A₂ ≠ 0 :=
    noncollinear_of_irreducible hirr a45 a42 a52 hq₄ hq₅ hq₂
  have xa2 : X ⨯₃ A₂ ≠ 0 := cross_ne_zero_of_line hX0 hX2 t452
  have xa3 : X ⨯₃ A₃ ≠ 0 := cross_ne_zero_of_line hX0 hX1 t123
  have xa4 : X ⨯₃ A₄ ≠ 0 := cross_ne_zero_of_line hX0 hX1 t124
  have t125 : A₁ ⨯₃ A₂ ⬝ᵥ A₅ ≠ 0 :=
    noncollinear_of_irreducible hirr a12 a15 a25 hq₁ hq₂ hq₅
  have xa5 : X ⨯₃ A₅ ≠ 0 := cross_ne_zero_of_line hX0 hX1 t125
  have xa6 : X ⨯₃ A₆ ≠ 0 := cross_ne_zero_of_line hX0 hX1 t126
  have t231 : A₂ ⨯₃ A₃ ⬝ᵥ A₁ ≠ 0 :=
    noncollinear_of_irreducible hirr a23 a21 a31 hq₂ hq₃ hq₁
  have ya1 : Y ⨯₃ A₁ ≠ 0 := cross_ne_zero_of_line hY0 hY1 t231
  have ya2 : Y ⨯₃ A₂ ≠ 0 := cross_ne_zero_of_line hY0 hY2 t562
  have t563 : A₅ ⨯₃ A₆ ⬝ᵥ A₃ ≠ 0 :=
    noncollinear_of_irreducible hirr a56 a53 a63 hq₅ hq₆ hq₃
  have ya3 : Y ⨯₃ A₃ ≠ 0 := cross_ne_zero_of_line hY0 hY2 t563
  have t234 : A₂ ⨯₃ A₃ ⬝ᵥ A₄ ≠ 0 :=
    noncollinear_of_irreducible hirr a23 a24 a34 hq₂ hq₃ hq₄
  have ya4 : Y ⨯₃ A₄ ≠ 0 := cross_ne_zero_of_line hY0 hY1 t234
  have t235 : A₂ ⨯₃ A₃ ⬝ᵥ A₅ ≠ 0 :=
    noncollinear_of_irreducible hirr a23 a25 a35 hq₂ hq₃ hq₅
  have ya5 : Y ⨯₃ A₅ ≠ 0 := cross_ne_zero_of_line hY0 hY1 t235
  have t236 : A₂ ⨯₃ A₃ ⬝ᵥ A₆ ≠ 0 :=
    noncollinear_of_irreducible hirr a23 a26 a36 hq₂ hq₃ hq₆
  have ya6 : Y ⨯₃ A₆ ≠ 0 := cross_ne_zero_of_line hY0 hY1 t236
  have t341 : A₃ ⨯₃ A₄ ⬝ᵥ A₁ ≠ 0 :=
    noncollinear_of_irreducible hirr a34 a31 a41 hq₃ hq₄ hq₁
  have za1 : Z ⨯₃ A₁ ≠ 0 := cross_ne_zero_of_line hZ0 hZ1 t341
  have za2 : Z ⨯₃ A₂ ≠ 0 := cross_ne_zero_of_line hZ0 hZ1 t342
  have t613 : A₆ ⨯₃ A₁ ⬝ᵥ A₃ ≠ 0 :=
    noncollinear_of_irreducible hirr a61 a63 a13 hq₆ hq₁ hq₃
  have za3 : Z ⨯₃ A₃ ≠ 0 := cross_ne_zero_of_line hZ0 hZ2 t613
  have t614 : A₆ ⨯₃ A₁ ⬝ᵥ A₄ ≠ 0 :=
    noncollinear_of_irreducible hirr a61 a64 a14 hq₆ hq₁ hq₄
  have za4 : Z ⨯₃ A₄ ≠ 0 := cross_ne_zero_of_line hZ0 hZ2 t614
  have za5 : Z ⨯₃ A₅ ≠ 0 := cross_ne_zero_of_line hZ0 hZ1 t345
  have za6 : Z ⨯₃ A₆ ≠ 0 := cross_ne_zero_of_line hZ0 hZ1 t346
  have xy : X ⨯₃ Y ≠ 0 := fun h => ya2 (cross_eq_zero_of_two_lines l11
    (dot_eq_zero_of_cross_eq_zero hX0 h hX1) hY1 (cross_dot_right _ _) (cross_dot_left _ _))
  have xz : X ⨯₃ Z ≠ 0 := fun h => za1 (cross_eq_zero_of_two_lines l13
    (dot_eq_zero_of_cross_eq_zero hX0 h hX1) hZ2 (cross_dot_left _ _) (cross_dot_right _ _))
  have yz : Y ⨯₃ Z ≠ 0 := fun h => za3 (cross_eq_zero_of_two_lines l21
    hZ1 (dot_eq_zero_of_cross_eq_zero hY0 h hY1) (cross_dot_left _ _) (cross_dot_right _ _))
  exact ⟨pairwise9 a12 a13 a14 a15 a16 (cross_ne_zero_symm xa1) (cross_ne_zero_symm ya1) (cross_ne_zero_symm za1) a23 a24 a25 a26 (cross_ne_zero_symm xa2) (cross_ne_zero_symm ya2) (cross_ne_zero_symm za2) a34 a35 a36 (cross_ne_zero_symm xa3) (cross_ne_zero_symm ya3) (cross_ne_zero_symm za3) a45 a46 (cross_ne_zero_symm xa4) (cross_ne_zero_symm ya4) (cross_ne_zero_symm za4) a56 (cross_ne_zero_symm xa5) (cross_ne_zero_symm ya5) (cross_ne_zero_symm za5) (cross_ne_zero_symm xa6) (cross_ne_zero_symm ya6) (cross_ne_zero_symm za6) xy xz yz,
    lines9 l11 l12 l13 l21 l22 l23 l31 l32 l33⟩

/-- **Pascal's theorem, natural hypotheses.** Six pairwise non-proportional points on a
conic `q` that is not a product of two linear forms: the three intersections of opposite
sides `L₁₂ ∩ L₄₅`, `L₂₃ ∩ L₅₆`, `L₃₄ ∩ L₆₁` (explicit cross products) are collinear. -/
theorem pascal_clean [CardGT K 10] (A₁ A₂ A₃ A₄ A₅ A₆ : Fin 3 → K)
    (hA : ∀ i j, i ≠ j → ![A₁, A₂, A₃, A₄, A₅, A₆] i ⨯₃ ![A₁, A₂, A₃, A₄, A₅, A₆] j ≠ 0)
    (q : Fin 6 → K) (hirr : ∀ ℓ m : Fin 3 → K, q ≠ linMul ℓ m)
    (hq₁ : evalC q A₁ = 0) (hq₂ : evalC q A₂ = 0) (hq₃ : evalC q A₃ = 0)
    (hq₄ : evalC q A₄ = 0) (hq₅ : evalC q A₅ = 0) (hq₆ : evalC q A₆ = 0) :
    Matrix.det ![A₁ ⨯₃ A₂ ⨯₃ (A₄ ⨯₃ A₅), A₂ ⨯₃ A₃ ⨯₃ (A₅ ⨯₃ A₆),
      A₃ ⨯₃ A₄ ⨯₃ (A₆ ⨯₃ A₁)] = 0 := by
  obtain ⟨hP, hL⟩ := pascal_generic A₁ A₂ A₃ A₄ A₅ A₆ _ _ _ hA q hirr hq₁ hq₂ hq₃ hq₄ hq₅ hq₆
    rfl rfl rfl
  exact pascal_of_cayley_bacharach' A₁ A₂ A₃ A₄ A₅ A₆ _ _ _ hP hL
    (dot_self_cross _ _) (dot_cross_self _ _) (dot_self_cross _ _) (dot_cross_self _ _)
    (dot_self_cross _ _) (dot_cross_self _ _) q hirr hq₁ hq₂ hq₃ hq₄ hq₅ hq₆

/-- The three Pascal points lie off the conic (each is a third point of a side line). -/
theorem pascal_points_off_conic (A₁ A₂ A₃ A₄ A₅ A₆ : Fin 3 → K)
    (hA : ∀ i j, i ≠ j → ![A₁, A₂, A₃, A₄, A₅, A₆] i ⨯₃ ![A₁, A₂, A₃, A₄, A₅, A₆] j ≠ 0)
    (q : Fin 6 → K) (hirr : ∀ ℓ m : Fin 3 → K, q ≠ linMul ℓ m)
    (hq₁ : evalC q A₁ = 0) (hq₂ : evalC q A₂ = 0) (hq₃ : evalC q A₃ = 0)
    (hq₄ : evalC q A₄ = 0) (hq₅ : evalC q A₅ = 0) (hq₆ : evalC q A₆ = 0) :
    evalC q (A₁ ⨯₃ A₂ ⨯₃ (A₄ ⨯₃ A₅)) ≠ 0 ∧ evalC q (A₂ ⨯₃ A₃ ⨯₃ (A₅ ⨯₃ A₆)) ≠ 0 ∧
      evalC q (A₃ ⨯₃ A₄ ⨯₃ (A₆ ⨯₃ A₁)) ≠ 0 := by
  obtain ⟨hP, -⟩ := pascal_generic A₁ A₂ A₃ A₄ A₅ A₆ _ _ _ hA q hirr hq₁ hq₂ hq₃ hq₄ hq₅ hq₆
    rfl rfl rfl
  have a12 : A₁ ⨯₃ A₂ ≠ 0 := hP 0 1 (by decide)
  have a23 : A₂ ⨯₃ A₃ ≠ 0 := hP 1 2 (by decide)
  have a34 : A₃ ⨯₃ A₄ ≠ 0 := hP 2 3 (by decide)
  have x1 : A₁ ⨯₃ (A₁ ⨯₃ A₂ ⨯₃ (A₄ ⨯₃ A₅)) ≠ 0 := hP 0 6 (by decide)
  have x2 : A₂ ⨯₃ (A₁ ⨯₃ A₂ ⨯₃ (A₄ ⨯₃ A₅)) ≠ 0 := hP 1 6 (by decide)
  have y2 : A₂ ⨯₃ (A₂ ⨯₃ A₃ ⨯₃ (A₅ ⨯₃ A₆)) ≠ 0 := hP 1 7 (by decide)
  have y3 : A₃ ⨯₃ (A₂ ⨯₃ A₃ ⨯₃ (A₅ ⨯₃ A₆)) ≠ 0 := hP 2 7 (by decide)
  have z3 : A₃ ⨯₃ (A₃ ⨯₃ A₄ ⨯₃ (A₆ ⨯₃ A₁)) ≠ 0 := hP 2 8 (by decide)
  have z4 : A₄ ⨯₃ (A₃ ⨯₃ A₄ ⨯₃ (A₆ ⨯₃ A₁)) ≠ 0 := hP 3 8 (by decide)
  exact ⟨evalC_ne_zero_of_line hirr a12 x1 x2 (dot_self_cross _ _) hq₁ hq₂,
    evalC_ne_zero_of_line hirr a23 y2 y3 (dot_self_cross _ _) hq₂ hq₃,
    evalC_ne_zero_of_line hirr a34 z3 z4 (dot_self_cross _ _) hq₃ hq₄⟩

end PlaneCubic
