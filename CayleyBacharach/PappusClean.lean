import CayleyBacharach.PascalClean

/-!
# Pappus with only the natural hypotheses, and a determinant criterion for conics
-/

open Matrix

namespace PlaneCubic

variable {K : Type*} [Field K]

/-- A point `v` on a line `l` and on the chord `ab` (with `a` on `l`, `b` off `l`) is
proportional to `a`. -/
theorem on_chord_prop {l a b v : Fin 3 → K} (hab : a ⨯₃ b ≠ 0) (ha : l ⬝ᵥ a = 0)
    (hb : l ⬝ᵥ b ≠ 0) (hv : a ⨯₃ b ⬝ᵥ v = 0) (hlv : l ⬝ᵥ v = 0) : a ⨯₃ v = 0 := by
  have hlm : a ⨯₃ b ⨯₃ l ≠ 0 := by
    intro h
    have := dot_eq_zero_of_cross_eq_zero (l := b) hab h
      (by rw [dotProduct_comm]; exact cross_dot_right a b)
    exact hb (by rw [dotProduct_comm]; exact this)
  exact cross_eq_zero_of_two_lines hlm (cross_dot_left a b) ha hv hlv

/-- The chord `ab` (`a` on `l`, `b` off `l`) misses every other point `c` of `l`. -/
theorem off_chord {l a b c : Fin 3 → K} (hab : a ⨯₃ b ≠ 0) (ha : l ⬝ᵥ a = 0)
    (hb : l ⬝ᵥ b ≠ 0) (hc : l ⬝ᵥ c = 0) (hac : a ⨯₃ c ≠ 0) : a ⨯₃ b ⬝ᵥ c ≠ 0 :=
  fun hv => hac (on_chord_prop hab ha hb hv hc)

/-- The chord `ab` (`a` off `m`, `b` on `m`) misses every other point `c` of `m`. -/
theorem off_chord' {m a b c : Fin 3 → K} (hab : a ⨯₃ b ≠ 0) (ha : m ⬝ᵥ a ≠ 0)
    (hb : m ⬝ᵥ b = 0) (hc : m ⬝ᵥ c = 0) (hbc : b ⨯₃ c ≠ 0) : a ⨯₃ b ⬝ᵥ c ≠ 0 := by
  intro hv
  refine off_chord (cross_ne_zero_symm hab) hb ha hc hbc ?_
  rw [← cross_anticomm, neg_dotProduct, hv, neg_zero]

end PlaneCubic

namespace PlaneCubic

variable {K : Type*} [Field K]

/-- Variant of `on_chord_prop` with the chord written `b ⨯₃ a`. -/
theorem on_chord_prop' {l a b v : Fin 3 → K} (hab : a ⨯₃ b ≠ 0) (ha : l ⬝ᵥ a = 0)
    (hb : l ⬝ᵥ b ≠ 0) (hv : b ⨯₃ a ⬝ᵥ v = 0) (hlv : l ⬝ᵥ v = 0) : a ⨯₃ v = 0 :=
  on_chord_prop hab ha hb (by rw [← cross_anticomm, neg_dotProduct, hv, neg_zero]) hlv

/-- **Pappus genericity for free.** `A₁, A₃, A₅` on `l`, `A₂, A₄, A₆` on `m`, none of the six
on the other line (i.e. not at `l ∩ m`), and the three points on each line pairwise
non-proportional. Then with `X = L₁₂ ⨯₃ L₄₅`, `Y = L₂₃ ⨯₃ L₅₆`, `Z = L₃₄ ⨯₃ L₆₁` all the
genericity hypotheses of `pappus_of_cayley_bacharach` hold. -/
theorem pappus_generic (A₁ A₂ A₃ A₄ A₅ A₆ X Y Z l m : Fin 3 → K)
    (hl₁ : l ⬝ᵥ A₁ = 0) (hl₃ : l ⬝ᵥ A₃ = 0) (hl₅ : l ⬝ᵥ A₅ = 0)
    (hm₂ : m ⬝ᵥ A₂ = 0) (hm₄ : m ⬝ᵥ A₄ = 0) (hm₆ : m ⬝ᵥ A₆ = 0)
    (hm₁ : m ⬝ᵥ A₁ ≠ 0) (hm₃ : m ⬝ᵥ A₃ ≠ 0) (hm₅ : m ⬝ᵥ A₅ ≠ 0)
    (hl₂ : l ⬝ᵥ A₂ ≠ 0) (hl₄ : l ⬝ᵥ A₄ ≠ 0) (hl₆ : l ⬝ᵥ A₆ ≠ 0)
    (a13 : A₁ ⨯₃ A₃ ≠ 0) (a15 : A₁ ⨯₃ A₅ ≠ 0) (a35 : A₃ ⨯₃ A₅ ≠ 0)
    (a24 : A₂ ⨯₃ A₄ ≠ 0) (a26 : A₂ ⨯₃ A₆ ≠ 0) (a46 : A₄ ⨯₃ A₆ ≠ 0)
    (hX : X = A₁ ⨯₃ A₂ ⨯₃ (A₄ ⨯₃ A₅)) (hY : Y = A₂ ⨯₃ A₃ ⨯₃ (A₅ ⨯₃ A₆))
    (hZ : Z = A₃ ⨯₃ A₄ ⨯₃ (A₆ ⨯₃ A₁)) :
    (∀ i j, i ≠ j →
      ![A₁, A₂, A₃, A₄, A₅, A₆, X, Y, Z] i ⨯₃ ![A₁, A₂, A₃, A₄, A₅, A₆, X, Y, Z] j ≠ 0) ∧
    (∀ i j : Fin 3,
      ![A₁ ⨯₃ A₂, A₃ ⨯₃ A₄, A₅ ⨯₃ A₆] i ⨯₃ ![A₂ ⨯₃ A₃, A₄ ⨯₃ A₅, A₆ ⨯₃ A₁] j ≠ 0) ∧
    l ⬝ᵥ Z ≠ 0 ∧ m ⬝ᵥ Z ≠ 0 := by
  have n1 : A₁ ≠ 0 := by rintro rfl; exact hm₁ (dotProduct_zero _)
  have n3 : A₃ ≠ 0 := by rintro rfl; exact hm₃ (dotProduct_zero _)
  have n5 : A₅ ≠ 0 := by rintro rfl; exact hm₅ (dotProduct_zero _)
  have n2 : A₂ ≠ 0 := by rintro rfl; exact hl₂ (dotProduct_zero _)
  have n4 : A₄ ≠ 0 := by rintro rfl; exact hl₄ (dotProduct_zero _)
  have n6 : A₆ ≠ 0 := by rintro rfl; exact hl₆ (dotProduct_zero _)
  -- odd–even pairs are non-proportional (one is on `l`, the other is not)
  have a12 : A₁ ⨯₃ A₂ ≠ 0 := cross_ne_zero_of_line n1 hl₁ hl₂
  have a14 : A₁ ⨯₃ A₄ ≠ 0 := cross_ne_zero_of_line n1 hl₁ hl₄
  have a16 : A₁ ⨯₃ A₆ ≠ 0 := cross_ne_zero_of_line n1 hl₁ hl₆
  have a32 : A₃ ⨯₃ A₂ ≠ 0 := cross_ne_zero_of_line n3 hl₃ hl₂
  have a34 : A₃ ⨯₃ A₄ ≠ 0 := cross_ne_zero_of_line n3 hl₃ hl₄
  have a36 : A₃ ⨯₃ A₆ ≠ 0 := cross_ne_zero_of_line n3 hl₃ hl₆
  have a52 : A₅ ⨯₃ A₂ ≠ 0 := cross_ne_zero_of_line n5 hl₅ hl₂
  have a54 : A₅ ⨯₃ A₄ ≠ 0 := cross_ne_zero_of_line n5 hl₅ hl₄
  have a56 : A₅ ⨯₃ A₆ ≠ 0 := cross_ne_zero_of_line n5 hl₅ hl₆
  have a21 : A₂ ⨯₃ A₁ ≠ 0 := cross_ne_zero_symm a12
  have a41 : A₄ ⨯₃ A₁ ≠ 0 := cross_ne_zero_symm a14
  have a61 : A₆ ⨯₃ A₁ ≠ 0 := cross_ne_zero_symm a16
  have a23 : A₂ ⨯₃ A₃ ≠ 0 := cross_ne_zero_symm a32
  have a43 : A₄ ⨯₃ A₃ ≠ 0 := cross_ne_zero_symm a34
  have a63 : A₆ ⨯₃ A₃ ≠ 0 := cross_ne_zero_symm a36
  have a25 : A₂ ⨯₃ A₅ ≠ 0 := cross_ne_zero_symm a52
  have a45 : A₄ ⨯₃ A₅ ≠ 0 := cross_ne_zero_symm a54
  have a65 : A₆ ⨯₃ A₅ ≠ 0 := cross_ne_zero_symm a56
  have a31 : A₃ ⨯₃ A₁ ≠ 0 := cross_ne_zero_symm a13
  have a51 : A₅ ⨯₃ A₁ ≠ 0 := cross_ne_zero_symm a15
  have a53 : A₅ ⨯₃ A₃ ≠ 0 := cross_ne_zero_symm a35
  have a42 : A₄ ⨯₃ A₂ ≠ 0 := cross_ne_zero_symm a24
  have a62 : A₆ ⨯₃ A₂ ≠ 0 := cross_ne_zero_symm a26
  have a64 : A₆ ⨯₃ A₄ ≠ 0 := cross_ne_zero_symm a46
  -- each side line misses the four other vertices
  have t123 : A₁ ⨯₃ A₂ ⬝ᵥ A₃ ≠ 0 := off_chord a12 hl₁ hl₂ hl₃ a13
  have t125 : A₁ ⨯₃ A₂ ⬝ᵥ A₅ ≠ 0 := off_chord a12 hl₁ hl₂ hl₅ a15
  have t124 : A₁ ⨯₃ A₂ ⬝ᵥ A₄ ≠ 0 := off_chord' a12 hm₁ hm₂ hm₄ a24
  have t126 : A₁ ⨯₃ A₂ ⬝ᵥ A₆ ≠ 0 := off_chord' a12 hm₁ hm₂ hm₆ a26
  have t341 : A₃ ⨯₃ A₄ ⬝ᵥ A₁ ≠ 0 := off_chord a34 hl₃ hl₄ hl₁ a31
  have t345 : A₃ ⨯₃ A₄ ⬝ᵥ A₅ ≠ 0 := off_chord a34 hl₃ hl₄ hl₅ a35
  have t342 : A₃ ⨯₃ A₄ ⬝ᵥ A₂ ≠ 0 := off_chord' a34 hm₃ hm₄ hm₂ a42
  have t346 : A₃ ⨯₃ A₄ ⬝ᵥ A₆ ≠ 0 := off_chord' a34 hm₃ hm₄ hm₆ a46
  have t561 : A₅ ⨯₃ A₆ ⬝ᵥ A₁ ≠ 0 := off_chord a56 hl₅ hl₆ hl₁ a51
  have t563 : A₅ ⨯₃ A₆ ⬝ᵥ A₃ ≠ 0 := off_chord a56 hl₅ hl₆ hl₃ a53
  have t562 : A₅ ⨯₃ A₆ ⬝ᵥ A₂ ≠ 0 := off_chord' a56 hm₅ hm₆ hm₂ a62
  have t564 : A₅ ⨯₃ A₆ ⬝ᵥ A₄ ≠ 0 := off_chord' a56 hm₅ hm₆ hm₄ a64
  have t234 : A₂ ⨯₃ A₃ ⬝ᵥ A₄ ≠ 0 := off_chord a23 hm₂ hm₃ hm₄ a24
  have t236 : A₂ ⨯₃ A₃ ⬝ᵥ A₆ ≠ 0 := off_chord a23 hm₂ hm₃ hm₆ a26
  have t231 : A₂ ⨯₃ A₃ ⬝ᵥ A₁ ≠ 0 := off_chord' a23 hl₂ hl₃ hl₁ a31
  have t235 : A₂ ⨯₃ A₃ ⬝ᵥ A₅ ≠ 0 := off_chord' a23 hl₂ hl₃ hl₅ a35
  have t452 : A₄ ⨯₃ A₅ ⬝ᵥ A₂ ≠ 0 := off_chord a45 hm₄ hm₅ hm₂ a42
  have t451 : A₄ ⨯₃ A₅ ⬝ᵥ A₁ ≠ 0 := off_chord' a45 hl₄ hl₅ hl₁ a51
  have t614 : A₆ ⨯₃ A₁ ⬝ᵥ A₄ ≠ 0 := off_chord a61 hm₆ hm₁ hm₄ a64
  have t613 : A₆ ⨯₃ A₁ ⬝ᵥ A₃ ≠ 0 := off_chord' a61 hl₆ hl₁ hl₃ a13
  -- the nine side-line conditions
  have l11 : A₁ ⨯₃ A₂ ⨯₃ (A₂ ⨯₃ A₃) ≠ 0 := lines_ne_right a23 t123
  have l12 : A₁ ⨯₃ A₂ ⨯₃ (A₄ ⨯₃ A₅) ≠ 0 := lines_ne_left a45 t124
  have l13 : A₁ ⨯₃ A₂ ⨯₃ (A₆ ⨯₃ A₁) ≠ 0 := lines_ne_left a61 t126
  have l21 : A₃ ⨯₃ A₄ ⨯₃ (A₂ ⨯₃ A₃) ≠ 0 := lines_ne_left a23 t342
  have l22 : A₃ ⨯₃ A₄ ⨯₃ (A₄ ⨯₃ A₅) ≠ 0 := lines_ne_right a45 t345
  have l23 : A₃ ⨯₃ A₄ ⨯₃ (A₆ ⨯₃ A₁) ≠ 0 := lines_ne_left a61 t346
  have l31 : A₅ ⨯₃ A₆ ⨯₃ (A₂ ⨯₃ A₃) ≠ 0 := lines_ne_left a23 t562
  have l32 : A₅ ⨯₃ A₆ ⨯₃ (A₄ ⨯₃ A₅) ≠ 0 := lines_ne_left a45 t564
  have l33 : A₅ ⨯₃ A₆ ⨯₃ (A₆ ⨯₃ A₁) ≠ 0 := lines_ne_right a61 t561
  have hX0 : X ≠ 0 := hX ▸ l12
  have hY0 : Y ≠ 0 := hY ▸ cross_ne_zero_symm l31
  have hZ0 : Z ≠ 0 := hZ ▸ l23
  have hX1 : A₁ ⨯₃ A₂ ⬝ᵥ X = 0 := by rw [hX]; exact dot_self_cross _ _
  have hX2 : A₄ ⨯₃ A₅ ⬝ᵥ X = 0 := by rw [hX]; exact dot_cross_self _ _
  have hY1 : A₂ ⨯₃ A₃ ⬝ᵥ Y = 0 := by rw [hY]; exact dot_self_cross _ _
  have hY2 : A₅ ⨯₃ A₆ ⬝ᵥ Y = 0 := by rw [hY]; exact dot_cross_self _ _
  have hZ1 : A₃ ⨯₃ A₄ ⬝ᵥ Z = 0 := by rw [hZ]; exact dot_self_cross _ _
  have hZ2 : A₆ ⨯₃ A₁ ⬝ᵥ Z = 0 := by rw [hZ]; exact dot_cross_self _ _
  -- the Pappus points against the vertices
  have xa1 : X ⨯₃ A₁ ≠ 0 := cross_ne_zero_of_line hX0 hX2 t451
  have xa2 : X ⨯₃ A₂ ≠ 0 := cross_ne_zero_of_line hX0 hX2 t452
  have xa3 : X ⨯₃ A₃ ≠ 0 := cross_ne_zero_of_line hX0 hX1 t123
  have xa4 : X ⨯₃ A₄ ≠ 0 := cross_ne_zero_of_line hX0 hX1 t124
  have xa5 : X ⨯₃ A₅ ≠ 0 := cross_ne_zero_of_line hX0 hX1 t125
  have xa6 : X ⨯₃ A₆ ≠ 0 := cross_ne_zero_of_line hX0 hX1 t126
  have ya1 : Y ⨯₃ A₁ ≠ 0 := cross_ne_zero_of_line hY0 hY1 t231
  have ya2 : Y ⨯₃ A₂ ≠ 0 := cross_ne_zero_of_line hY0 hY2 t562
  have ya3 : Y ⨯₃ A₃ ≠ 0 := cross_ne_zero_of_line hY0 hY2 t563
  have ya4 : Y ⨯₃ A₄ ≠ 0 := cross_ne_zero_of_line hY0 hY1 t234
  have ya5 : Y ⨯₃ A₅ ≠ 0 := cross_ne_zero_of_line hY0 hY1 t235
  have ya6 : Y ⨯₃ A₆ ≠ 0 := cross_ne_zero_of_line hY0 hY1 t236
  have za1 : Z ⨯₃ A₁ ≠ 0 := cross_ne_zero_of_line hZ0 hZ1 t341
  have za2 : Z ⨯₃ A₂ ≠ 0 := cross_ne_zero_of_line hZ0 hZ1 t342
  have za3 : Z ⨯₃ A₃ ≠ 0 := cross_ne_zero_of_line hZ0 hZ2 t613
  have za4 : Z ⨯₃ A₄ ≠ 0 := cross_ne_zero_of_line hZ0 hZ2 t614
  have za5 : Z ⨯₃ A₅ ≠ 0 := cross_ne_zero_of_line hZ0 hZ1 t345
  have za6 : Z ⨯₃ A₆ ≠ 0 := cross_ne_zero_of_line hZ0 hZ1 t346
  have xy : X ⨯₃ Y ≠ 0 := fun h => ya2 (cross_eq_zero_of_two_lines l11
    (dot_eq_zero_of_cross_eq_zero hX0 h hX1) hY1 (cross_dot_right _ _) (cross_dot_left _ _))
  have xz : X ⨯₃ Z ≠ 0 := fun h => za1 (cross_eq_zero_of_two_lines l13
    (dot_eq_zero_of_cross_eq_zero hX0 h hX1) hZ2 (cross_dot_left _ _) (cross_dot_right _ _))
  have yz : Y ⨯₃ Z ≠ 0 := fun h => za3 (cross_eq_zero_of_two_lines l21
    hZ1 (dot_eq_zero_of_cross_eq_zero hY0 h hY1) (cross_dot_left _ _) (cross_dot_right _ _))
  -- `Z` is on neither line
  have lZ : l ⬝ᵥ Z ≠ 0 := fun h => cross_ne_zero_symm za1 (on_chord_prop' a16 hl₁ hl₆ hZ2 h)
  have mZ : m ⬝ᵥ Z ≠ 0 := fun h => cross_ne_zero_symm za4 (on_chord_prop' a43 hm₄ hm₃ hZ1 h)
  exact ⟨pairwise9 a12 a13 a14 a15 a16 (cross_ne_zero_symm xa1) (cross_ne_zero_symm ya1) (cross_ne_zero_symm za1) a23 a24 a25 a26 (cross_ne_zero_symm xa2) (cross_ne_zero_symm ya2) (cross_ne_zero_symm za2) a34 a35 a36 (cross_ne_zero_symm xa3) (cross_ne_zero_symm ya3) (cross_ne_zero_symm za3) a45 a46 (cross_ne_zero_symm xa4) (cross_ne_zero_symm ya4) (cross_ne_zero_symm za4) a56 (cross_ne_zero_symm xa5) (cross_ne_zero_symm ya5) (cross_ne_zero_symm za5) (cross_ne_zero_symm xa6) (cross_ne_zero_symm ya6) (cross_ne_zero_symm za6) xy xz yz,
    lines9 l11 l12 l13 l21 l22 l23 l31 l32 l33, lZ, mZ⟩

end PlaneCubic

namespace PlaneCubic

variable {K : Type*} [Field K]

/-- **Pappus's theorem, natural hypotheses.** `A₁, A₃, A₅` pairwise non-proportional on a
line `l`, `A₂, A₄, A₆` pairwise non-proportional on a line `m`, and none of the six on the
other line (i.e. none at `l ∩ m`). Then the three points `L₁₂ ∩ L₄₅`, `L₂₃ ∩ L₅₆`,
`L₃₄ ∩ L₆₁` (explicit cross products) are collinear. `l ≠ m` and `l, m ≠ 0` are not
assumed separately: they follow from `m ⬝ᵥ A₁ ≠ 0`, `l ⬝ᵥ A₂ ≠ 0` and the incidences. -/
theorem pappus_clean [CardGT K 10] (A₁ A₂ A₃ A₄ A₅ A₆ l m : Fin 3 → K)
    (hl₁ : l ⬝ᵥ A₁ = 0) (hl₃ : l ⬝ᵥ A₃ = 0) (hl₅ : l ⬝ᵥ A₅ = 0)
    (hm₂ : m ⬝ᵥ A₂ = 0) (hm₄ : m ⬝ᵥ A₄ = 0) (hm₆ : m ⬝ᵥ A₆ = 0)
    (hm₁ : m ⬝ᵥ A₁ ≠ 0) (hm₃ : m ⬝ᵥ A₃ ≠ 0) (hm₅ : m ⬝ᵥ A₅ ≠ 0)
    (hl₂ : l ⬝ᵥ A₂ ≠ 0) (hl₄ : l ⬝ᵥ A₄ ≠ 0) (hl₆ : l ⬝ᵥ A₆ ≠ 0)
    (a13 : A₁ ⨯₃ A₃ ≠ 0) (a15 : A₁ ⨯₃ A₅ ≠ 0) (a35 : A₃ ⨯₃ A₅ ≠ 0)
    (a24 : A₂ ⨯₃ A₄ ≠ 0) (a26 : A₂ ⨯₃ A₆ ≠ 0) (a46 : A₄ ⨯₃ A₆ ≠ 0) :
    Matrix.det ![A₁ ⨯₃ A₂ ⨯₃ (A₄ ⨯₃ A₅), A₂ ⨯₃ A₃ ⨯₃ (A₅ ⨯₃ A₆),
      A₃ ⨯₃ A₄ ⨯₃ (A₆ ⨯₃ A₁)] = 0 := by
  obtain ⟨hP, hL, hlZ, hmZ⟩ := pappus_generic A₁ A₂ A₃ A₄ A₅ A₆ _ _ _ l m hl₁ hl₃ hl₅
    hm₂ hm₄ hm₆ hm₁ hm₃ hm₅ hl₂ hl₄ hl₆ a13 a15 a35 a24 a26 a46 rfl rfl rfl
  exact pappus_of_cayley_bacharach A₁ A₂ A₃ A₄ A₅ A₆ _ _ _ l m hP hL
    (dot_self_cross _ _) (dot_cross_self _ _) (dot_self_cross _ _) (dot_cross_self _ _)
    (dot_self_cross _ _) (dot_cross_self _ _) hl₁ hl₃ hl₅ hm₂ hm₄ hm₆ hlZ hmZ

/-- The hypotheses of `pappus_clean` force `l, m` to be nonzero and non-proportional. -/
theorem pappus_lines_distinct (A₁ A₂ l m : Fin 3 → K) (hl₁ : l ⬝ᵥ A₁ = 0)
    (hm₁ : m ⬝ᵥ A₁ ≠ 0) (hl₂ : l ⬝ᵥ A₂ ≠ 0) : l ⨯₃ m ≠ 0 := by
  intro h
  have hl0 : l ≠ 0 := by rintro rfl; exact hl₂ (zero_dotProduct _)
  have h1 : A₁ ⬝ᵥ l = 0 := by rw [dotProduct_comm]; exact hl₁
  have h2 : A₁ ⬝ᵥ m = 0 := dot_eq_zero_of_cross_eq_zero hl0 h h1
  exact hm₁ (by rw [dotProduct_comm]; exact h2)

end PlaneCubic

namespace PlaneCubic

variable {K : Type*} [Field K]

/-- The symmetric (Gram) matrix of the conic `q = q₀x² + q₁xy + q₂xz + q₃y² + q₄yz + q₅z²`,
off-diagonal entries halved, so that `vᵀ M(q) v = q(v)` when `(2 : K) ≠ 0`. -/
def gram (q : Fin 6 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![q 0, q 1 / 2, q 2 / 2; q 1 / 2, q 3, q 4 / 2; q 2 / 2, q 4 / 2, q 5]

/-- `vᵀ M(q) v = q(v)` (needs `2 ≠ 0`). -/
theorem gram_quadForm (h2 : (2 : K) ≠ 0) (q : Fin 6 → K) (v : Fin 3 → K) :
    v ⬝ᵥ (gram q *ᵥ v) = evalC q v := by
  rw [evalC_expand]
  simp [gram, dotProduct, mulVec, Fin.sum_univ_succ]
  field_simp
  ring

/-- **A line pair has singular Gram matrix.** If `q = ℓ · m` and `(2 : K) ≠ 0` then
`det M(q) = 0`. (In characteristic 2, `2⁻¹ = 0` in Lean and the statement fails.) -/
theorem det_gram_linMul (h2 : (2 : K) ≠ 0) (ℓ m : Fin 3 → K) :
    (gram (linMul ℓ m)).det = 0 := by
  simp [gram, linMul, Matrix.det_fin_three]
  field_simp
  ring

/-- Contrapositive: `det M(q) ≠ 0` implies `q` is not a product of two linear forms. -/
theorem not_linMul_of_det_gram_ne_zero (h2 : (2 : K) ≠ 0) {q : Fin 6 → K}
    (h : (gram q).det ≠ 0) : ∀ ℓ m : Fin 3 → K, q ≠ linMul ℓ m := by
  rintro ℓ m rfl
  exact h (det_gram_linMul h2 ℓ m)

/-- **Pascal's theorem for a nondegenerate conic** (`det M(q) ≠ 0`). -/
theorem pascal_clean_det [CardGT K 10] (h2 : (2 : K) ≠ 0) (A₁ A₂ A₃ A₄ A₅ A₆ : Fin 3 → K)
    (hA : ∀ i j, i ≠ j → ![A₁, A₂, A₃, A₄, A₅, A₆] i ⨯₃ ![A₁, A₂, A₃, A₄, A₅, A₆] j ≠ 0)
    (q : Fin 6 → K) (hdet : (gram q).det ≠ 0)
    (hq₁ : evalC q A₁ = 0) (hq₂ : evalC q A₂ = 0) (hq₃ : evalC q A₃ = 0)
    (hq₄ : evalC q A₄ = 0) (hq₅ : evalC q A₅ = 0) (hq₆ : evalC q A₆ = 0) :
    Matrix.det ![A₁ ⨯₃ A₂ ⨯₃ (A₄ ⨯₃ A₅), A₂ ⨯₃ A₃ ⨯₃ (A₅ ⨯₃ A₆),
      A₃ ⨯₃ A₄ ⨯₃ (A₆ ⨯₃ A₁)] = 0 :=
  pascal_clean A₁ A₂ A₃ A₄ A₅ A₆ hA q (not_linMul_of_det_gram_ne_zero h2 hdet)
    hq₁ hq₂ hq₃ hq₄ hq₅ hq₆

end PlaneCubic

namespace PlaneCubic

/-- **`(2 : K) ≠ 0` is needed in `det_gram_linMul`.** Over `ZMod 2` (where `2⁻¹ = 0`), the
square `(x + y + z)²` has Gram matrix `diag(1,1,1)`, of determinant `1`. -/
theorem det_gram_linMul_char_two :
    (gram (linMul (fun _ => (1 : ZMod 2)) (fun _ => 1))).det = 1 := by
  have h : (2 : ZMod 2) = 0 := rfl
  simp [gram, linMul, Matrix.det_fin_three, one_add_one_eq_two, h]

end PlaneCubic

namespace PlaneCubic

variable {K : Type*} [Field K]

/-- The mixed term of `q(s•v + t•w)` is twice the Gram bilinear form. -/
theorem cmono1_sum_eq_gram (h2 : (2 : K) ≠ 0) (q : Fin 6 → K) (v w : Fin 3 → K) :
    ∑ j, q j * cmono1 v w j = 2 * (w ⬝ᵥ (gram q *ᵥ v)) := by
  simp [cmono1, gram, dotProduct, mulVec, Fin.sum_univ_succ]
  field_simp
  ring

/-- **Converse over an algebraically closed field.** If `(2 : K) ≠ 0` and `det M(q) = 0`,
then `q` is a product of two linear forms. Proof: a kernel vector `v` of `M(q)` is a
singular point of `q`; a second zero `w` of `q` off `v` exists (a quadratic on a line
missing `v` has a root); `q` vanishes on the whole line `vw`, so `conic_line_lemma`
splits off that line. -/
theorem exists_linMul_of_det_gram_eq_zero [IsAlgClosed K] (h2 : (2 : K) ≠ 0)
    (q : Fin 6 → K) (h : (gram q).det = 0) : ∃ ℓ m : Fin 3 → K, q = linMul ℓ m := by
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have qv : evalC q v = 0 := by rw [← gram_quadForm h2, hv, dotProduct_zero]
  have key : ∃ w, evalC q w = 0 ∧ w ⨯₃ v ≠ 0 := by
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hv0
    have hk' : v k ≠ 0 := hk
    set e : Fin 3 → K := Pi.single k 1 with he
    have ev : e ⬝ᵥ v ≠ 0 := by rw [he, single_dotProduct, one_mul]; exact hk'
    obtain ⟨a, b, ha, hb, hab⟩ := exists_line_basis e
    have hne : ∀ s : K, a + s • b ≠ 0 := by
      intro s hs
      apply hab
      rw [eq_neg_of_add_eq_zero_left hs]
      ext i; fin_cases i <;> simp
    have hon : ∀ s : K, e ⬝ᵥ (a + s • b) = 0 := by
      intro s; rw [dotProduct_add, dotProduct_smul, ha, hb, smul_zero, add_zero]
    have b0 : b ≠ 0 := by
      rintro rfl; apply hab
      ext i; fin_cases i <;> simp
    by_cases qb : evalC q b = 0
    · exact ⟨b, qb, cross_ne_zero_of_line b0 hb ev⟩
    · have : NeZero (2 : K) := ⟨h2⟩
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_eq_mul_self
        (discrim (evalC q b) (∑ j, q j * cmono1 a b j) (evalC q a))
      obtain ⟨s, hs⟩ := exists_quadratic_eq_zero qb ⟨z, hz⟩
      refine ⟨a + s • b, ?_, cross_ne_zero_of_line (hne s) (hon s) ev⟩
      have e1 := evalC_smul_add_smul q a b 1 s
      rw [one_smul] at e1
      rw [e1]
      linear_combination hs
  obtain ⟨w, qw, hwv⟩ := key
  have hvw : v ⨯₃ w ≠ 0 := cross_ne_zero_symm hwv
  obtain ⟨m, hm⟩ := conic_line_lemma q (v ⨯₃ w) hvw (fun x hx => by
    obtain ⟨s, t, rfl⟩ := on_line hvw hvw (cross_dot_left _ _) (cross_dot_right _ _) hx
    rw [evalC_smul_add_smul, qv, qw, cmono1_sum_eq_gram h2, hv, dotProduct_zero]
    ring)
  exact ⟨_, m, hm⟩

/-- **Irreducibility criterion.** Over an algebraically closed field with `(2 : K) ≠ 0`,
a conic is a product of two linear forms iff its Gram matrix is singular. -/
theorem det_gram_eq_zero_iff [IsAlgClosed K] (h2 : (2 : K) ≠ 0) (q : Fin 6 → K) :
    (gram q).det = 0 ↔ ∃ ℓ m : Fin 3 → K, q = linMul ℓ m :=
  ⟨exists_linMul_of_det_gram_eq_zero h2 q, fun ⟨ℓ, m, hq⟩ => hq ▸ det_gram_linMul h2 ℓ m⟩

end PlaneCubic
