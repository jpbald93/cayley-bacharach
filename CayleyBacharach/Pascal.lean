import CayleyBacharach.ClassicalFinite

/-!
# Pascal and Pappus from Cayley–Bacharach

Hexagon `A₁ … A₆` on a conic `q`. The cubics
`F = L₁₂ · L₃₄ · L₅₆` and `G = L₂₃ · L₄₅ · L₆₁` (alternate sides, `Lᵢⱼ = Aᵢ ⨯₃ Aⱼ`)
meet in the six vertices and in `X = L₁₂ ∩ L₄₅`, `Y = L₂₃ ∩ L₅₆`, `Z = L₃₄ ∩ L₆₁`.
The cubic `H = L_{XY} · q` passes through eight of these nine points, so by
Cayley–Bacharach (`cayley_bacharach_classical`) it passes through `Z`; as `q(Z) ≠ 0`,
`Z` lies on the line `XY`.
-/

open Matrix

namespace PlaneCubic

variable {K : Type*} [Field K]

/-- Evaluation of a product of three linear forms. -/
theorem eval_mulLin_linMul (a b c v : Fin 3 → K) :
    eval (mulLin a (linMul b c)) v = (a ⬝ᵥ v) * ((b ⬝ᵥ v) * (c ⬝ᵥ v)) := by
  rw [eval_mulLin]
  exact congrArg _ (evalC_linMul b c v)

/-- Two vectors on two distinct lines `l, m` are proportional. -/
theorem cross_eq_zero_of_two_lines {l m v p : Fin 3 → K} (hlm : l ⨯₃ m ≠ 0)
    (lv : l ⬝ᵥ v = 0) (mv : m ⬝ᵥ v = 0) (lp : l ⬝ᵥ p = 0) (mp : m ⬝ᵥ p = 0) :
    v ⨯₃ p = 0 := by
  obtain ⟨c, hc⟩ := lin_two hlm (by rw [dotProduct_comm]; exact lv)
    (by rw [dotProduct_comm]; exact mv)
  obtain ⟨c', hc'⟩ := lin_two hlm (by rw [dotProduct_comm]; exact lp)
    (by rw [dotProduct_comm]; exact mp)
  rw [hc, hc']
  ext i; fin_cases i <;> simp [cross_apply] <;> ring

/-- **Pascal's theorem via Cayley–Bacharach.** Let `A₁, …, A₆` lie on a conic `q`, let
`X, Y, Z` be the intersections of opposite sides `A₁A₂ ∩ A₄A₅`, `A₂A₃ ∩ A₅A₆`,
`A₃A₄ ∩ A₆A₁` (side lines `Aᵢ ⨯₃ Aⱼ`). Genericity hypotheses:
* `hP`: the nine points are pairwise non-proportional;
* `hL`: each side of `F = L₁₂ L₃₄ L₅₆` is a different line from each side of
  `G = L₂₃ L₄₅ L₆₁` (so `F, G` meet in exactly the nine points);
* `hqZ`: `Z` is not on the conic.
Then `X, Y, Z` are collinear. No nondegeneracy of `q` is used (so Pappus is a special
case, `pappus_of_cayley_bacharach`). -/
theorem pascal_of_cayley_bacharach [CardGT K 10] (A₁ A₂ A₃ A₄ A₅ A₆ X Y Z : Fin 3 → K)
    (hP : ∀ i j, i ≠ j →
      ![A₁, A₂, A₃, A₄, A₅, A₆, X, Y, Z] i ⨯₃ ![A₁, A₂, A₃, A₄, A₅, A₆, X, Y, Z] j ≠ 0)
    (hL : ∀ i j : Fin 3,
      ![A₁ ⨯₃ A₂, A₃ ⨯₃ A₄, A₅ ⨯₃ A₆] i ⨯₃ ![A₂ ⨯₃ A₃, A₄ ⨯₃ A₅, A₆ ⨯₃ A₁] j ≠ 0)
    (hX₁ : A₁ ⨯₃ A₂ ⬝ᵥ X = 0) (hX₂ : A₄ ⨯₃ A₅ ⬝ᵥ X = 0)
    (hY₁ : A₂ ⨯₃ A₃ ⬝ᵥ Y = 0) (hY₂ : A₅ ⨯₃ A₆ ⬝ᵥ Y = 0)
    (hZ₁ : A₃ ⨯₃ A₄ ⬝ᵥ Z = 0) (hZ₂ : A₆ ⨯₃ A₁ ⬝ᵥ Z = 0)
    (q : Fin 6 → K) (hq₁ : evalC q A₁ = 0) (hq₂ : evalC q A₂ = 0) (hq₃ : evalC q A₃ = 0)
    (hq₄ : evalC q A₄ = 0) (hq₅ : evalC q A₅ = 0) (hq₆ : evalC q A₆ = 0)
    (hqZ : evalC q Z ≠ 0) :
    Matrix.det ![X, Y, Z] = 0 := by
  set P : Fin 9 → Fin 3 → K := ![A₁, A₂, A₃, A₄, A₅, A₆, X, Y, Z] with hPdef
  set F : PlaneCubic K := mulLin (A₁ ⨯₃ A₂) (linMul (A₃ ⨯₃ A₄) (A₅ ⨯₃ A₆)) with hFdef
  set G : PlaneCubic K := mulLin (A₂ ⨯₃ A₃) (linMul (A₄ ⨯₃ A₅) (A₆ ⨯₃ A₁)) with hGdef
  have hFe : ∀ v, eval F v = (A₁ ⨯₃ A₂ ⬝ᵥ v) * ((A₃ ⨯₃ A₄ ⬝ᵥ v) * (A₅ ⨯₃ A₆ ⬝ᵥ v)) :=
    fun v => eval_mulLin_linMul _ _ _ v
  have hGe : ∀ v, eval G v = (A₂ ⨯₃ A₃ ⬝ᵥ v) * ((A₄ ⨯₃ A₅ ⬝ᵥ v) * (A₆ ⨯₃ A₁ ⬝ᵥ v)) :=
    fun v => eval_mulLin_linMul _ _ _ v
  have hP0 : ∀ i, P i ≠ 0 := ne_zero_of_pairwise (n := 7) hP
  -- every common zero of `F, G` is one of the nine points
  have hZ : ∀ v, v ≠ 0 → eval F v = 0 → eval G v = 0 → ∃ i, v ⨯₃ P i = 0 := by
    intro v _ hF hG
    rw [hFe] at hF
    rw [hGe] at hG
    have l11 : A₁ ⨯₃ A₂ ⨯₃ (A₂ ⨯₃ A₃) ≠ 0 := hL 0 0
    have l12 : A₁ ⨯₃ A₂ ⨯₃ (A₄ ⨯₃ A₅) ≠ 0 := hL 0 1
    have l13 : A₁ ⨯₃ A₂ ⨯₃ (A₆ ⨯₃ A₁) ≠ 0 := hL 0 2
    have l21 : A₃ ⨯₃ A₄ ⨯₃ (A₂ ⨯₃ A₃) ≠ 0 := hL 1 0
    have l22 : A₃ ⨯₃ A₄ ⨯₃ (A₄ ⨯₃ A₅) ≠ 0 := hL 1 1
    have l23 : A₃ ⨯₃ A₄ ⨯₃ (A₆ ⨯₃ A₁) ≠ 0 := hL 1 2
    have l31 : A₅ ⨯₃ A₆ ⨯₃ (A₂ ⨯₃ A₃) ≠ 0 := hL 2 0
    have l32 : A₅ ⨯₃ A₆ ⨯₃ (A₄ ⨯₃ A₅) ≠ 0 := hL 2 1
    have l33 : A₅ ⨯₃ A₆ ⨯₃ (A₆ ⨯₃ A₁) ≠ 0 := hL 2 2
    rcases mul_eq_zero.mp hF with f1 | hF'
    · rcases mul_eq_zero.mp hG with g1 | hG'
      · exact ⟨1, cross_eq_zero_of_two_lines l11 f1 g1 (cross_dot_right _ _)
          (cross_dot_left _ _)⟩
      rcases mul_eq_zero.mp hG' with g2 | g3
      · exact ⟨6, cross_eq_zero_of_two_lines l12 f1 g2 hX₁ hX₂⟩
      · exact ⟨0, cross_eq_zero_of_two_lines l13 f1 g3 (cross_dot_left _ _)
          (cross_dot_right _ _)⟩
    rcases mul_eq_zero.mp hF' with f2 | f3
    · rcases mul_eq_zero.mp hG with g1 | hG'
      · exact ⟨2, cross_eq_zero_of_two_lines l21 f2 g1 (cross_dot_left _ _)
          (cross_dot_right _ _)⟩
      rcases mul_eq_zero.mp hG' with g2 | g3
      · exact ⟨3, cross_eq_zero_of_two_lines l22 f2 g2 (cross_dot_right _ _)
          (cross_dot_left _ _)⟩
      · exact ⟨8, cross_eq_zero_of_two_lines l23 f2 g3 hZ₁ hZ₂⟩
    · rcases mul_eq_zero.mp hG with g1 | hG'
      · exact ⟨7, cross_eq_zero_of_two_lines l31 f3 g1 hY₂ hY₁⟩
      rcases mul_eq_zero.mp hG' with g2 | g3
      · exact ⟨4, cross_eq_zero_of_two_lines l32 f3 g2 (cross_dot_left _ _)
          (cross_dot_right _ _)⟩
      · exact ⟨5, cross_eq_zero_of_two_lines l33 f3 g3 (cross_dot_right _ _)
          (cross_dot_left _ _)⟩
  -- the nine points are common zeros
  have hPZ : ∀ i, CommonZero F G (P i) := by
    intro i
    refine ⟨hP0 i, ?_, ?_⟩
    · rw [hFe]
      fin_cases i <;> simp [P, cross_dot_left, cross_dot_right, hX₁, hY₂, hZ₁]
    · rw [hGe]
      fin_cases i <;> simp [P, cross_dot_left, cross_dot_right, hX₂, hY₁, hZ₂]
  -- `F, G` are linearly independent: otherwise a whole side line consists of common zeros
  have hFG : LinearIndependent K ![F, G] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have key : ∀ v, s * eval F v + t * eval G v = 0 := fun v => by
      rw [← eval_smul, ← eval_smul, ← eval_add, hst, eval_zero]
    by_cases hs : s = 0
    · refine ⟨hs, ?_⟩
      by_contra ht
      refine false_of_line' hP0 (A₁ ⨯₃ A₂) fun v hv hl => hZ v hv ?_ ?_
      · rw [hFe, hl, zero_mul]
      · have := key v
        rw [hs, zero_mul, zero_add] at this
        exact (mul_eq_zero.mp this).resolve_left ht
    · exfalso
      refine false_of_line' hP0 (A₂ ⨯₃ A₃) fun v hv hl => hZ v hv ?_ ?_
      · have := key v
        rw [hGe, hl, zero_mul, mul_zero, add_zero] at this
        exact (mul_eq_zero.mp this).resolve_left hs
      · rw [hGe, hl, zero_mul]
  -- the cubic `H = L_{XY} · q` through eight of the nine points
  set H : PlaneCubic K := mulLin (X ⨯₃ Y) q with hHdef
  have hq₁' : conicEval q A₁ = 0 := hq₁
  have hq₂' : conicEval q A₂ = 0 := hq₂
  have hq₃' : conicEval q A₃ = 0 := hq₃
  have hq₄' : conicEval q A₄ = 0 := hq₄
  have hq₅' : conicEval q A₅ = 0 := hq₅
  have hq₆' : conicEval q A₆ = 0 := hq₆
  have hH : ∀ i : Fin 8, eval H (P (Fin.castSucc i)) = 0 := by
    intro i
    rw [hHdef, eval_mulLin]
    fin_cases i <;> simp [P, hq₁', hq₂', hq₃', hq₄', hq₅', hq₆', cross_dot_left,
      cross_dot_right]
  have h9 := cayley_bacharach_classical' P hP F G hFG ⟨hPZ, fun v hv => hZ v hv.1 hv.2.1 hv.2.2⟩
    H hH
  rw [hHdef, eval_mulLin] at h9
  have h9' : X ⨯₃ Y ⬝ᵥ Z = 0 := (mul_eq_zero.mp h9).resolve_right hqZ
  rw [← triple_product_eq_det, ← triple_product_permutation, dotProduct_comm]
  exact h9'

/-- **Pascal for a conic that is not a line pair.** If `q` is not a product of two linear
forms, the hypothesis `evalC q Z ≠ 0` of `pascal_of_cayley_bacharach` is automatic:
otherwise `q` vanishes at the three non-proportional points `A₃, A₄, Z` of the line `L₃₄`
and so contains that line (`conic_three`). -/
theorem pascal_of_cayley_bacharach' [CardGT K 10] (A₁ A₂ A₃ A₄ A₅ A₆ X Y Z : Fin 3 → K)
    (hP : ∀ i j, i ≠ j →
      ![A₁, A₂, A₃, A₄, A₅, A₆, X, Y, Z] i ⨯₃ ![A₁, A₂, A₃, A₄, A₅, A₆, X, Y, Z] j ≠ 0)
    (hL : ∀ i j : Fin 3,
      ![A₁ ⨯₃ A₂, A₃ ⨯₃ A₄, A₅ ⨯₃ A₆] i ⨯₃ ![A₂ ⨯₃ A₃, A₄ ⨯₃ A₅, A₆ ⨯₃ A₁] j ≠ 0)
    (hX₁ : A₁ ⨯₃ A₂ ⬝ᵥ X = 0) (hX₂ : A₄ ⨯₃ A₅ ⬝ᵥ X = 0)
    (hY₁ : A₂ ⨯₃ A₃ ⬝ᵥ Y = 0) (hY₂ : A₅ ⨯₃ A₆ ⬝ᵥ Y = 0)
    (hZ₁ : A₃ ⨯₃ A₄ ⬝ᵥ Z = 0) (hZ₂ : A₆ ⨯₃ A₁ ⬝ᵥ Z = 0)
    (q : Fin 6 → K) (hirr : ∀ ℓ m : Fin 3 → K, q ≠ linMul ℓ m)
    (hq₁ : evalC q A₁ = 0) (hq₂ : evalC q A₂ = 0) (hq₃ : evalC q A₃ = 0)
    (hq₄ : evalC q A₄ = 0) (hq₅ : evalC q A₅ = 0) (hq₆ : evalC q A₆ = 0) :
    Matrix.det ![X, Y, Z] = 0 := by
  refine pascal_of_cayley_bacharach A₁ A₂ A₃ A₄ A₅ A₆ X Y Z hP hL hX₁ hX₂ hY₁ hY₂ hZ₁ hZ₂
    q hq₁ hq₂ hq₃ hq₄ hq₅ hq₆ fun hqZ => ?_
  have h34 : A₃ ⨯₃ A₄ ≠ 0 := hP 2 3 (by decide)
  have h3Z : A₃ ⨯₃ Z ≠ 0 := hP 2 8 (by decide)
  have h4Z : A₄ ⨯₃ Z ≠ 0 := hP 3 8 (by decide)
  obtain ⟨m, hm⟩ := conic_three h34 h34 h3Z h4Z (cross_dot_left _ _) (cross_dot_right _ _)
    hZ₁ hq₃ hq₄ hqZ
  exact hirr _ _ hm

/-- **Pappus's theorem via Cayley–Bacharach.** `A₁, A₃, A₅` on a line `l`, `A₂, A₄, A₆` on a
line `m`; `X, Y, Z` as in Pascal. This is Pascal for the degenerate conic `q = l · m`, with
`evalC q Z ≠ 0` becoming "`Z` is on neither line". -/
theorem pappus_of_cayley_bacharach [CardGT K 10] (A₁ A₂ A₃ A₄ A₅ A₆ X Y Z l m : Fin 3 → K)
    (hP : ∀ i j, i ≠ j →
      ![A₁, A₂, A₃, A₄, A₅, A₆, X, Y, Z] i ⨯₃ ![A₁, A₂, A₃, A₄, A₅, A₆, X, Y, Z] j ≠ 0)
    (hL : ∀ i j : Fin 3,
      ![A₁ ⨯₃ A₂, A₃ ⨯₃ A₄, A₅ ⨯₃ A₆] i ⨯₃ ![A₂ ⨯₃ A₃, A₄ ⨯₃ A₅, A₆ ⨯₃ A₁] j ≠ 0)
    (hX₁ : A₁ ⨯₃ A₂ ⬝ᵥ X = 0) (hX₂ : A₄ ⨯₃ A₅ ⬝ᵥ X = 0)
    (hY₁ : A₂ ⨯₃ A₃ ⬝ᵥ Y = 0) (hY₂ : A₅ ⨯₃ A₆ ⬝ᵥ Y = 0)
    (hZ₁ : A₃ ⨯₃ A₄ ⬝ᵥ Z = 0) (hZ₂ : A₆ ⨯₃ A₁ ⬝ᵥ Z = 0)
    (hl₁ : l ⬝ᵥ A₁ = 0) (hl₃ : l ⬝ᵥ A₃ = 0) (hl₅ : l ⬝ᵥ A₅ = 0)
    (hm₂ : m ⬝ᵥ A₂ = 0) (hm₄ : m ⬝ᵥ A₄ = 0) (hm₆ : m ⬝ᵥ A₆ = 0)
    (hlZ : l ⬝ᵥ Z ≠ 0) (hmZ : m ⬝ᵥ Z ≠ 0) :
    Matrix.det ![X, Y, Z] = 0 :=
  pascal_of_cayley_bacharach A₁ A₂ A₃ A₄ A₅ A₆ X Y Z hP hL hX₁ hX₂ hY₁ hY₂ hZ₁ hZ₂
    (linMul l m) (by rw [evalC_linMul, hl₁, zero_mul]) (by rw [evalC_linMul, hm₂, mul_zero])
    (by rw [evalC_linMul, hl₃, zero_mul]) (by rw [evalC_linMul, hm₄, mul_zero])
    (by rw [evalC_linMul, hl₅, zero_mul]) (by rw [evalC_linMul, hm₆, mul_zero])
    (by rw [evalC_linMul]; exact mul_ne_zero hlZ hmZ)

end PlaneCubic
