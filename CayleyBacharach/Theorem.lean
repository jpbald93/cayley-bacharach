import CayleyBacharach.General

/-!
# The Cayley–Bacharach theorem (general-position form)

Let `P 0, …, P 8` be nine pairwise non-proportional points and let `F, G` be linearly
independent cubics through all nine. If the first eight points have no five on a line and
do not all lie on a nonzero conic, then every cubic through `P 0, …, P 7` lies in the span
of `F, G`, and hence also passes through `P 8`.
-/

open Matrix

namespace PlaneCubic

variable {K : Type*} [Field K]

/-- Every cubic through the first eight points is a combination of `F` and `G`. -/
theorem mem_span_of_eight [AtLeastThree K] (P : Fin 9 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0)
    (h5 : ∀ ℓ : Fin 3 → K, ℓ ≠ 0 → ∀ s : Finset (Fin 8),
      (∀ i ∈ s, ℓ ⬝ᵥ P (Fin.castSucc i) = 0) → s.card ≤ 4)
    (hconic : ∀ q : Fin 6 → K, (∀ i : Fin 8, evalC q (P (Fin.castSucc i)) = 0) → q = 0)
    (F G : PlaneCubic K) (hFG : LinearIndependent K ![F, G])
    (hF : ∀ i, eval F (P i) = 0) (hG : ∀ i, eval G (P i) = 0)
    (H : PlaneCubic K) (hH : ∀ i : Fin 8, eval H (P (Fin.castSucc i)) = 0) :
    H ∈ Submodule.span K (Set.range ![F, G]) := by
  set P' : Fin 8 → Fin 3 → K := fun i => P (Fin.castSucc i)
  have hP' : ∀ i j, i ≠ j → P' i ⨯₃ P' j ≠ 0 := fun i j hij =>
    hP _ _ (fun h => hij (Fin.castSucc_injective _ h))
  have hle : Submodule.span K (Set.range ![F, G]) ≤ cubicsThrough (Set.range P') := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩ _ ⟨i, rfl⟩
    fin_cases k
    · exact hF _
    · exact hG _
  have h2 : Module.finrank K (Submodule.span K (Set.range ![F, G])) = 2 := by
    rw [finrank_span_eq_card hFG]; simp
  have heq : Submodule.span K (Set.range ![F, G]) = cubicsThrough (Set.range P') :=
    Submodule.eq_of_le_of_finrank_le hle
      (by rw [h2]; exact finrank_cubicsThrough_le_two P' hP' h5 hconic)
  rw [heq]
  rintro _ ⟨i, rfl⟩
  exact hH i

/-- **Cayley–Bacharach.** A cubic through eight of the nine base points of a pencil
`⟨F, G⟩` (with the eight in general position) passes through the ninth. -/
theorem cayley_bacharach [AtLeastThree K] (P : Fin 9 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0)
    (h5 : ∀ ℓ : Fin 3 → K, ℓ ≠ 0 → ∀ s : Finset (Fin 8),
      (∀ i ∈ s, ℓ ⬝ᵥ P (Fin.castSucc i) = 0) → s.card ≤ 4)
    (hconic : ∀ q : Fin 6 → K, (∀ i : Fin 8, evalC q (P (Fin.castSucc i)) = 0) → q = 0)
    (F G : PlaneCubic K) (hFG : LinearIndependent K ![F, G])
    (hF : ∀ i, eval F (P i) = 0) (hG : ∀ i, eval G (P i) = 0)
    (H : PlaneCubic K) (hH : ∀ i : Fin 8, eval H (P (Fin.castSucc i)) = 0) :
    eval H (P 8) = 0 := by
  have hmem := mem_span_of_eight P hP h5 hconic F G hFG hF hG H hH
  have hle : Submodule.span K (Set.range ![F, G]) ≤ cubicsThrough {P 8} := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩ v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    fin_cases k
    · exact hF _
    · exact hG _
  exact hle hmem (P 8) rfl

end PlaneCubic
