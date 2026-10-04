import CayleyBacharach.FiniteField
import CayleyBacharach.Criterion

/-!
# The eight-point criterion, as a single `iff`

* `finrank_ker_evalMap_eq_two_iff`: for eight pairwise non-proportional points `P`, the
  cubics through them form a space of dimension exactly `2` **iff** the two general-position
  hypotheses hold: no line carries five of the points, and no nonzero conic passes through
  all eight. The forward direction is the two easy directions
  (`finrank_ker_ge_of_line`, `finrank_ker_ge_of_conic`); the converse is the criterion
  (`finrank_ker_evalMap_eq_two_any`), which needs no `AtLeastThree` hypothesis.
-/

open Matrix

namespace PlaneCubic

variable {K : Type*} [Field K]

private theorem card_compl_fin8 (s : Finset (Fin 8)) :
    Fintype.card {i : Fin 8 // i ∉ s} = 8 - s.card := by
  rw [Fintype.card_subtype_compl (fun i => i ∈ s), Fintype.card_fin]
  congr 1
  exact Finset.card_attach

/-- **The eight-point criterion, as an equivalence.** For eight pairwise non-proportional
points in the plane, the space of cubics through them is `2`-dimensional if and only if no
line contains five of the points and no nonzero conic passes through all eight. -/
theorem finrank_ker_evalMap_eq_two_iff (P : Fin 8 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0) :
    Module.finrank K (LinearMap.ker (evalMap P)) = 2 ↔
      (∀ ℓ : Fin 3 → K, ℓ ≠ 0 → ∀ s : Finset (Fin 8), (∀ i ∈ s, ℓ ⬝ᵥ P i = 0) →
        s.card ≤ 4) ∧
      (∀ q : Fin 6 → K, (∀ i, evalC q (P i) = 0) → q = 0) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro ℓ hℓ s hs
      by_contra hc
      push Not at hc
      have hcard : Fintype.card {i : Fin 8 // i ∉ s} ≤ 3 := by
        rw [card_compl_fin8]; omega
      have hge := finrank_ker_ge_of_line P ℓ hℓ s hs hcard
      omega
    · intro q hq
      by_contra hq0
      have hge := finrank_ker_ge_of_conic P q hq0 hq
      omega
  · rintro ⟨h5, hconic⟩
    exact finrank_ker_evalMap_eq_two_any P hP h5 hconic

end PlaneCubic
