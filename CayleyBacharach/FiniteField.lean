import CayleyBacharach.Classical

/-!
# Finite fields: the sharp size hypotheses

* `AtLeastThree K` (Line.lean) is the sharp hypothesis for `line_lemma`
  (`line_lemma_false_zmod_two`); `conic_line_lemma` needs no hypothesis at all.
* A field without a third element has at most `8` vectors in `K³`, hence at most `7`
  pairwise non-proportional nonzero ones (`card_le_seven_of_not_atLeastThree`).
  So the criterion and Cayley–Bacharach, which involve `8` resp. `9` pairwise
  non-proportional points, are vacuous there, and hold over **every** field
  (`finrank_ker_evalMap_eq_two_any`, `cayley_bacharach_any`,
  `cayley_bacharach_of_no_common_factor_any`).
-/

open Matrix

namespace PlaneCubic

variable {K : Type*} [Field K]

theorem atLeastThree_iff_card [Fintype K] : AtLeastThree K ↔ 3 ≤ Fintype.card K := by
  classical
  refine ⟨fun h => ?_, AtLeastThree.of_card⟩
  obtain ⟨t, ht0, ht1⟩ := h.exists_ne
  have h3 : ({0, 1, t} : Finset K).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm ht1)]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨zero_ne_one, Ne.symm ht0⟩
  rw [← h3]
  exact Finset.card_le_univ _

/-- **Line lemma over a finite field**, with the sharp bound `3 ≤ |K|`. -/
theorem line_lemma_fintype [Fintype K] (hK : 3 ≤ Fintype.card K) (F : PlaneCubic K)
    (ℓ : Fin 3 → K) (hℓ : ℓ ≠ 0) (hF : ∀ v : Fin 3 → K, ℓ ⬝ᵥ v = 0 → eval F v = 0) :
    ∃ q : Fin 6 → K, F = mulLin ℓ q :=
  haveI := AtLeastThree.of_card hK
  line_lemma F ℓ hℓ hF

/-- Without a third element, every element is `0` or `1`. -/
theorem eq_zero_or_eq_one_of_not_atLeastThree (h : ¬ AtLeastThree K) (t : K) :
    t = 0 ∨ t = 1 := by
  by_contra ht
  push Not at ht
  exact h ⟨⟨t, ht.1, ht.2⟩⟩

theorem finite_of_not_atLeastThree (h : ¬ AtLeastThree K) : Finite K :=
  Finite.of_surjective (fun b : Bool => if b then (1 : K) else 0) fun t => by
    rcases eq_zero_or_eq_one_of_not_atLeastThree h t with rfl | rfl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩

/-- **At most seven points.** Over a field with no third element (i.e. `𝔽₂`), a family of
pairwise non-proportional vectors in `K³` has at most `7` members (`P²(𝔽₂)` has 7 points). -/
theorem card_le_seven_of_not_atLeastThree (h : ¬ AtLeastThree K) {n : ℕ}
    (P : Fin n → Fin 3 → K) (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0) : n ≤ 7 := by
  have := finite_of_not_atLeastThree h
  have hK : Nat.card K ≤ 2 := by
    have := Nat.card_le_card_of_surjective (fun b : Bool => if b then (1 : K) else 0)
      fun t => by
        rcases eq_zero_or_eq_one_of_not_atLeastThree h t with rfl | rfl
        · exact ⟨false, rfl⟩
        · exact ⟨true, rfl⟩
    simpa using this
  have hV : Nat.card (Fin 3 → K) ≤ 8 := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]
    calc Nat.card K ^ 3 ≤ 2 ^ 3 := Nat.pow_le_pow_left hK 3
      _ = 8 := by norm_num
  by_contra hn
  push Not at hn
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  let f : Option (Fin n) → Fin 3 → K := fun o => o.elim 0 P
  have hne : ∀ i, P i ≠ 0 := fun i h0 => by
    obtain ⟨j, hj⟩ := exists_ne i
    exact hP j i hj (by rw [h0]; simp)
  have hf : Function.Injective f := by
    rintro (_ | i) (_ | j) hij
    · rfl
    · exact absurd hij.symm (hne j)
    · exact absurd hij (hne i)
    · by_contra hne'
      have hij' : i ≠ j := fun e => hne' (congrArg some e)
      apply hP i j hij'
      simp only [f, Option.elim] at hij
      rw [hij, cross_self]
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card (α := Option (Fin n)), Fintype.card_option, Fintype.card_fin]
    at this
  omega

/-- **The criterion over every field.** No size hypothesis: for `|K| = 2` it is vacuous. -/
theorem finrank_ker_evalMap_eq_two_any (P : Fin 8 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0)
    (h5 : ∀ ℓ : Fin 3 → K, ℓ ≠ 0 → ∀ s : Finset (Fin 8), (∀ i ∈ s, ℓ ⬝ᵥ P i = 0) →
      s.card ≤ 4)
    (hconic : ∀ q : Fin 6 → K, (∀ i, evalC q (P i) = 0) → q = 0) :
    Module.finrank K (LinearMap.ker (evalMap P)) = 2 := by
  by_cases hK : AtLeastThree K
  · exact finrank_ker_evalMap_eq_two P hP h5 hconic
  · exact absurd (card_le_seven_of_not_atLeastThree hK P hP) (by norm_num)

/-- **Cayley–Bacharach over every field** (general-position form), finite fields included. -/
theorem cayley_bacharach_any (P : Fin 9 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0)
    (h5 : ∀ ℓ : Fin 3 → K, ℓ ≠ 0 → ∀ s : Finset (Fin 8),
      (∀ i ∈ s, ℓ ⬝ᵥ P (Fin.castSucc i) = 0) → s.card ≤ 4)
    (hconic : ∀ q : Fin 6 → K, (∀ i : Fin 8, evalC q (P (Fin.castSucc i)) = 0) → q = 0)
    (F G : PlaneCubic K) (hFG : LinearIndependent K ![F, G])
    (hF : ∀ i, eval F (P i) = 0) (hG : ∀ i, eval G (P i) = 0)
    (H : PlaneCubic K) (hH : ∀ i : Fin 8, eval H (P (Fin.castSucc i)) = 0) :
    eval H (P 8) = 0 := by
  by_cases hK : AtLeastThree K
  · exact cayley_bacharach P hP h5 hconic F G hFG hF hG H hH
  · exact absurd (card_le_seven_of_not_atLeastThree hK P hP) (by norm_num)

/-- **Cayley–Bacharach, no-common-factor form, over every field.** -/
theorem cayley_bacharach_of_no_common_factor_any (P : Fin 9 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0)
    (F G : PlaneCubic K) (hFG : LinearIndependent K ![F, G])
    (hF : ∀ i, eval F (P i) = 0) (hG : ∀ i, eval G (P i) = 0)
    (hlin : ¬ ∃ ℓ q q', ℓ ≠ 0 ∧ F = mulLin ℓ q ∧ G = mulLin ℓ q')
    (hcon : ¬ ∃ q m m', q ≠ 0 ∧ F = mulLin m q ∧ G = mulLin m' q)
    (H : PlaneCubic K) (hH : ∀ i : Fin 8, eval H (P (Fin.castSucc i)) = 0) :
    eval H (P 8) = 0 := by
  by_cases hK : AtLeastThree K
  · exact cayley_bacharach_of_no_common_factor P hP F G hFG hF hG hlin hcon H hH
  · exact absurd (card_le_seven_of_not_atLeastThree hK P hP) (by norm_num)

end PlaneCubic
