import CayleyBacharach.FiniteField

/-!
# The classical form over finite fields

`Classical.lean` uses `[Infinite K]` to show that a common line or conic component gives
more common zeros than nine. Here the same arguments are done by counting: it suffices
that `K` has more than `10` elements (`∃ s : Finset K, 10 < s.card`). This covers every
infinite field and every finite field with `|K| ≥ 11`.

Over `𝔽₄, 𝔽₅, 𝔽₇` the classical form is **false** (explicit counterexamples in
`code/stage9/`, e.g. over `𝔽₅`: `F = z·(x+2y+3z)(x+2z)`, `G = z·(x+3y+2z)(x+y)`).
-/

open Matrix

namespace PlaneCubic

variable {K : Type*} [Field K]

/-- `K` has more than `n` elements. Automatic for infinite `K`; for finite `K` it is
`n < Fintype.card K` (`CardGT.of_card`). -/
class CardGT (K : Type*) (n : ℕ) : Prop where
  exists_finset : ∃ s : Finset K, n < s.card

instance (priority := 100) CardGT.of_infinite [Infinite K] {n : ℕ} : CardGT K n :=
  ⟨by
    obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq K (n + 1)
    exact ⟨s, by omega⟩⟩

theorem CardGT.of_card {L : Type*} [Fintype L] {n : ℕ} (h : n < Fintype.card L) :
    CardGT L n :=
  ⟨⟨Finset.univ, by rw [Finset.card_univ]; exact h⟩⟩

/-- A field with a `3`-element finset has at least three elements. -/
theorem AtLeastThree.of_finset (s : Finset K) (h : 3 ≤ s.card) : AtLeastThree K := by
  classical
  by_contra hK
  have hsub : s ⊆ {0, 1} := fun t _ => by
    rcases eq_zero_or_eq_one_of_not_atLeastThree hK t with rfl | rfl <;> simp
  have := (Finset.card_le_card hsub).trans Finset.card_le_two
  omega

/-- **Pigeonhole, finite version.** More pairwise non-proportional zeros than classes. -/
theorem false_of_finset_family {ι : Type*} [Fintype ι] {P : ι → Fin 3 → K}
    (hP : ∀ i, P i ≠ 0) {Z : (Fin 3 → K) → Prop}
    (hZ : ∀ v, v ≠ 0 → Z v → ∃ i, v ⨯₃ P i = 0) (S : Finset K)
    (hS : Fintype.card ι < S.card)
    (g : K → Fin 3 → K) (hg0 : ∀ t ∈ S, g t ≠ 0) (hgZ : ∀ t ∈ S, Z (g t))
    (hg : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → g s ⨯₃ g t ≠ 0) : False := by
  choose f hf using fun t : S => hZ _ (hg0 t t.2) (hgZ t t.2)
  obtain ⟨s, t, hst, he⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simpa using hS)
  have h1 := hf s
  have h2 := hf t
  rw [he] at h1
  exact hg s s.2 t t.2 (fun h => hst (Subtype.ext h))
    (cross_eq_zero_of_cross_eq_zero (hP _) h1 h2)

theorem false_of_pencil_card {ι : Type*} [Fintype ι] {P : ι → Fin 3 → K}
    (hP : ∀ i, P i ≠ 0) {Z : (Fin 3 → K) → Prop}
    (hZ : ∀ v, v ≠ 0 → Z v → ∃ i, v ⨯₃ P i = 0)
    (hK : ∃ s : Finset K, Fintype.card ι < s.card) {u w : Fin 3 → K} (huw : u ⨯₃ w ≠ 0)
    (hZuw : ∀ t : K, Z (u + t • w)) : False := by
  obtain ⟨S, hS⟩ := hK
  exact false_of_finset_family hP hZ S hS (fun t => u + t • w)
    (fun t _ => ne_zero_of_cross (u := w) (by rw [cross_add_smul']; exact neg_ne_zero.mpr huw))
    (fun t _ => hZuw t)
    (fun s _ t _ hst => by
      rw [cross_add_smul]; exact smul_ne_zero (sub_ne_zero.mpr (Ne.symm hst)) huw)

theorem false_of_line_card {ι : Type*} [Fintype ι] {P : ι → Fin 3 → K}
    (hP : ∀ i, P i ≠ 0) (hK : ∃ s : Finset K, Fintype.card ι < s.card) (ℓ : Fin 3 → K)
    (hZ : ∀ v, v ≠ 0 → ℓ ⬝ᵥ v = 0 → ∃ i, v ⨯₃ P i = 0) : False := by
  obtain ⟨u, w, hu, hw, huw⟩ := exists_line_basis ℓ
  exact false_of_pencil_card hP hZ hK huw fun t => by
    simp [dotProduct_add, dotProduct_smul, hu, hw]

theorem no_common_line_of_exact_card {ι : Type*} [Fintype ι] {P : ι → Fin 3 → K}
    (hP : ∀ i, P i ≠ 0) (hK : ∃ s : Finset K, Fintype.card ι < s.card) (F G : PlaneCubic K)
    (hex : ∀ v, v ≠ 0 → eval F v = 0 → eval G v = 0 → ∃ i, v ⨯₃ P i = 0) :
    ¬ ∃ ℓ q q', ℓ ≠ 0 ∧ F = mulLin ℓ q ∧ G = mulLin ℓ q' := by
  rintro ⟨ℓ, q, q', hℓ, rfl, rfl⟩
  exact false_of_line_card hP hK ℓ fun v hv hl =>
    hex v hv (eval_mulLin_of_dot_eq_zero _ _ _ hl) (eval_mulLin_of_dot_eq_zero _ _ _ hl)

/-- A conic with two distinct zeros has at least `|K| - 1` pairwise non-proportional zeros. -/
theorem false_of_conic_card {ι : Type*} [Fintype ι] {P : ι → Fin 3 → K}
    (hP : ∀ i, P i ≠ 0) (hK : ∃ s : Finset K, Fintype.card ι + 1 < s.card)
    {q : Fin 6 → K} {u v : Fin 3 → K} (huv : u ⨯₃ v ≠ 0)
    (hu : evalC q u = 0) (hv : evalC q v = 0)
    (hZ : ∀ w, w ≠ 0 → evalC q w = 0 → ∃ i, w ⨯₃ P i = 0) : False := by
  classical
  obtain ⟨T, hT⟩ := hK
  by_cases hB : polarC q u v = 0
  · refine false_of_pencil_card hP hZ ⟨T, by omega⟩ huv fun t => ?_
    have := evalC_smul_add_smul' q u v 1 t
    rw [one_smul] at this
    rw [this, hu, hv, hB]; ring
  obtain ⟨z, hz⟩ := exists_off_line huv
  have hS : Fintype.card ι < (T.filter fun t => polarC q u v + t * polarC q u z ≠ 0).card := by
    have h1 := Finset.card_filter_add_card_filter_not (s := T)
      (fun t => polarC q u v + t * polarC q u z ≠ 0)
    have h2 : (T.filter fun t => ¬ (polarC q u v + t * polarC q u z ≠ 0)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      simp only [Finset.mem_filter, not_not] at ha hb
      by_cases hz0 : polarC q u z = 0
      · rw [hz0, mul_zero, add_zero] at ha; exact absurd ha.2 hB
      · have : (a - b) * polarC q u z = 0 := by linear_combination ha.2 - hb.2
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hz0)
    omega
  refine false_of_finset_family hP hZ _ hS
    (fun t => evalC q (v + t • z) • u + (-polarC q u (v + t • z)) • (v + t • z))
    (fun t ht => ?_) (fun t _ => ?_) (fun s hs t ht hst => ?_)
  · have ht' := (Finset.mem_filter.mp ht).2
    intro h0
    have := proj_cross_dot' u v z (evalC q (v + t • z)) (-polarC q u (v + t • z)) t
    rw [h0, polarC_add_smul] at this
    simp only [map_zero, zero_dotProduct] at this
    exact mul_ne_zero (neg_ne_zero.mpr ht') hz this.symm
  · show evalC q (_ • u + _ • _) = 0
    rw [evalC_smul_add_smul', hu]; ring
  · have hs' := (Finset.mem_filter.mp hs).2
    have ht' := (Finset.mem_filter.mp ht).2
    intro h0
    have := proj_cross_dot u v z (evalC q (v + s • z)) (-polarC q u (v + s • z))
      (evalC q (v + t • z)) (-polarC q u (v + t • z)) t s
    rw [h0, zero_dotProduct, polarC_add_smul, polarC_add_smul] at this
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hs') (neg_ne_zero.mpr ht'))
      (sub_ne_zero.mpr (Ne.symm hst))) hz this.symm

theorem false_of_common_pair_card {ι : Type*} [Fintype ι] {P : ι → Fin 3 → K}
    (hP : ∀ i, P i ≠ 0) (hK : ∃ s : Finset K, Fintype.card ι < s.card)
    {q : Fin 6 → K} {m m' a b : Fin 3 → K} (hab : a ⨯₃ b ≠ 0)
    (ma : m ⬝ᵥ a = 0) (mb : m ⬝ᵥ b = 0) (m'a : m' ⬝ᵥ a = 0) (m'b : m' ⬝ᵥ b = 0)
    (hex : ∀ v, v ≠ 0 → eval (mulLin m q) v = 0 → eval (mulLin m' q) v = 0 →
      ∃ i, v ⨯₃ P i = 0) : False := by
  obtain ⟨c, hc⟩ := lin_two hab ma mb
  obtain ⟨c', hc'⟩ := lin_two hab m'a m'b
  refine false_of_line_card hP hK (a ⨯₃ b) fun v hv hl => hex v hv ?_ ?_
  · rw [eval_mulLin, hc, smul_dotProduct, hl, smul_zero, zero_mul]
  · rw [eval_mulLin, hc', smul_dotProduct, hl, smul_zero, zero_mul]

theorem no_common_conic_of_exact_card {n : ℕ} {P : Fin (n + 3) → Fin 3 → K}
    (hK : ∃ s : Finset K, n + 4 < s.card)
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0) (F G : PlaneCubic K)
    (hF : ∀ i, eval F (P i) = 0) (hG : ∀ i, eval G (P i) = 0)
    (hex : ∀ v, v ≠ 0 → eval F v = 0 → eval G v = 0 → ∃ i, v ⨯₃ P i = 0) :
    ¬ ∃ q m m', q ≠ 0 ∧ F = mulLin m q ∧ G = mulLin m' q := by
  rintro ⟨q, m, m', -, rfl, rfl⟩
  obtain ⟨T, hT⟩ := hK
  have hK1 : ∃ s : Finset K, Fintype.card (Fin (n + 3)) + 1 < s.card :=
    ⟨T, by rw [Fintype.card_fin]; omega⟩
  have hK0 : ∃ s : Finset K, Fintype.card (Fin (n + 3)) < s.card :=
    ⟨T, by rw [Fintype.card_fin]; omega⟩
  have hP0 : ∀ i, P i ≠ 0 := ne_zero_of_pairwise (n := n + 1) hP
  have hZq : ∀ w, w ≠ 0 → evalC q w = 0 → ∃ i, w ⨯₃ P i = 0 := fun w hw h =>
    hex w hw (by rw [eval_mulLin, show conicEval q w = 0 from h, mul_zero])
      (by rw [eval_mulLin, show conicEval q w = 0 from h, mul_zero])
  have hq2 : ∀ i j, i ≠ j → evalC q (P i) = 0 → evalC q (P j) = 0 → False :=
    fun i j hij hi hj => false_of_conic_card hP0 hK1 (hP i j hij) hi hj hZq
  have hmm : ∀ i, evalC q (P i) ≠ 0 → m ⬝ᵥ P i = 0 ∧ m' ⬝ᵥ P i = 0 := fun i hi => by
    have h1 := hF i
    have h2 := hG i
    rw [eval_mulLin] at h1 h2
    exact ⟨(mul_eq_zero.mp h1).resolve_right hi, (mul_eq_zero.mp h2).resolve_right hi⟩
  have key : ∀ a b, a ≠ b → evalC q (P a) ≠ 0 → evalC q (P b) ≠ 0 → False :=
    fun a b hab ha hb => false_of_common_pair_card hP0 hK0 (hP a b hab) (hmm a ha).1
      (hmm b hb).1 (hmm a ha).2 (hmm b hb).2 hex
  have d01 : (0 : Fin (n + 3)) ≠ 1 := by simp
  have d02 : (0 : Fin (n + 3)) ≠ 2 := by
    simp [Fin.ext_iff, Nat.mod_eq_of_lt (show 2 < n + 3 by omega)]
  have d12 : (1 : Fin (n + 3)) ≠ 2 := by
    simp [Fin.ext_iff, Nat.mod_eq_of_lt (show 2 < n + 3 by omega)]
  by_cases h0 : evalC q (P 0) = 0
  · exact key 1 2 d12 (fun h => hq2 0 1 d01 h0 h) (fun h => hq2 0 2 d02 h0 h)
  · by_cases h1 : evalC q (P 1) = 0
    · exact key 0 2 d02 h0 (fun h => hq2 1 2 d12 h1 h)
    · exact key 0 1 d01 h0 h1

/-- **Cayley–Bacharach, classical form, counting version.** As `cayley_bacharach_classical`,
with `[Infinite K]` replaced by "`K` has at least `11` elements". -/
theorem cayley_bacharach_classical_card (hK : ∃ s : Finset K, 10 < s.card)
    (P : Fin 9 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0)
    (F G : PlaneCubic K) (hFG : LinearIndependent K ![F, G])
    (hex : ExactlyMeetIn F G P)
    (H : PlaneCubic K) (hH : ∀ i : Fin 8, eval H (P (Fin.castSucc i)) = 0) :
    eval H (P 8) = 0 := by
  obtain ⟨T, hT⟩ := hK
  have : AtLeastThree K := AtLeastThree.of_finset T (by omega)
  obtain ⟨hPZ, hZ⟩ := hex
  have hF : ∀ i, eval F (P i) = 0 := fun i => (hPZ i).2.1
  have hG : ∀ i, eval G (P i) = 0 := fun i => (hPZ i).2.2
  have hex' : ∀ v, v ≠ 0 → eval F v = 0 → eval G v = 0 → ∃ i, v ⨯₃ P i = 0 :=
    fun v hv h1 h2 => hZ v ⟨hv, h1, h2⟩
  exact cayley_bacharach_of_no_common_factor P hP F G hFG hF hG
    (no_common_line_of_exact_card (fun i => (hPZ i).1) ⟨T, by rw [Fintype.card_fin]; omega⟩
      F G hex')
    (no_common_conic_of_exact_card (n := 6) ⟨T, by omega⟩ hP F G hF hG hex') H hH

/-- **Classical Cayley–Bacharach over a finite field with at least 11 elements.** -/
theorem cayley_bacharach_classical_fintype [Fintype K] (hK : 11 ≤ Fintype.card K)
    (P : Fin 9 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0)
    (F G : PlaneCubic K) (hFG : LinearIndependent K ![F, G])
    (hex : ExactlyMeetIn F G P)
    (H : PlaneCubic K) (hH : ∀ i : Fin 8, eval H (P (Fin.castSucc i)) = 0) :
    eval H (P 8) = 0 :=
  cayley_bacharach_classical_card ⟨Finset.univ, by rw [Finset.card_univ]; omega⟩
    P hP F G hFG hex H hH

/-- **Classical Cayley–Bacharach under `CardGT K 10`** (typeclass form, used by
`Pascal.lean`; `[Infinite K]` provides the instance). -/
theorem cayley_bacharach_classical' [CardGT K 10] (P : Fin 9 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0)
    (F G : PlaneCubic K) (hFG : LinearIndependent K ![F, G])
    (hex : ExactlyMeetIn F G P)
    (H : PlaneCubic K) (hH : ∀ i : Fin 8, eval H (P (Fin.castSucc i)) = 0) :
    eval H (P 8) = 0 :=
  cayley_bacharach_classical_card CardGT.exists_finset P hP F G hFG hex H hH

/-- `false_of_line` under `CardGT K 10`, for nine classes. -/
theorem false_of_line' [CardGT K 10] {P : Fin 9 → Fin 3 → K}
    (hP : ∀ i, P i ≠ 0) (ℓ : Fin 3 → K)
    (hZ : ∀ v, v ≠ 0 → ℓ ⬝ᵥ v = 0 → ∃ i, v ⨯₃ P i = 0) : False := by
  obtain ⟨T, hT⟩ := CardGT.exists_finset (K := K) (n := 10)
  exact false_of_line_card hP ⟨T, by rw [Fintype.card_fin]; omega⟩ ℓ hZ

end PlaneCubic
