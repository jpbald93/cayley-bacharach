import CayleyBacharach.ClassicalSmall

/-!
# The classical form over `𝔽₃`

`ClassicalSmall.lean` proves the classical ("exactly nine common zeros") form of
Cayley–Bacharach for finite fields with `|K| ≥ 8`; it is false over `𝔽₄, 𝔽₅, 𝔽₇` and vacuous
over `𝔽₂` (the plane `ℙ²(𝔽₂)` has only seven points). Here we close the remaining case `𝔽₃`.

Over a field with three elements, two linearly independent cubics with nine pairwise
non-proportional common zeros never have a common component:

* **common line `ℓ`** (`no_common_line_card3`): at most `|K| + 1 = 4` of the nine points lie
  on `ℓ` (`card_le_of_line`), so at least five lie off `ℓ` and are common zeros of the two
  residual conics. No four of these five are collinear: a line `m` through four of them also
  contains `ℓ ∩ m`, which would give five points on `m` (`card_le_of_line_off`). Five points
  with no four collinear lie on at most a pencil of dimension one (`conics_le_one`), so the
  residual conics are proportional, and then so are the cubics.
* **common conic `q` without line component** (`no_common_conic_card3`): at most one of the
  nine points is off `q` (two of them would give a common line), so `q` has eight pairwise
  non-proportional zeros; but projecting from one zero, the other zeros lie on distinct lines
  through it (three collinear zeros force a line component), so `q` has at most
  `|K| + 2 = 5` zeros (`card_le_of_conic`).

Hence the no-common-factor form `cayley_bacharach_of_no_common_factor` applies. Only the
nine points being common zeros is used, not that they are *all* the common zeros
(`cayley_bacharach_card3`). Combined with `cayley_bacharach_classical_card8`, the classical
form holds over every finite field with `|K| ∉ {4, 5, 7}`
(`cayley_bacharach_classical_finite`).
-/

open Matrix

namespace PlaneCubic

variable {K : Type*} [Field K]

/-! ### Upper bounds for points on lines and conics -/

/-- **At most `|K| + 1` points on a line.** -/
theorem card_le_of_line [Fintype K] {ι : Type*} [Fintype ι] {P : ι → Fin 3 → K}
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0) {ℓ : Fin 3 → K} (hℓ : ℓ ≠ 0)
    (hl : ∀ i, ℓ ⬝ᵥ P i = 0) : Fintype.card ι ≤ Fintype.card K + 1 := by
  classical
  obtain ⟨u, w, hu, hw, huw⟩ := exists_line_basis ℓ
  choose s t hst using fun i => on_line hℓ huw hu hw (hl i)
  have hf : Function.Injective
      (fun i => if s i = 0 then (none : Option K) else some (t i / s i)) := by
    intro i j hij
    have hij' : (if s i = 0 then (none : Option K) else some (t i / s i)) =
        (if s j = 0 then none else some (t j / s j)) := hij
    by_contra hne
    apply hP i j hne
    rw [hst i, hst j, cross_smul_add_smul]
    suffices h : s i * t j - s j * t i = 0 by rw [h, zero_smul]
    by_cases hi : s i = 0 <;> by_cases hj : s j = 0
    · rw [hi, hj]; ring
    · rw [if_pos hi, if_neg hj] at hij'; cases hij'
    · rw [if_neg hi, if_pos hj] at hij'; cases hij'
    · rw [if_neg hi, if_neg hj] at hij'
      have h := Option.some.inj hij'
      rw [div_eq_div_iff hi hj] at h
      linear_combination -h
  simpa [Fintype.card_option] using Fintype.card_le_of_injective _ hf

/-- **At most `|K|` points off `ℓ` on another line `m`**: the point `ℓ ∩ m` is also on `m`. -/
theorem card_le_of_line_off [Fintype K] {ι : Type*} {R : ι → Fin 3 → K}
    (hR : ∀ i j, i ≠ j → R i ⨯₃ R j ≠ 0) {ℓ : Fin 3 → K} (hℓ : ℓ ≠ 0)
    (hoff : ∀ i, ℓ ⬝ᵥ R i ≠ 0) {m : Fin 3 → K} (hm : m ≠ 0) (s : Finset ι)
    (hs : ∀ i ∈ s, m ⬝ᵥ R i = 0) : s.card ≤ Fintype.card K := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · simp
  have hv : ℓ ⨯₃ m ≠ 0 := by
    intro h
    obtain ⟨c, hc⟩ := eq_smul_of_cross_eq_zero hℓ h
    have h0 := hs i₀ hi₀
    rw [hc, smul_dotProduct, smul_eq_mul] at h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact hm (by rw [hc, h1, zero_smul])
    · exact hoff i₀ h1
  have hoff' : ∀ i, (ℓ ⨯₃ m) ⨯₃ R i ≠ 0 := fun i h =>
    hoff i (dot_eq_zero_of_prop hv h (dot_self_cross ℓ m))
  have key := card_le_of_line (ι := Option s)
    (P := fun a => a.elim (ℓ ⨯₃ m) (fun i => R i)) (ℓ := m) ?_ hm ?_
  · simp only [Fintype.card_option, Fintype.card_coe] at key
    omega
  · rintro (_ | i) (_ | j) hij
    · exact absurd rfl hij
    · exact hoff' j
    · intro h
      have h2 : R i ⨯₃ (ℓ ⨯₃ m) = 0 := h
      exact hoff' i (by rw [← cross_anticomm (R i) (ℓ ⨯₃ m), h2, neg_zero])
    · exact hR i j (fun h => hij (congrArg some (Subtype.ext h)))
  · rintro (_ | i)
    · exact dot_cross_self ℓ m
    · exact hs i i.2

theorem cross_cross_cross (a b c : Fin 3 → K) :
    (a ⨯₃ b) ⨯₃ (a ⨯₃ c) = (a ⬝ᵥ b ⨯₃ c) • a := by
  ext i; fin_cases i <;> simp [cross_apply, dotProduct, Fin.sum_univ_succ] <;> ring

/-- **At most `|K| + 1` zeros besides a given one on a conic without line component**:
projection from the zero `u` is injective, since three collinear zeros force a line
component. -/
theorem card_le_of_conic [Fintype K] {ι : Type*} [Fintype ι] {P : ι → Fin 3 → K}
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0) {q : Fin 6 → K}
    (hno : ∀ ℓ m, ℓ ≠ 0 → q ≠ linMul ℓ m) (hq : ∀ i, evalC q (P i) = 0)
    {u : Fin 3 → K} (hu0 : u ≠ 0) (hu : evalC q u = 0) (hPu : ∀ i, u ⨯₃ P i ≠ 0) :
    Fintype.card ι ≤ Fintype.card K + 1 := by
  refine card_le_of_line (P := fun i => u ⨯₃ P i) (ℓ := u) (fun i j hij h => ?_) hu0
    (fun i => dot_self_cross u (P i))
  have h' : (u ⨯₃ P i) ⨯₃ (u ⨯₃ P j) = 0 := h
  rw [cross_cross_cross] at h'
  have h0 : u ⬝ᵥ P i ⨯₃ P j = 0 := (smul_eq_zero.mp h').resolve_right hu0
  obtain ⟨m, hm⟩ := conic_three (hPu i) (hPu i) (hPu j) (hP i j hij)
    (cross_dot_left u (P i)) (cross_dot_right u (P i))
    (by rw [dotProduct_comm, triple_product_permutation]; exact h0) hu (hq i) (hq j)
  exact hno _ m (hPu i) hm

/-! ### No common component over a field with three elements -/

/-- Over a field with three elements, two linearly independent cubics with nine pairwise
non-proportional common zeros have no common line. -/
theorem no_common_line_card3 [Fintype K] (hK : Fintype.card K = 3) (P : Fin 9 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0) (F G : PlaneCubic K)
    (hFG : LinearIndependent K ![F, G])
    (hF : ∀ i, eval F (P i) = 0) (hG : ∀ i, eval G (P i) = 0) :
    ¬ ∃ ℓ q q', ℓ ≠ 0 ∧ F = mulLin ℓ q ∧ G = mulLin ℓ q' := by
  classical
  rintro ⟨ℓ, q, q', hℓ, rfl, rfl⟩
  have hon : (Finset.univ.filter fun i => ℓ ⬝ᵥ P i = 0).card ≤ 4 := by
    have := card_le_of_line (ι := Finset.univ.filter fun i => ℓ ⬝ᵥ P i = 0)
      (P := fun i => P i) (fun i j hij => hP i j (fun h => hij (Subtype.ext h))) hℓ
      (fun i => (Finset.mem_filter.mp i.2).2)
    rw [Fintype.card_coe, hK] at this
    exact this
  have hsplit : (Finset.univ.filter fun i => ℓ ⬝ᵥ P i = 0).card
      + (Finset.univ.filter fun i => ¬ ℓ ⬝ᵥ P i = 0).card = 9 := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq
    (show 5 ≤ (Finset.univ.filter fun i => ¬ ℓ ⬝ᵥ P i = 0).card by omega)
  set e := t.orderEmbOfFin htc
  set R : Fin 5 → Fin 3 → K := fun k => P (e k)
  have hR : ∀ i j, i ≠ j → R i ⨯₃ R j ≠ 0 := fun i j hij =>
    hP _ _ (fun h => hij (e.injective h))
  have hoff : ∀ k, ℓ ⬝ᵥ R k ≠ 0 := fun k =>
    (Finset.mem_filter.mp (hts (t.orderEmbOfFin_mem htc k))).2
  have hq : ∀ k, evalC q (R k) = 0 := fun k => by
    have h := hF (e k)
    rw [eval_mulLin] at h
    exact (mul_eq_zero.mp h).resolve_left (hoff k)
  have hq' : ∀ k, evalC q' (R k) = 0 := fun k => by
    have h := hG (e k)
    rw [eval_mulLin] at h
    exact (mul_eq_zero.mp h).resolve_left (hoff k)
  have n4 : ∀ a b c d : Fin 5, ({a, b, c, d} : Finset (Fin 5)).card = 4 →
      ¬ Col4 (R a) (R b) (R c) (R d) := by
    rintro a b c d hc ⟨m, hm, ha, hb, hc', hd⟩
    have := card_le_of_line_off hR hℓ hoff hm {a, b, c, d} (by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> assumption)
    omega
  have hW := conics_le_one (Set.range R) ⟨0, rfl⟩ ⟨1, rfl⟩ ⟨2, rfl⟩ ⟨3, rfl⟩ ⟨4, rfl⟩
    (hR 0 1 (by decide)) (hR 0 2 (by decide)) (hR 0 3 (by decide)) (hR 0 4 (by decide))
    (hR 1 2 (by decide)) (hR 1 3 (by decide)) (hR 1 4 (by decide))
    (hR 2 3 (by decide)) (hR 2 4 (by decide)) (hR 3 4 (by decide))
    (n4 0 1 2 3 (by decide)) (n4 0 1 2 4 (by decide)) (n4 0 1 3 4 (by decide))
    (n4 0 2 3 4 (by decide)) (n4 1 2 3 4 (by decide))
  have hz : mulLin ℓ (0 : Fin 6 → K) = 0 := by simpa using mulLin_smul ℓ (0 : K) 0
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hFG.ne_zero 0 (by simpa using hz)
  have hq'0 : q' ≠ 0 := by
    rintro rfl
    exact hFG.ne_zero 1 (by simpa using hz)
  have hmem : ∀ r : Fin 6 → K, (∀ k, evalC r (R k) = 0) →
      r ∈ conicsThrough (Set.range R) := by
    rintro r hr _ ⟨k, rfl⟩
    exact hr k
  obtain ⟨c, -, hc⟩ := proportional hW (hmem q hq) (hmem q' hq') hq0 hq'0
  have := LinearIndependent.pair_iff.mp hFG 1 (-c) (by rw [hc, mulLin_smul]; simp)
  exact one_ne_zero this.1

/-- Over a field with three elements, two cubics with nine pairwise non-proportional common
zeros and no common line have no common conic. -/
theorem no_common_conic_card3 [Fintype K] (hK : Fintype.card K = 3) (P : Fin 9 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0) (F G : PlaneCubic K)
    (hF : ∀ i, eval F (P i) = 0) (hG : ∀ i, eval G (P i) = 0)
    (hlin : ¬ ∃ ℓ q q', ℓ ≠ 0 ∧ F = mulLin ℓ q ∧ G = mulLin ℓ q') :
    ¬ ∃ q m m', q ≠ 0 ∧ F = mulLin m q ∧ G = mulLin m' q := by
  classical
  rintro ⟨q, m, m', -, rfl, rfl⟩
  have hno : ∀ ℓ n, ℓ ≠ 0 → q ≠ linMul ℓ n := fun ℓ n hℓ hq =>
    hlin ⟨ℓ, linMul m n, linMul m' n, hℓ, by rw [hq, mulLin_linMul],
      by rw [hq, mulLin_linMul]⟩
  have hmm : ∀ i, evalC q (P i) ≠ 0 → m ⬝ᵥ P i = 0 ∧ m' ⬝ᵥ P i = 0 := fun i hi => by
    have h1 := hF i
    have h2 := hG i
    rw [eval_mulLin] at h1 h2
    exact ⟨(mul_eq_zero.mp h1).resolve_right hi, (mul_eq_zero.mp h2).resolve_right hi⟩
  have hoff : (Finset.univ.filter fun i => ¬ evalC q (P i) = 0).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    by_contra hab
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    obtain ⟨c, hc⟩ := lin_two (hP a b hab) (hmm a ha').1 (hmm b hb').1
    obtain ⟨c', hc'⟩ := lin_two (hP a b hab) (hmm a ha').2 (hmm b hb').2
    exact hlin ⟨P a ⨯₃ P b, c • q, c' • q, hP a b hab, by rw [hc, mulLin_smul_left],
      by rw [hc', mulLin_smul_left]⟩
  have hsplit : (Finset.univ.filter fun i => evalC q (P i) = 0).card
      + (Finset.univ.filter fun i => ¬ evalC q (P i) = 0).card = 9 := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  set s := Finset.univ.filter fun i => evalC q (P i) = 0
  obtain ⟨a, ha⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
  have hsq : ∀ i ∈ s, evalC q (P i) = 0 := fun i hi => (Finset.mem_filter.mp hi).2
  have hcard := card_le_of_conic (ι := s.erase a) (P := fun i => P i)
    (fun i j hij => hP i j (fun h => hij (Subtype.ext h))) hno
    (fun i => hsq i (Finset.mem_of_mem_erase i.2))
    (u := P a) (ne_zero_of_pairwise (n := 7) hP a) (hsq a ha)
    (fun i => hP a i (fun h => Finset.ne_of_mem_erase i.2 h.symm))
  rw [Fintype.card_coe, Finset.card_erase_of_mem ha, hK] at hcard
  omega

/-! ### The classical form over `𝔽₃` -/

/-- **Cayley–Bacharach over a field with three elements.** Two linearly independent cubics
with nine pairwise non-proportional common zeros (not necessarily all of them): every cubic
through eight of the points passes through the ninth. -/
theorem cayley_bacharach_card3 [Fintype K] (hK : Fintype.card K = 3) (P : Fin 9 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0) (F G : PlaneCubic K)
    (hFG : LinearIndependent K ![F, G])
    (hF : ∀ i, eval F (P i) = 0) (hG : ∀ i, eval G (P i) = 0)
    (H : PlaneCubic K) (hH : ∀ i : Fin 8, eval H (P (Fin.castSucc i)) = 0) :
    eval H (P 8) = 0 := by
  have : AtLeastThree K := AtLeastThree.of_card (by omega)
  have hlin := no_common_line_card3 hK P hP F G hFG hF hG
  exact cayley_bacharach_of_no_common_factor P hP F G hFG hF hG hlin
    (no_common_conic_card3 hK P hP F G hF hG hlin) H hH

/-- **Cayley–Bacharach, classical form, over a field with three elements.** -/
theorem cayley_bacharach_classical_card3 [Fintype K] (hK : Fintype.card K = 3)
    (P : Fin 9 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0)
    (F G : PlaneCubic K) (hFG : LinearIndependent K ![F, G])
    (hex : ExactlyMeetIn F G P)
    (H : PlaneCubic K) (hH : ∀ i : Fin 8, eval H (P (Fin.castSucc i)) = 0) :
    eval H (P 8) = 0 :=
  cayley_bacharach_card3 hK P hP F G hFG (fun i => (hex.1 i).2.1) (fun i => (hex.1 i).2.2) H hH

/-- **Cayley–Bacharach, classical form, over `𝔽₃ = ZMod 3`.** Two linearly independent
cubics whose common zeros are exactly nine pairwise non-proportional points: every cubic
through eight of them passes through the ninth. -/
theorem cayley_bacharach_classical_zmod3 (P : Fin 9 → Fin 3 → ZMod 3)
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0)
    (F G : PlaneCubic (ZMod 3)) (hFG : LinearIndependent (ZMod 3) ![F, G])
    (hex : ExactlyMeetIn F G P)
    (H : PlaneCubic (ZMod 3)) (hH : ∀ i : Fin 8, eval H (P (Fin.castSucc i)) = 0) :
    eval H (P 8) = 0 :=
  cayley_bacharach_classical_card3 (ZMod.card 3) P hP F G hFG hex H hH

/-- **Cayley–Bacharach, classical form, over finite fields.** The classical form holds over
every finite field with `|K| ∉ {4, 5, 7}` (vacuously for `|K| = 2`). Over `𝔽₄, 𝔽₅, 𝔽₇` it is
false (explicit counterexamples, checked by computer; not formalised here). -/
theorem cayley_bacharach_classical_finite [Fintype K] (h4 : Fintype.card K ≠ 4)
    (h5 : Fintype.card K ≠ 5) (h7 : Fintype.card K ≠ 7)
    (P : Fin 9 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0)
    (F G : PlaneCubic K) (hFG : LinearIndependent K ![F, G])
    (hex : ExactlyMeetIn F G P)
    (H : PlaneCubic K) (hH : ∀ i : Fin 8, eval H (P (Fin.castSucc i)) = 0) :
    eval H (P 8) = 0 := by
  obtain ⟨p, -, n, hp, hcard⟩ := FiniteField.card' K
  have h6 : Fintype.card K ≠ 6 := by
    intro h6
    rw [h6] at hcard
    have hp6 : p ∣ 2 * 3 := by
      rw [show (2 * 3 : ℕ) = 6 from rfl, hcard]; exact dvd_pow_self p n.ne_zero
    rcases (Nat.Prime.dvd_mul hp).mp hp6 with h | h
    · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h] at hcard
      have : 3 ∣ 2 ^ (n : ℕ) := by rw [← hcard]; norm_num
      exact absurd (Nat.prime_three.dvd_of_dvd_pow this) (by norm_num)
    · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h] at hcard
      have : 2 ∣ 3 ^ (n : ℕ) := by rw [← hcard]; norm_num
      exact absurd (Nat.prime_two.dvd_of_dvd_pow this) (by norm_num)
  have h1 : 1 < Fintype.card K := Fintype.one_lt_card
  by_cases h2 : Fintype.card K = 2
  · exact absurd (card_le_seven_of_not_atLeastThree
      (by rw [atLeastThree_iff_card]; omega) P hP) (by norm_num)
  by_cases h3 : Fintype.card K = 3
  · exact cayley_bacharach_classical_card3 h3 P hP F G hFG hex H hH
  · exact cayley_bacharach_classical_card8 (by omega) P hP F G hFG hex H hH

end PlaneCubic
