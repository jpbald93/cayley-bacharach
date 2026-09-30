import CayleyBacharach.Factor

/-!
# Cayley–Bacharach for two cubics meeting in exactly nine points

The hypothesis "the common zeros of `F` and `G` are exactly the nine points `P i` (up to
scaling)" rules out a common linear factor and a common conic factor over any infinite
field. This holds without algebraic closure: a common factor would give infinitely many
pairwise non-proportional common zeros.
-/

open Matrix

namespace PlaneCubic

variable {K : Type*} [Field K]

/-- If `u ⨯₃ p = 0` then `p k • u = u k • p`. -/
theorem smul_eq_smul_of_cross_eq_zero {u p : Fin 3 → K} (h : u ⨯₃ p = 0) (k : Fin 3) :
    p k • u = u k • p := by
  have e := cross_cross_eq_smul_sub_smul' (Pi.single k 1) u p
  rw [h] at e
  simp only [map_zero, single_dotProduct, one_mul, dotProduct_single, mul_one] at e
  exact (sub_eq_zero.mp e.symm)

/-- Proportionality to a nonzero vector is transitive. -/
theorem cross_eq_zero_of_cross_eq_zero {u w p : Fin 3 → K} (hp : p ≠ 0) (hu : u ⨯₃ p = 0)
    (hw : w ⨯₃ p = 0) : u ⨯₃ w = 0 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hp
  have e1 := smul_eq_smul_of_cross_eq_zero hu k
  have e2 := smul_eq_smul_of_cross_eq_zero hw k
  have h1 : (p k • u) ⨯₃ (p k • w) = (p k * p k) • (u ⨯₃ w) := by
    ext i; fin_cases i <;> simp [cross_apply] <;> ring
  have h2 : (u k • p) ⨯₃ (w k • p) = (u k * w k) • (p ⨯₃ p) := by
    ext i; fin_cases i <;> simp
  rw [e1, e2, h2, cross_self, smul_zero] at h1
  exact (smul_eq_zero.mp h1.symm).resolve_left (mul_ne_zero hk hk)

/-- **Pigeonhole.** If every nonzero `v` with property `Z` is proportional to one of finitely
many nonzero `P i`, there is no infinite family of pairwise non-proportional such `v`. -/
theorem false_of_infinite_family {ι : Type*} [Finite ι] {P : ι → Fin 3 → K}
    (hP : ∀ i, P i ≠ 0) {Z : (Fin 3 → K) → Prop}
    (hZ : ∀ v, v ≠ 0 → Z v → ∃ i, v ⨯₃ P i = 0) {S : Set K} (hS : S.Infinite)
    (g : K → Fin 3 → K) (hg0 : ∀ t ∈ S, g t ≠ 0) (hgZ : ∀ t ∈ S, Z (g t))
    (hg : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → g s ⨯₃ g t ≠ 0) : False := by
  have : Infinite S := hS.to_subtype
  choose f hf using fun t : S => hZ _ (hg0 t t.2) (hgZ t t.2)
  obtain ⟨s, t, hst, he⟩ := Finite.exists_ne_map_eq_of_infinite f
  have h1 := hf s
  have h2 := hf t
  rw [he] at h1
  exact hg s s.2 t t.2 (fun h => hst (Subtype.ext h))
    (cross_eq_zero_of_cross_eq_zero (hP _) h1 h2)

theorem cross_add_smul (u w : Fin 3 → K) (s t : K) :
    (u + s • w) ⨯₃ (u + t • w) = (t - s) • (u ⨯₃ w) := by
  ext i; fin_cases i <;> simp [cross_apply] <;> ring

theorem cross_add_smul' (u w : Fin 3 → K) (t : K) : w ⨯₃ (u + t • w) = -(u ⨯₃ w) := by
  ext i; fin_cases i <;> simp [cross_apply] <;> ring

/-- The points `u + t • w` (`t ∈ K`) of a line cannot all be among finitely many classes. -/
theorem false_of_pencil [Infinite K] {ι : Type*} [Finite ι] {P : ι → Fin 3 → K}
    (hP : ∀ i, P i ≠ 0) {Z : (Fin 3 → K) → Prop}
    (hZ : ∀ v, v ≠ 0 → Z v → ∃ i, v ⨯₃ P i = 0) {u w : Fin 3 → K} (huw : u ⨯₃ w ≠ 0)
    (hZuw : ∀ t : K, Z (u + t • w)) : False :=
  false_of_infinite_family hP hZ Set.infinite_univ (fun t => u + t • w)
    (fun t _ => ne_zero_of_cross (u := w) (by rw [cross_add_smul']; exact neg_ne_zero.mpr huw))
    (fun t _ => hZuw t)
    (fun s _ t _ hst => by
      rw [cross_add_smul]; exact smul_ne_zero (sub_ne_zero.mpr (Ne.symm hst)) huw)

/-- Two independent vectors on the line `ℓ = 0`. -/
theorem exists_line_basis (ℓ : Fin 3 → K) :
    ∃ u w : Fin 3 → K, ℓ ⬝ᵥ u = 0 ∧ ℓ ⬝ᵥ w = 0 ∧ u ⨯₃ w ≠ 0 := by
  by_cases h0 : ℓ 0 = 0
  · by_cases h1 : ℓ 1 = 0
    · refine ⟨![1, 0, 0], ![0, 1, 0], ?_, ?_, ?_⟩
      · simp [dotProduct, Fin.sum_univ_succ, h0]
      · simp [dotProduct, Fin.sum_univ_succ, h1]
      · intro h; have := congrFun h 2; simp [cross_apply] at this
    · refine ⟨![1, 0, 0], ![0, -ℓ 2, ℓ 1], ?_, ?_, ?_⟩
      · simp [dotProduct, Fin.sum_univ_succ, h0]
      · simp [dotProduct, Fin.sum_univ_succ]; ring
      · intro h; have := congrFun h 1; simp [cross_apply] at this; exact h1 this
  · refine ⟨![-ℓ 1, ℓ 0, 0], ![-ℓ 2, 0, ℓ 0], ?_, ?_, ?_⟩
    · simp [dotProduct, Fin.sum_univ_succ]; ring
    · simp [dotProduct, Fin.sum_univ_succ]; ring
    · intro h; have := congrFun h 0; simp [cross_apply] at this; exact h0 this

/-- A whole line cannot consist of common zeros lying in finitely many classes. -/
theorem false_of_line [Infinite K] {ι : Type*} [Finite ι] {P : ι → Fin 3 → K}
    (hP : ∀ i, P i ≠ 0) (ℓ : Fin 3 → K)
    (hZ : ∀ v, v ≠ 0 → ℓ ⬝ᵥ v = 0 → ∃ i, v ⨯₃ P i = 0) : False := by
  obtain ⟨u, w, hu, hw, huw⟩ := exists_line_basis ℓ
  exact false_of_pencil hP hZ huw fun t => by
    simp [dotProduct_add, dotProduct_smul, hu, hw]

/-- **Exactly nine common zeros ⇒ no common linear factor.** -/
theorem no_common_line_of_exact [Infinite K] {ι : Type*} [Finite ι] {P : ι → Fin 3 → K}
    (hP : ∀ i, P i ≠ 0) (F G : PlaneCubic K)
    (hex : ∀ v, v ≠ 0 → eval F v = 0 → eval G v = 0 → ∃ i, v ⨯₃ P i = 0) :
    ¬ ∃ ℓ q q', ℓ ≠ 0 ∧ F = mulLin ℓ q ∧ G = mulLin ℓ q' := by
  rintro ⟨ℓ, q, q', hℓ, rfl, rfl⟩
  exact false_of_line hP ℓ fun v hv hl =>
    hex v hv (eval_mulLin_of_dot_eq_zero _ _ _ hl) (eval_mulLin_of_dot_eq_zero _ _ _ hl)

/-- Polarisation of a conic: `B(u, d) = q(u + d) - q(u) - q(d)`. -/
def polarC (q : Fin 6 → K) (u d : Fin 3 → K) : K := evalC q (u + d) - evalC q u - evalC q d

theorem evalC_smul_add_smul' (q : Fin 6 → K) (u d : Fin 3 → K) (a b : K) :
    evalC q (a • u + b • d) = a ^ 2 * evalC q u + a * b * polarC q u d + b ^ 2 * evalC q d := by
  simp only [polarC, evalC_expand, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem polarC_add_smul (q : Fin 6 → K) (u v z : Fin 3 → K) (t : K) :
    polarC q u (v + t • z) = polarC q u v + t * polarC q u z := by
  simp only [polarC, evalC_expand, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem proj_cross_dot (u v z : Fin 3 → K) (a b c e s t : K) :
    (a • u + b • (v + t • z)) ⨯₃ (c • u + e • (v + s • z)) ⬝ᵥ u =
      b * e * (s - t) * (u ⨯₃ v ⬝ᵥ z) := by
  simp [cross_apply, dotProduct, Fin.sum_univ_succ]
  ring

theorem proj_cross_dot' (u v z : Fin 3 → K) (a b t : K) :
    u ⨯₃ (a • u + b • (v + t • z)) ⬝ᵥ z = b * (u ⨯₃ v ⬝ᵥ z) := by
  simp [cross_apply, dotProduct, Fin.sum_univ_succ]
  ring

/-- A third vector off the line through `u, v`. -/
theorem exists_off_line {u v : Fin 3 → K} (huv : u ⨯₃ v ≠ 0) : ∃ z, u ⨯₃ v ⬝ᵥ z ≠ 0 := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp huv
  exact ⟨Pi.single k 1, by simpa [dotProduct_single] using hk⟩

/-- **A conic with two distinct zeros has infinitely many.** If every zero of `q` is
proportional to one of finitely many `P i`, then `q` has no two non-proportional zeros.
(Projection from a zero `u`: `d ↦ q(d) • u - B(u, d) • d`.) Works over any infinite field,
in any characteristic. -/
theorem false_of_conic [Infinite K] {ι : Type*} [Finite ι] {P : ι → Fin 3 → K}
    (hP : ∀ i, P i ≠ 0) {q : Fin 6 → K} {u v : Fin 3 → K} (huv : u ⨯₃ v ≠ 0)
    (hu : evalC q u = 0) (hv : evalC q v = 0)
    (hZ : ∀ w, w ≠ 0 → evalC q w = 0 → ∃ i, w ⨯₃ P i = 0) : False := by
  by_cases hB : polarC q u v = 0
  · refine false_of_pencil hP hZ huv fun t => ?_
    have := evalC_smul_add_smul' q u v 1 t
    rw [one_smul] at this
    rw [this, hu, hv, hB]; ring
  obtain ⟨z, hz⟩ := exists_off_line huv
  set S : Set K := {t | polarC q u v + t * polarC q u z = 0}ᶜ
  have hS : S.Infinite := by
    refine Set.Finite.infinite_compl ((Set.finite_singleton
      (-(polarC q u v) / polarC q u z)).subset fun t ht => ?_)
    simp only [Set.mem_ofPred_eq] at ht
    by_cases hz0 : polarC q u z = 0
    · rw [hz0, mul_zero, add_zero] at ht; exact absurd ht hB
    · rw [Set.mem_singleton_iff, eq_div_iff hz0]; linear_combination ht
  refine false_of_infinite_family hP hZ hS
    (fun t => evalC q (v + t • z) • u + (-polarC q u (v + t • z)) • (v + t • z))
    (fun t ht => ?_) (fun t _ => ?_) (fun s hs t ht hst => ?_)
  · intro h0
    have := proj_cross_dot' u v z (evalC q (v + t • z)) (-polarC q u (v + t • z)) t
    rw [h0, polarC_add_smul] at this
    simp only [map_zero, zero_dotProduct] at this
    exact mul_ne_zero (neg_ne_zero.mpr ht) hz this.symm
  · show evalC q (_ • u + _ • _) = 0
    rw [evalC_smul_add_smul', hu]; ring
  · intro h0
    have := proj_cross_dot u v z (evalC q (v + s • z)) (-polarC q u (v + s • z))
      (evalC q (v + t • z)) (-polarC q u (v + t • z)) t s
    rw [h0, zero_dotProduct, polarC_add_smul, polarC_add_smul] at this
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hs) (neg_ne_zero.mpr ht))
      (sub_ne_zero.mpr (Ne.symm hst))) hz this.symm

/-- If two linear forms vanish at two non-proportional points, then with a conic `q` the
cubics `m q`, `m' q` share the whole line through the points: impossible under `hex`. -/
theorem false_of_common_pair [Infinite K] {ι : Type*} [Finite ι] {P : ι → Fin 3 → K}
    (hP : ∀ i, P i ≠ 0) {q : Fin 6 → K} {m m' a b : Fin 3 → K} (hab : a ⨯₃ b ≠ 0)
    (ma : m ⬝ᵥ a = 0) (mb : m ⬝ᵥ b = 0) (m'a : m' ⬝ᵥ a = 0) (m'b : m' ⬝ᵥ b = 0)
    (hex : ∀ v, v ≠ 0 → eval (mulLin m q) v = 0 → eval (mulLin m' q) v = 0 →
      ∃ i, v ⨯₃ P i = 0) : False := by
  obtain ⟨c, hc⟩ := lin_two hab ma mb
  obtain ⟨c', hc'⟩ := lin_two hab m'a m'b
  refine false_of_line hP (a ⨯₃ b) fun v hv hl => hex v hv ?_ ?_
  · rw [eval_mulLin, hc, smul_dotProduct, hl, smul_zero, zero_mul]
  · rw [eval_mulLin, hc', smul_dotProduct, hl, smul_zero, zero_mul]

theorem ne_zero_of_pairwise {n : ℕ} {P : Fin (n + 2) → Fin 3 → K}
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0) (i : Fin (n + 2)) : P i ≠ 0 := by
  obtain ⟨j, hj⟩ := exists_ne i
  exact ne_zero_of_cross' (hP i j hj.symm)

/-- **Exactly nine common zeros ⇒ no common conic factor.** No algebraic closure is needed:
if `F = m q` and `G = m' q`, then `q` vanishes on at most one of the classes `P i`
(otherwise `q` has infinitely many zeros, all common zeros, by `false_of_conic`), so the
linear forms `m, m'` both vanish at two of `P 0, P 1, P 2`, and then the line through them
consists of common zeros. -/
theorem no_common_conic_of_exact [Infinite K] {n : ℕ} {P : Fin (n + 3) → Fin 3 → K}
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0) (F G : PlaneCubic K)
    (hF : ∀ i, eval F (P i) = 0) (hG : ∀ i, eval G (P i) = 0)
    (hex : ∀ v, v ≠ 0 → eval F v = 0 → eval G v = 0 → ∃ i, v ⨯₃ P i = 0) :
    ¬ ∃ q m m', q ≠ 0 ∧ F = mulLin m q ∧ G = mulLin m' q := by
  rintro ⟨q, m, m', -, rfl, rfl⟩
  have hP0 : ∀ i, P i ≠ 0 := ne_zero_of_pairwise (n := n + 1) hP
  have hZq : ∀ w, w ≠ 0 → evalC q w = 0 → ∃ i, w ⨯₃ P i = 0 := fun w hw h =>
    hex w hw (by rw [eval_mulLin, show conicEval q w = 0 from h, mul_zero])
      (by rw [eval_mulLin, show conicEval q w = 0 from h, mul_zero])
  have hq2 : ∀ i j, i ≠ j → evalC q (P i) = 0 → evalC q (P j) = 0 → False :=
    fun i j hij hi hj => false_of_conic hP0 (hP i j hij) hi hj hZq
  have hmm : ∀ i, evalC q (P i) ≠ 0 → m ⬝ᵥ P i = 0 ∧ m' ⬝ᵥ P i = 0 := fun i hi => by
    have h1 := hF i
    have h2 := hG i
    rw [eval_mulLin] at h1 h2
    exact ⟨(mul_eq_zero.mp h1).resolve_right hi, (mul_eq_zero.mp h2).resolve_right hi⟩
  have key : ∀ a b, a ≠ b → evalC q (P a) ≠ 0 → evalC q (P b) ≠ 0 → False :=
    fun a b hab ha hb => false_of_common_pair hP0 (hP a b hab) (hmm a ha).1 (hmm b hb).1
      (hmm a ha).2 (hmm b hb).2 hex
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

/-- `v` is a common zero of the cubics `F` and `G` (a nonzero vector, i.e. a projective point). -/
def CommonZero (F G : PlaneCubic K) (v : Fin 3 → K) : Prop :=
  v ≠ 0 ∧ eval F v = 0 ∧ eval G v = 0

/-- The common zeros of `F, G` are exactly the points `P i`, up to scaling. -/
def ExactlyMeetIn {ι : Type*} (F G : PlaneCubic K) (P : ι → Fin 3 → K) : Prop :=
  (∀ i, CommonZero F G (P i)) ∧ ∀ v, CommonZero F G v → ∃ i, v ⨯₃ P i = 0

/-- **Cayley–Bacharach, classical form.** Let `F, G` be linearly independent cubics over an
infinite field whose common zeros are exactly nine pairwise non-proportional points
`P 0, …, P 8` (up to scaling). Then every cubic through `P 0, …, P 7` passes through `P 8`.
No algebraic closure is assumed. -/
theorem cayley_bacharach_classical [Infinite K] (P : Fin 9 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0)
    (F G : PlaneCubic K) (hFG : LinearIndependent K ![F, G])
    (hex : ExactlyMeetIn F G P)
    (H : PlaneCubic K) (hH : ∀ i : Fin 8, eval H (P (Fin.castSucc i)) = 0) :
    eval H (P 8) = 0 := by
  obtain ⟨hPZ, hZ⟩ := hex
  have hF : ∀ i, eval F (P i) = 0 := fun i => (hPZ i).2.1
  have hG : ∀ i, eval G (P i) = 0 := fun i => (hPZ i).2.2
  have hex' : ∀ v, v ≠ 0 → eval F v = 0 → eval G v = 0 → ∃ i, v ⨯₃ P i = 0 :=
    fun v hv h1 h2 => hZ v ⟨hv, h1, h2⟩
  exact cayley_bacharach_of_no_common_factor P hP F G hFG hF hG
    (no_common_line_of_exact (fun i => (hPZ i).1) F G hex')
    (no_common_conic_of_exact (n := 6) hP F G hF hG hex') H hH

end PlaneCubic
