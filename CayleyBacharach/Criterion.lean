import CayleyBacharach.Conic

/-!
# The general-position criterion for 8 points and plane cubics

* `evalMap P : PlaneCubic K →ₗ[K] (ι → K)`, `F ↦ (i ↦ F(P i))`.
* `mulLin_eq_zero`: `ℓ · q = 0` with `ℓ ≠ 0` forces `q = 0`.
* `finrank_ker_ge_of_conic` (easy direction): if a nonzero conic passes through all points,
  the cubics through them have dimension `≥ 3`.
* `finrank_ker_ge_of_line`: if all but (at most) three of the points lie on a line,
  the cubics through them have dimension `≥ 3`.
-/

namespace PlaneCubic

variable {K : Type*} [Field K]

/-- Simultaneous evaluation at a family of points. -/
def evalMap {ι : Type*} (P : ι → Fin 3 → K) : PlaneCubic K →ₗ[K] (ι → K) where
  toFun F i := eval F (P i)
  map_add' F G := by funext i; simp [eval_add]
  map_smul' c F := by funext i; simp [eval_smul]

@[simp] theorem evalMap_apply {ι : Type*} (P : ι → Fin 3 → K) (F : PlaneCubic K) (i : ι) :
    evalMap P F i = eval F (P i) := rfl

theorem mem_ker_evalMap {ι : Type*} (P : ι → Fin 3 → K) (F : PlaneCubic K) :
    F ∈ LinearMap.ker (evalMap P) ↔ ∀ i, eval F (P i) = 0 := by
  simp [LinearMap.mem_ker, funext_iff]

/-- `ℓ · q = 0` with `ℓ ≠ 0` forces `q = 0`. -/
theorem mulLin_eq_zero {ℓ : Fin 3 → K} {q : Fin 6 → K} (hℓ : ℓ ≠ 0) (h : mulLin ℓ q = 0) :
    q = 0 := by
  have E : ∀ i : Fin 10, mulLin ℓ q i = 0 := fun i => by rw [h]; rfl
  have e0 : ℓ 0 * q 0 = 0 := by simpa [mulLin] using E 0
  have e1 : ℓ 0 * q 1 + ℓ 1 * q 0 = 0 := by simpa [mulLin] using E 1
  have e2 : ℓ 0 * q 2 + ℓ 2 * q 0 = 0 := by simpa [mulLin] using E 2
  have e3 : ℓ 0 * q 3 + ℓ 1 * q 1 = 0 := by simpa [mulLin] using E 3
  have e4 : ℓ 0 * q 4 + ℓ 1 * q 2 + ℓ 2 * q 1 = 0 := by simpa [mulLin] using E 4
  have e5 : ℓ 0 * q 5 + ℓ 2 * q 2 = 0 := by simpa [mulLin] using E 5
  have e6 : ℓ 1 * q 3 = 0 := by simpa [mulLin] using E 6
  have e7 : ℓ 1 * q 4 + ℓ 2 * q 3 = 0 := by simpa [mulLin] using E 7
  have e8 : ℓ 1 * q 5 + ℓ 2 * q 4 = 0 := by simpa [mulLin] using E 8
  have e9 : ℓ 2 * q 5 = 0 := by simpa [mulLin] using E 9
  have key : q 0 = 0 ∧ q 1 = 0 ∧ q 2 = 0 ∧ q 3 = 0 ∧ q 4 = 0 ∧ q 5 = 0 := by
    by_cases h0 : ℓ 0 = 0
    · by_cases h1 : ℓ 1 = 0
      · have h2 : ℓ 2 ≠ 0 := by
          intro h2; apply hℓ; funext i; fin_cases i <;> simp [h0, h1, h2]
        have q0 : q 0 = 0 := by simpa [h0, h1, h2] using e2
        have q1 : q 1 = 0 := by simpa [h0, h1, h2] using e4
        have q2 : q 2 = 0 := by simpa [h0, h1, h2] using e5
        have q3 : q 3 = 0 := by simpa [h0, h1, h2] using e7
        have q4 : q 4 = 0 := by simpa [h0, h1, h2] using e8
        have q5 : q 5 = 0 := by simpa [h0, h1, h2] using e9
        exact ⟨q0, q1, q2, q3, q4, q5⟩
      · have q3 : q 3 = 0 := by simpa [h0, h1] using e6
        have q4 : q 4 = 0 := by simpa [h0, h1, q3] using e7
        have q5 : q 5 = 0 := by simpa [h0, h1, q4] using e8
        have q1 : q 1 = 0 := by simpa [h0, h1] using e3
        have q0 : q 0 = 0 := by simpa [h0, h1] using e1
        have q2 : q 2 = 0 := by simpa [h0, h1, q1] using e4
        exact ⟨q0, q1, q2, q3, q4, q5⟩
    · have q0 : q 0 = 0 := by simpa [h0] using e0
      have q1 : q 1 = 0 := by simpa [h0, q0] using e1
      have q2 : q 2 = 0 := by simpa [h0, q0] using e2
      have q3 : q 3 = 0 := by simpa [h0, q1] using e3
      have q4 : q 4 = 0 := by simpa [h0, q1, q2] using e4
      have q5 : q 5 = 0 := by simpa [h0, q2] using e5
      exact ⟨q0, q1, q2, q3, q4, q5⟩
  obtain ⟨q0, q1, q2, q3, q4, q5⟩ := key
  funext i; fin_cases i <;> simp [q0, q1, q2, q3, q4, q5]

/-- `m ↦ m · q` (a cubic), linear in the linear form `m`. -/
def mulConicLin (q : Fin 6 → K) : (Fin 3 → K) →ₗ[K] PlaneCubic K where
  toFun m := mulLin m q
  map_add' m m' := by ext i; fin_cases i <;> simp [mulLin] <;> ring
  map_smul' c m := by ext i; fin_cases i <;> simp [mulLin] <;> ring

/-- `q ↦ ℓ · q`, linear in the conic `q`. -/
def mulLinLin (ℓ : Fin 3 → K) : (Fin 6 → K) →ₗ[K] PlaneCubic K where
  toFun q := mulLin ℓ q
  map_add' q q' := by ext i; fin_cases i <;> simp [mulLin] <;> ring
  map_smul' c q := by ext i; fin_cases i <;> simp [mulLin] <;> ring

theorem mulConicLin_injective {q : Fin 6 → K} (hq : q ≠ 0) :
    Function.Injective (mulConicLin q) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro m hm
  by_contra hm0
  exact hq (mulLin_eq_zero hm0 hm)

theorem mulLinLin_injective {ℓ : Fin 3 → K} (hℓ : ℓ ≠ 0) :
    Function.Injective (mulLinLin ℓ) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro q hq
  exact mulLin_eq_zero hℓ hq

/-- **Easy direction (conic).** If a nonzero conic `q` passes through all the points, then
the cubics through them form a space of dimension `≥ 3` (it contains `m · q` for every
linear form `m`). -/
theorem finrank_ker_ge_of_conic {ι : Type*} (P : ι → Fin 3 → K) (q : Fin 6 → K) (hq : q ≠ 0)
    (hP : ∀ i, evalC q (P i) = 0) :
    3 ≤ Module.finrank K (LinearMap.ker (evalMap P)) := by
  have hle : LinearMap.range (mulConicLin q) ≤ LinearMap.ker (evalMap P) := by
    rintro F ⟨m, rfl⟩
    rw [mem_ker_evalMap]
    intro i
    simp only [mulConicLin, LinearMap.coe_mk, AddHom.coe_mk, eval_mulLin]
    have := hP i
    simp only [evalC] at this
    simp [this]
  have h3 : Module.finrank K (LinearMap.range (mulConicLin q)) = 3 := by
    rw [LinearMap.finrank_range_of_inj (mulConicLin_injective hq)]
    simp
  rw [← h3]
  exact Submodule.finrank_mono hle

/-- **Easy direction (line).** If all points outside `s` number at most three and every point
of `s` lies on the line `ℓ = 0` (`ℓ ≠ 0`), then the cubics through all the points form a
space of dimension `≥ 3`. (For 8 points: five collinear points force `dim ≥ 3`.) -/
theorem finrank_ker_ge_of_line {ι : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Fin 3 → K)
    (ℓ : Fin 3 → K) (hℓ : ℓ ≠ 0) (s : Finset ι) (hs : ∀ i ∈ s, ℓ ⬝ᵥ P i = 0)
    (hcard : Fintype.card {i // i ∉ s} ≤ 3) :
    3 ≤ Module.finrank K (LinearMap.ker (evalMap P)) := by
  set g : (Fin 6 → K) →ₗ[K] ({i // i ∉ s} → K) :=
    (evalMap (fun i : {i // i ∉ s} => P i)).comp (mulLinLin ℓ) with hg
  have hker : 3 ≤ Module.finrank K (LinearMap.ker g) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker g
    have h2 : Module.finrank K (LinearMap.range g) ≤ Fintype.card {i // i ∉ s} := by
      have := Submodule.finrank_le (LinearMap.range g)
      simpa using this
    simp only [Module.finrank_fin_fun] at h1
    omega
  have hle : Submodule.map (mulLinLin ℓ) (LinearMap.ker g) ≤ LinearMap.ker (evalMap P) := by
    rintro F ⟨q, hq, rfl⟩
    rw [mem_ker_evalMap]
    intro i
    by_cases hi : i ∈ s
    · simp [mulLinLin, eval_mulLin, hs i hi]
    · have := congrFun (LinearMap.mem_ker.mp hq) ⟨i, hi⟩
      simpa [hg] using this
  have heq : Module.finrank K (Submodule.map (mulLinLin ℓ) (LinearMap.ker g)) =
      Module.finrank K (LinearMap.ker g) :=
    (Submodule.equivMapOfInjective _ (mulLinLin_injective hℓ) _).finrank_eq.symm
  calc 3 ≤ _ := hker
    _ = _ := heq.symm
    _ ≤ _ := Submodule.finrank_mono hle

end PlaneCubic
