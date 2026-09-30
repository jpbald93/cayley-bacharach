import CayleyBacharach.Criterion
import CayleyBacharach.LineRestrict

/-!
# Spaces of cubics / conics / linear forms through a set of points, and residual bounds
-/

open Matrix

namespace PlaneCubic

variable {K : Type*} [Field K]

/-- Cubics vanishing on `S`. -/
def cubicsThrough (S : Set (Fin 3 → K)) : Submodule K (PlaneCubic K) where
  carrier := {F | ∀ v ∈ S, eval F v = 0}
  add_mem' hF hG v hv := by simp [eval_add, hF v hv, hG v hv]
  zero_mem' v _ := eval_zero v
  smul_mem' c F hF v hv := by simp [eval_smul, hF v hv]

/-- Conics vanishing on `S`. -/
def conicsThrough (S : Set (Fin 3 → K)) : Submodule K (Fin 6 → K) where
  carrier := {q | ∀ v ∈ S, evalC q v = 0}
  add_mem' hF hG v hv := by simp [evalC_add, hF v hv, hG v hv]
  zero_mem' v _ := by simp [evalC_expand]
  smul_mem' c F hF v hv := by simp [evalC_smul, hF v hv]

/-- Linear forms vanishing on `S`. -/
def linesThrough (S : Set (Fin 3 → K)) : Submodule K (Fin 3 → K) where
  carrier := {m | ∀ v ∈ S, m ⬝ᵥ v = 0}
  add_mem' hF hG v hv := by simp [add_dotProduct, hF v hv, hG v hv]
  zero_mem' v _ := by simp
  smul_mem' c F hF v hv := by simp [smul_dotProduct, hF v hv]

theorem ker_evalMap_eq {ι : Type*} (P : ι → Fin 3 → K) :
    LinearMap.ker (evalMap P) = cubicsThrough (Set.range P) := by
  ext F
  rw [mem_ker_evalMap]
  simp [cubicsThrough]

/-- One linear condition lowers the dimension by at most one. -/
theorem finrank_le_inf_ker_add_one {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W W' : Submodule K V) (f : V →ₗ[K] K)
    (h : ∀ x ∈ W, f x = 0 → x ∈ W') :
    Module.finrank K W ≤ Module.finrank K W' + 1 := by
  set g := f.domRestrict W
  have h1 := LinearMap.finrank_range_add_finrank_ker g
  have h2 : Module.finrank K (LinearMap.range g) ≤ 1 := by
    simpa using Submodule.finrank_le (LinearMap.range g)
  have h3 : Module.finrank K (LinearMap.ker g) ≤ Module.finrank K W' := by
    have e := (Submodule.equivMapOfInjective W.subtype W.injective_subtype
      (LinearMap.ker g)).finrank_eq
    rw [e]
    apply Submodule.finrank_mono
    rintro x ⟨y, hy, rfl⟩
    exact h y y.2 (by simpa [g] using hy)
  omega

theorem cubics_insert (a : Fin 3 → K) (S : Set (Fin 3 → K)) :
    Module.finrank K (cubicsThrough S) ≤ Module.finrank K (cubicsThrough (insert a S)) + 1 :=
  finrank_le_inf_ker_add_one _ _ (evalLin a) fun F hF ha v hv => by
    rcases hv with rfl | hv
    · simpa using ha
    · exact hF v hv

theorem conics_insert (a : Fin 3 → K) (S : Set (Fin 3 → K)) :
    Module.finrank K (conicsThrough S) ≤ Module.finrank K (conicsThrough (insert a S)) + 1 := by
  let f : (Fin 6 → K) →ₗ[K] K :=
    { toFun := fun q => evalC q a
      map_add' := fun q r => evalC_add q r a
      map_smul' := fun c q => evalC_smul c q a }
  exact finrank_le_inf_ker_add_one _ _ f fun F hF ha v hv => by
    rcases hv with rfl | hv
    · exact ha
    · exact hF v hv

/-- Residual bound for cubics: four distinct points of `S` on `ℓ = 0`. -/
theorem cubics_resid [AtLeastThree K] {ℓ u v w z : Fin 3 → K} (hℓ : ℓ ≠ 0)
    (huv : u ⨯₃ v ≠ 0) (huw : u ⨯₃ w ≠ 0) (hvw : v ⨯₃ w ≠ 0)
    (huz : u ⨯₃ z ≠ 0) (hvz : v ⨯₃ z ≠ 0) (hwz : w ⨯₃ z ≠ 0)
    (hu : ℓ ⬝ᵥ u = 0) (hv : ℓ ⬝ᵥ v = 0) (hw : ℓ ⬝ᵥ w = 0) (hz : ℓ ⬝ᵥ z = 0)
    (S : Set (Fin 3 → K)) (huS : u ∈ S) (hvS : v ∈ S) (hwS : w ∈ S) (hzS : z ∈ S) :
    Module.finrank K (cubicsThrough S) ≤
      Module.finrank K (conicsThrough {x | x ∈ S ∧ ℓ ⬝ᵥ x ≠ 0}) := by
  have hle : cubicsThrough S ≤ (conicsThrough {x | x ∈ S ∧ ℓ ⬝ᵥ x ≠ 0}).map (mulLinLin ℓ) := by
    intro F hF
    obtain ⟨q, rfl⟩ := cubic_four hℓ huv huw hvw huz hvz hwz hu hv hw hz
      (hF u huS) (hF v hvS) (hF w hwS) (hF z hzS)
    refine ⟨q, fun x hx => ?_, rfl⟩
    have := hF x hx.1
    rw [eval_mulLin] at this
    exact (mul_eq_zero.mp this).resolve_left hx.2
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_map_le _ _)

/-- `m ↦ ℓ · m` as a linear map from linear forms to conics. -/
def linMulLin (ℓ : Fin 3 → K) : (Fin 3 → K) →ₗ[K] (Fin 6 → K) where
  toFun m := linMul ℓ m
  map_add' m m' := by ext i; fin_cases i <;> simp [linMul] <;> ring
  map_smul' c m := by ext i; fin_cases i <;> simp [linMul] <;> ring

/-- Residual bound for conics: three distinct points of `S` on `ℓ = 0`. -/
theorem conics_resid {ℓ u v w : Fin 3 → K} (hℓ : ℓ ≠ 0)
    (huv : u ⨯₃ v ≠ 0) (huw : u ⨯₃ w ≠ 0) (hvw : v ⨯₃ w ≠ 0)
    (hu : ℓ ⬝ᵥ u = 0) (hv : ℓ ⬝ᵥ v = 0) (hw : ℓ ⬝ᵥ w = 0)
    (S : Set (Fin 3 → K)) (huS : u ∈ S) (hvS : v ∈ S) (hwS : w ∈ S) :
    Module.finrank K (conicsThrough S) ≤
      Module.finrank K (linesThrough {x | x ∈ S ∧ ℓ ⬝ᵥ x ≠ 0}) := by
  have hle : conicsThrough S ≤ (linesThrough {x | x ∈ S ∧ ℓ ⬝ᵥ x ≠ 0}).map (linMulLin ℓ) := by
    intro q hq
    obtain ⟨m, rfl⟩ := conic_three hℓ huv huw hvw hu hv hw (hq u huS) (hq v hvS) (hq w hwS)
    refine ⟨m, fun x hx => ?_, rfl⟩
    have := hq x hx.1
    rw [evalC_linMul] at this
    exact (mul_eq_zero.mp this).resolve_left hx.2
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_map_le _ _)

theorem lines_le_one {u v : Fin 3 → K} (huv : u ⨯₃ v ≠ 0) (S : Set (Fin 3 → K))
    (hu : u ∈ S) (hv : v ∈ S) : Module.finrank K (linesThrough S) ≤ 1 := by
  have hle : linesThrough S ≤ K ∙ (u ⨯₃ v) := by
    intro m hm
    obtain ⟨c, rfl⟩ := lin_two huv (hm u hu) (hm v hv)
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
  exact (Submodule.finrank_mono hle).trans (finrank_span_le_card _ |>.trans (by simp))

theorem lines_eq_zero {u v w : Fin 3 → K} (h : u ⨯₃ v ⬝ᵥ w ≠ 0) (S : Set (Fin 3 → K))
    (hu : u ∈ S) (hv : v ∈ S) (hw : w ∈ S) : Module.finrank K (linesThrough S) = 0 := by
  rw [Submodule.finrank_eq_zero, eq_bot_iff]
  intro m hm
  exact (Submodule.mem_bot K).mpr (lin_three h (hm u hu) (hm v hv) (hm w hw))

theorem lines_le_two {u : Fin 3 → K} (hu0 : u ≠ 0) (S : Set (Fin 3 → K)) (hu : u ∈ S) :
    Module.finrank K (linesThrough S) ≤ 2 := by
  let f : (Fin 3 → K) →ₗ[K] K :=
    { toFun := fun m => m ⬝ᵥ u
      map_add' := fun m m' => add_dotProduct m m' u
      map_smul' := fun c m => smul_dotProduct c m u }
  have hle : linesThrough S ≤ LinearMap.ker f := fun m hm => hm u hu
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 : LinearMap.range f ≠ ⊥ := by
    intro hb
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hu0
    have : f (Pi.single k 1) ∈ LinearMap.range f := LinearMap.mem_range_self f _
    rw [hb, Submodule.mem_bot] at this
    exact hk (by simpa [f, single_dotProduct] using this)
  have h3 : 0 < Module.finrank K (LinearMap.range f) :=
    Nat.pos_of_ne_zero fun h => h2 (Submodule.finrank_eq_zero.mp h)
  simp only [Module.finrank_fin_fun] at h1
  exact (Submodule.finrank_mono hle).trans (by omega)

end PlaneCubic
