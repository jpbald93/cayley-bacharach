import Mathlib

/-!
# Plane cubics as coefficient vectors

A homogeneous cubic form in the variables `x, y, z` (indexed `0, 1, 2` in `Fin 3`)
is represented by its vector of 10 coefficients, in the fixed monomial order

| index | 0  | 1   | 2   | 3   | 4   | 5   | 6  | 7   | 8   | 9  |
|-------|----|-----|-----|-----|-----|-----|----|-----|-----|----|
| mono  | x³ | x²y | x²z | xy² | xyz | xz² | y³ | y²z | yz² | z³ |
-/

/-- A plane cubic form over `K`: coefficient vector w.r.t. the monomial order
`x³, x²y, x²z, xy², xyz, xz², y³, y²z, yz², z³`. -/
abbrev PlaneCubic (K : Type*) := Fin 10 → K

namespace PlaneCubic

section CommRing

variable {R : Type*} [CommRing R]

/-- The values of the 10 cubic monomials at `v = (x, y, z)`, in the fixed order. -/
def mono (v : Fin 3 → R) : Fin 10 → R :=
  ![v 0 ^ 3, v 0 ^ 2 * v 1, v 0 ^ 2 * v 2, v 0 * v 1 ^ 2, v 0 * v 1 * v 2,
    v 0 * v 2 ^ 2, v 1 ^ 3, v 1 ^ 2 * v 2, v 1 * v 2 ^ 2, v 2 ^ 3]

/-- Evaluation of a cubic at a vector `v : Fin 3 → R`. -/
def eval (F : PlaneCubic R) (v : Fin 3 → R) : R := ∑ i, F i * mono v i

/-- The `i`-th monomial, as a cubic. -/
def monomial (i : Fin 10) : PlaneCubic R := Pi.single i 1

theorem eval_expand (F : PlaneCubic R) (v : Fin 3 → R) :
    eval F v = F 0 * v 0 ^ 3 + F 1 * (v 0 ^ 2 * v 1) + F 2 * (v 0 ^ 2 * v 2)
      + F 3 * (v 0 * v 1 ^ 2) + F 4 * (v 0 * v 1 * v 2) + F 5 * (v 0 * v 2 ^ 2)
      + F 6 * v 1 ^ 3 + F 7 * (v 1 ^ 2 * v 2) + F 8 * (v 1 * v 2 ^ 2)
      + F 9 * v 2 ^ 3 := by
  simp [eval, mono, Fin.sum_univ_succ]
  ring

theorem eval_monomial (i : Fin 10) (v : Fin 3 → R) : eval (monomial i) v = mono v i := by
  simp [eval, monomial, Pi.single_apply]

theorem eval_add (F G : PlaneCubic R) (v : Fin 3 → R) : eval (F + G) v = eval F v + eval G v := by
  simp [eval, add_mul, Finset.sum_add_distrib]

theorem eval_sub (F G : PlaneCubic R) (v : Fin 3 → R) : eval (F - G) v = eval F v - eval G v := by
  simp [eval, sub_mul, Finset.sum_sub_distrib]

theorem eval_zero (v : Fin 3 → R) : eval (0 : PlaneCubic R) v = 0 := by
  simp [eval]

theorem eval_smul (c : R) (F : PlaneCubic R) (v : Fin 3 → R) : eval (c • F) v = c * eval F v := by
  simp [eval, Finset.mul_sum, mul_assoc]

/-- Evaluation at a fixed vector, as a linear functional on cubics. -/
def evalLin (v : Fin 3 → R) : PlaneCubic R →ₗ[R] R where
  toFun F := eval F v
  map_add' F G := eval_add F G v
  map_smul' c F := eval_smul c F v

@[simp] theorem evalLin_apply (v : Fin 3 → R) (F : PlaneCubic R) : evalLin v F = eval F v := rfl

/-- The monomial basis of the space of cubics. -/
noncomputable def monoBasis : Module.Basis (Fin 10) R (PlaneCubic R) := Pi.basisFun R (Fin 10)

theorem monoBasis_apply (i : Fin 10) : (monoBasis i : PlaneCubic R) = monomial i := by
  simp [monoBasis, monomial]

theorem mono_smul (c : R) (v : Fin 3 → R) (i : Fin 10) :
    mono (c • v) i = c ^ 3 * mono v i := by
  fin_cases i <;> simp [mono] <;> ring

/-- Homogeneity: `F(c • v) = c³ F(v)`. -/
theorem eval_smul_vec (F : PlaneCubic R) (c : R) (v : Fin 3 → R) :
    eval F (c • v) = c ^ 3 * eval F v := by
  simp only [eval, mono_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `F` vanishes at the (projective point represented by the) vector `v`. -/
def VanishesAt (F : PlaneCubic R) (v : Fin 3 → R) : Prop := eval F v = 0

/-- Vanishing at a projective point is independent of the representative. -/
theorem vanishesAt_smul_iff [IsDomain R] (F : PlaneCubic R) {c : R} (hc : c ≠ 0)
    (v : Fin 3 → R) : VanishesAt F (c • v) ↔ VanishesAt F v := by
  simp [VanishesAt, eval_smul_vec, hc]

end CommRing

end PlaneCubic
