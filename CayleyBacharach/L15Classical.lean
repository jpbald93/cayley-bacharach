import CayleyBacharach.L14

/-!
Layer 15. These definitions and statements were written independently, from textbook statements,
by an AI model that did not see this code; they are reproduced verbatim. Each cov_* theorem proves
(or proves part of) one of them from this development.

Layout: the writer's definitions and statements (each unproved `theorem classical_X` of the
writer is repackaged mechanically as `def classical_X : Prop` with the same binders and
conclusion), then the comparison proofs (`l15_*` bridges, `cov_*` theorems, and the NEW PROOF
sections). The Mathlib ↔ library bridges come from `CayleyBacharach.L14` (namespace `CBL14`).
No writer statement was found false.
-/

open MvPolynomial Matrix

/-!
# Paper CB — classical statements (blind formalisation)

Cayley–Bacharach for plane cubics, eight-point criterion, Pascal, Braikenridge–Maclaurin,
Pappus.  Ambient: the projective plane `ℙ k (Fin 3 → k)` over a field `k`; curves are
nonzero homogeneous forms in `MvPolynomial (Fin 3) k`.
-/

open scoped LinearAlgebra.Projectivization
open Classical

noncomputable section

namespace CayleyBacharach.Classical

variable {k : Type*} [Field k]

/-- Shorthand for the polynomial ring `k[x,y,z]`. -/
abbrev R3 (k : Type*) [Field k] := MvPolynomial (Fin 3) k

/-- Shorthand for the projective plane `P²(k)`. -/
abbrev P2 (k : Type*) [Field k] := ℙ k (Fin 3 → k)

/-- OWN DEFINITION. A form `F` passes through the projective point `P`: `F(P) = 0`, evaluated
at the chosen representative (well defined for homogeneous `F`). -/
def Vanishes (F : R3 k) (P : P2 k) : Prop := MvPolynomial.eval P.rep F = 0

/-- OWN DEFINITION. A curve of degree `d` (line `d=1`, conic `d=2`, cubic `d=3`):
a nonzero homogeneous form of degree `d`. -/
def IsCurveOfDegree (d : ℕ) (F : R3 k) : Prop := F.IsHomogeneous d ∧ F ≠ 0

/-- OWN DEFINITION. Cubic. -/
abbrev IsCubic (F : R3 k) : Prop := IsCurveOfDegree 3 F
/-- OWN DEFINITION. Conic. -/
abbrev IsConic (F : R3 k) : Prop := IsCurveOfDegree 2 F
/-- OWN DEFINITION. Line. -/
abbrev IsLine (F : R3 k) : Prop := IsCurveOfDegree 1 F

/-- OWN DEFINITION. Three points of `P²` are collinear iff their representatives are linearly
dependent in `k³`. -/
def PCollinear (p q r : P2 k) : Prop := ¬ LinearIndependent k ![p.rep, q.rep, r.rep]

/-- OWN DEFINITION. The homogeneous prime ideal of the point `[v]`: kernel of
`F ↦ F(t·v) ∈ k[t]`. -/
def pointIdeal (v : Fin 3 → k) : Ideal (R3 k) :=
  RingHom.ker (MvPolynomial.aeval (fun i => Polynomial.C (v i) * Polynomial.X) :
    R3 k →ₐ[k] Polynomial k).toRingHom

instance (v : Fin 3 → k) : (pointIdeal v).IsPrime := RingHom.ker_isPrime _

/-- OWN DEFINITION. Intersection multiplicity `I(P; F, G)` of two plane curves at `P`:
the length of `R_𝔭 / (F, G)` where `R = k[x,y,z]` and `𝔭` is the homogeneous ideal of `P`
(this equals the length of `𝒪_{P²,P}/(f,g)`, the classical (Fulton) definition, since
`𝒪_{P²,P} → R_𝔭` is flat local with `𝔪 R_𝔭` maximal). Value `⊤` iff `F, G` share a
component through `P`. -/
def intMult (F G : R3 k) (P : P2 k) : ℕ∞ :=
  Module.length (Localization.AtPrime (pointIdeal P.rep))
    (Localization.AtPrime (pointIdeal P.rep) ⧸
      Ideal.span {algebraMap (R3 k) (Localization.AtPrime (pointIdeal P.rep)) F,
                  algebraMap (R3 k) (Localization.AtPrime (pointIdeal P.rep)) G})

/-- OWN DEFINITION. `P` is a simple (nonsingular) point of the curve `F`. -/
def IsSimplePoint (F : R3 k) (P : P2 k) : Prop :=
  Vanishes F P ∧ ∃ i : Fin 3, MvPolynomial.eval P.rep (MvPolynomial.pderiv i F) ≠ 0

/-- OWN DEFINITION. The `k`-vector space of cubic forms vanishing at the given points. -/
def cubicsThrough {n : ℕ} (P : Fin n → P2 k) : Submodule k (R3 k) :=
  MvPolynomial.homogeneousSubmodule (Fin 3) k 3 ⊓
    ⨅ i, LinearMap.ker (MvPolynomial.aeval (P i).rep : R3 k →ₐ[k] k).toLinearMap

/-! ## CB1. Cayley–Bacharach (Chasles' form) -/

/-- CB1(a). -/
def classical_CB1_a : Prop :=
  ∀ (F₁ F₂ F : R3 k) (h₁ : IsCubic F₁) (h₂ : IsCubic F₂)
    (hcop : IsRelPrime F₁ F₂)  -- no common component
    (P : Fin 9 → P2 k) (hP : Function.Injective P)
    (hP₁ : ∀ i, Vanishes F₁ (P i)) (hP₂ : ∀ i, Vanishes F₂ (P i))
    -- AMBIGUOUS: "meet in nine distinct points" could be read as the common zero locus being
    -- exactly {P₁,…,P₉}; by Bézout this is implied by the nine distinct common points.
    (hF : IsCubic F) (hF8 : ∀ i : Fin 9, i ≠ 8 → Vanishes F (P i)),

    Vanishes F (P 8)


/-- CB1(a), bracketed equivalent form: `C` is a linear combination of `F₁, F₂`. -/
def classical_CB1_a_linear : Prop :=
  ∀ (F₁ F₂ F : R3 k) (h₁ : IsCubic F₁) (h₂ : IsCubic F₂)
    (hcop : IsRelPrime F₁ F₂)
    (P : Fin 9 → P2 k) (hP : Function.Injective P)
    (hP₁ : ∀ i, Vanishes F₁ (P i)) (hP₂ : ∀ i, Vanishes F₂ (P i))
    (hF : IsCubic F) (hF8 : ∀ i : Fin 9, i ≠ 8 → Vanishes F (P i)),

    ∃ a b : k, F = MvPolynomial.C a * F₁ + MvPolynomial.C b * F₂


/-- CB1(b), multiplicity version (Fulton), simple-points hypothesis. -/
def classical_CB1_b : Prop :=
  ∀
    -- EXTRA HYPOTHESIS: `k` algebraically closed (Fulton's standing convention); needed so
    -- that intersection cycles are supported on `k`-points of `P²`.
    [IsAlgClosed k]
    (F₁ F₂ F : R3 k) (h₁ : IsCubic F₁) (h₂ : IsCubic F₂) (hF : IsCubic F)
    (hcop : IsRelPrime F₁ F₂)
    (P : Fin 9 → P2 k)
    (hcyc : ∀ X, intMult F₁ F₂ X = (Nat.card {i // P i = X} : ℕ∞))
    -- AMBIGUOUS: the statement allows "C₁ irreducible" instead; we use the general
    -- hypothesis that P₁,…,P₉ are simple points of C₁ (see `classical_CB1_b_irreducible`).
    (hsimple : ∀ i, IsSimplePoint F₁ (P i))
    (Q : P2 k)
    (hcyc' : ∀ X, intMult F₁ F X =
      (Nat.card {i : Fin 8 // P i.castSucc = X} : ℕ∞) + (if Q = X then 1 else 0)),

    Q = P 8


/-- CB1(b), the "C₁ irreducible" reading of the hypothesis. -/
def classical_CB1_b_irreducible : Prop :=
  ∀
    [IsAlgClosed k]  -- EXTRA HYPOTHESIS: as in `classical_CB1_b`
    (F₁ F₂ F : R3 k) (h₁ : IsCubic F₁) (h₂ : IsCubic F₂) (hF : IsCubic F)
    (hcop : IsRelPrime F₁ F₂)
    (hirr : Irreducible F₁)
    -- AMBIGUOUS: Fulton's Prop. 5.6.2 assumes both C₁ irreducible and Pᵢ simple; the
    -- statement as given uses irreducibility alone, which is what we formalise here.
    (P : Fin 9 → P2 k)
    (hcyc : ∀ X, intMult F₁ F₂ X = (Nat.card {i // P i = X} : ℕ∞))
    (Q : P2 k)
    (hcyc' : ∀ X, intMult F₁ F X =
      (Nat.card {i : Fin 8 // P i.castSucc = X} : ℕ∞) + (if Q = X then 1 else 0)),

    Q = P 8


/-! ## CB2. Eight-point criterion -/

/-- OWN DEFINITION. Hypotheses of CB2: no four of the points on a line, no seven on a conic. -/
def EightPointGeneral (P : Fin 8 → P2 k) : Prop :=
  Function.Injective P ∧
  (∀ s : Finset (Fin 8), s.card = 4 → ¬ ∃ L : R3 k, IsLine L ∧ ∀ i ∈ s, Vanishes L (P i)) ∧
  (∀ s : Finset (Fin 8), s.card = 7 → ¬ ∃ Q : R3 k, IsConic Q ∧ ∀ i ∈ s, Vanishes Q (P i))

/-- CB2(a). -/
def classical_CB2_a : Prop :=
  ∀ (P : Fin 8 → P2 k) (hP : EightPointGeneral P),

    Module.finrank k (cubicsThrough P) = 2


/-- CB2(b), algebraically closed form: there is a unique ninth base point `P₉` such that any two
independent members of the pencil cut out exactly `P₁ + ⋯ + P₈ + P₉`.
AMBIGUOUS: "uniquely determined ninth point" read as a point of the base cycle (it may coincide
with some `Pᵢ`); the "nine distinct points" reading is `classical_CB2_b_distinct`. -/
def classical_CB2_b : Prop :=
  ∀ [IsAlgClosed k] (P : Fin 8 → P2 k) (hP : EightPointGeneral P),

    ∃! P₉ : P2 k, ∀ F₁ ∈ cubicsThrough P, ∀ F₂ ∈ cubicsThrough P,
      LinearIndependent k ![F₁, F₂] →
      ∀ X, intMult F₁ F₂ X =
        (Nat.card {i // P i = X} : ℕ∞) + (if P₉ = X then 1 else 0)


/-- CB2(b), "two members of the pencil meet in nine distinct points" form, any field. -/
def classical_CB2_b_distinct : Prop :=
  ∀ (P : Fin 8 → P2 k) (hP : EightPointGeneral P)
    (F₁ F₂ : R3 k) (hF₁ : F₁ ∈ cubicsThrough P) (hF₂ : F₂ ∈ cubicsThrough P)
    (h₁ : F₁ ≠ 0) (h₂ : F₂ ≠ 0) (hcop : IsRelPrime F₁ F₂)
    (Q : P2 k) (hQ : Q ∉ Set.range P) (hQ₁ : Vanishes F₁ Q) (hQ₂ : Vanishes F₂ Q),

    ∃! P₉ : P2 k, P₉ ∉ Set.range P ∧ ∀ F ∈ cubicsThrough P, Vanishes F P₉


/-! ## CB3. Pascal and Braikenridge–Maclaurin -/

/-- CB3(a), Pascal. `X, Y, Z` are given by their defining property
(`X` lies on lines `AB` and `DE`, etc.). -/
def classical_CB3_a : Prop :=
  ∀ (q : R3 k) (hq : IsConic q) (hirr : Irreducible q)
    -- AMBIGUOUS: "nondegenerate" read as irreducible over k (with six k-points this equals
    -- geometric irreducibility); alternative: nonsingular / nonzero discriminant.
    (A B C D E F : P2 k) (hdist : Function.Injective ![A, B, C, D, E, F])
    (hA : Vanishes q A) (hB : Vanishes q B) (hC : Vanishes q C)
    (hD : Vanishes q D) (hE : Vanishes q E) (hF : Vanishes q F)
    (X Y Z : P2 k)
    (hX : PCollinear A B X ∧ PCollinear D E X)
    (hY : PCollinear B C Y ∧ PCollinear E F Y)
    (hZ : PCollinear C D Z ∧ PCollinear F A Z),

    PCollinear X Y Z


/-- Well-formedness of CB3(a): the opposite sides meet in a unique point. -/
def classical_CB3_a_obligation : Prop :=
  ∀ (q : R3 k) (hq : IsConic q) (hirr : Irreducible q)
    (A B C D E F : P2 k) (hdist : Function.Injective ![A, B, C, D, E, F])
    (hA : Vanishes q A) (hB : Vanishes q B) (hC : Vanishes q C)
    (hD : Vanishes q D) (hE : Vanishes q E) (hF : Vanishes q F),

    (∃! X, PCollinear A B X ∧ PCollinear D E X) ∧
    (∃! Y, PCollinear B C Y ∧ PCollinear E F Y) ∧
    (∃! Z, PCollinear C D Z ∧ PCollinear F A Z)


/-- CB3(b), Braikenridge–Maclaurin (converse of Pascal). -/
def classical_CB3_b : Prop :=
  ∀ (A B C D E F : P2 k)
    (hgen : ∀ i j l : Fin 6, i ≠ j → i ≠ l → j ≠ l →
      ¬ PCollinear (![A, B, C, D, E, F] i) (![A, B, C, D, E, F] j) (![A, B, C, D, E, F] l))
    (X Y Z : P2 k)
    (hX : PCollinear A B X ∧ PCollinear D E X)
    (hY : PCollinear B C Y ∧ PCollinear E F Y)
    (hZ : PCollinear C D Z ∧ PCollinear F A Z)
    (hXYZ : PCollinear X Y Z),

    ∃ q : R3 k, IsConic q ∧ Vanishes q A ∧ Vanishes q B ∧ Vanishes q C ∧
      Vanishes q D ∧ Vanishes q E ∧ Vanishes q F


/-- Well-formedness of CB3(b). -/
def classical_CB3_b_obligation : Prop :=
  ∀ (A B C D E F : P2 k)
    (hgen : ∀ i j l : Fin 6, i ≠ j → i ≠ l → j ≠ l →
      ¬ PCollinear (![A, B, C, D, E, F] i) (![A, B, C, D, E, F] j) (![A, B, C, D, E, F] l)),

    (∃! X, PCollinear A B X ∧ PCollinear D E X) ∧
    (∃! Y, PCollinear B C Y ∧ PCollinear E F Y) ∧
    (∃! Z, PCollinear C D Z ∧ PCollinear F A Z)


/-! ## CB4. Pappus -/

/-- CB4(a), Pappus. Lines `L, M` given by linear forms `l, m`; distinct lines = non-associated
forms. -/
def classical_CB4_a : Prop :=
  ∀ (l m : R3 k) (hl : IsLine l) (hm : IsLine m) (hlm : ¬ Associated l m)
    (A B C A' B' C' : P2 k)
    (hA : Vanishes l A) (hB : Vanishes l B) (hC : Vanishes l C)
    (hA' : Vanishes m A') (hB' : Vanishes m B') (hC' : Vanishes m C')
    (hABC : A ≠ B ∧ B ≠ C ∧ A ≠ C) (hABC' : A' ≠ B' ∧ B' ≠ C' ∧ A' ≠ C')
    (hoff : ¬ Vanishes m A ∧ ¬ Vanishes m B ∧ ¬ Vanishes m C ∧
      ¬ Vanishes l A' ∧ ¬ Vanishes l B' ∧ ¬ Vanishes l C')
    (X Y Z : P2 k)
    (hX : PCollinear A B' X ∧ PCollinear A' B X)
    (hY : PCollinear A C' Y ∧ PCollinear A' C Y)
    (hZ : PCollinear B C' Z ∧ PCollinear B' C Z),

    PCollinear X Y Z


/-- Well-formedness of CB4(a). -/
def classical_CB4_a_obligation : Prop :=
  ∀ (l m : R3 k) (hl : IsLine l) (hm : IsLine m)
    (hlm : ¬ Associated l m)
    (A B C A' B' C' : P2 k)
    (hA : Vanishes l A) (hB : Vanishes l B) (hC : Vanishes l C)
    (hA' : Vanishes m A') (hB' : Vanishes m B') (hC' : Vanishes m C')
    (hABC : A ≠ B ∧ B ≠ C ∧ A ≠ C) (hABC' : A' ≠ B' ∧ B' ≠ C' ∧ A' ≠ C')
    (hoff : ¬ Vanishes m A ∧ ¬ Vanishes m B ∧ ¬ Vanishes m C ∧
      ¬ Vanishes l A' ∧ ¬ Vanishes l B' ∧ ¬ Vanishes l C'),

    (∃! X, PCollinear A B' X ∧ PCollinear A' B X) ∧
    (∃! Y, PCollinear A C' Y ∧ PCollinear A' C Y) ∧
    (∃! Z, PCollinear B C' Z ∧ PCollinear B' C Z)


/-- CB4(b), hexagon form: vertices `V 0, …, V 5`, with `V 0, V 2, V 4` on `L` and
`V 1, V 3, V 5` on `M`; opposite sides `V0V1 / V3V4`, `V1V2 / V4V5`, `V2V3 / V5V0`. -/
def classical_CB4_b : Prop :=
  ∀ (l m : R3 k) (hl : IsLine l) (hm : IsLine m)
    (V : Fin 6 → P2 k)
    (hL : Vanishes l (V 0) ∧ Vanishes l (V 2) ∧ Vanishes l (V 4))
    (hM : Vanishes m (V 1) ∧ Vanishes m (V 3) ∧ Vanishes m (V 5))
    -- EXTRA HYPOTHESIS: the two lines are distinct, the vertices are distinct and none is
    -- `L ∩ M`; without this opposite sides may coincide and their "intersection point" is not
    -- determined (the hexagon is degenerate).
    (hlm : ¬ Associated l m) (hV : Function.Injective V)
    (hoff : ¬ Vanishes m (V 0) ∧ ¬ Vanishes m (V 2) ∧ ¬ Vanishes m (V 4) ∧
      ¬ Vanishes l (V 1) ∧ ¬ Vanishes l (V 3) ∧ ¬ Vanishes l (V 5))
    (X Y Z : P2 k)
    (hX : PCollinear (V 0) (V 1) X ∧ PCollinear (V 3) (V 4) X)
    (hY : PCollinear (V 1) (V 2) Y ∧ PCollinear (V 4) (V 5) Y)
    (hZ : PCollinear (V 2) (V 3) Z ∧ PCollinear (V 5) (V 0) Z),

    PCollinear X Y Z


/-- Well-formedness of CB4(b). -/
def classical_CB4_b_obligation : Prop :=
  ∀ (l m : R3 k) (hl : IsLine l) (hm : IsLine m)
    (V : Fin 6 → P2 k)
    (hL : Vanishes l (V 0) ∧ Vanishes l (V 2) ∧ Vanishes l (V 4))
    (hM : Vanishes m (V 1) ∧ Vanishes m (V 3) ∧ Vanishes m (V 5))
    (hlm : ¬ Associated l m) (hV : Function.Injective V)
    (hoff : ¬ Vanishes m (V 0) ∧ ¬ Vanishes m (V 2) ∧ ¬ Vanishes m (V 4) ∧
      ¬ Vanishes l (V 1) ∧ ¬ Vanishes l (V 3) ∧ ¬ Vanishes l (V 5)),

    (∃! X, PCollinear (V 0) (V 1) X ∧ PCollinear (V 3) (V 4) X) ∧
    (∃! Y, PCollinear (V 1) (V 2) Y ∧ PCollinear (V 4) (V 5) Y) ∧
    (∃! Z, PCollinear (V 2) (V 3) Z ∧ PCollinear (V 5) (V 0) Z)



/-! Comparison proofs. -/

open CBL14

/-! ### Bridges: writer's encodings ↔ L14 Mathlib-only forms -/

theorem l15_li {a b : P2 k} (h : a ≠ b) : LinearIndependent k ![a.rep, b.rep] := by
  have h' := (Projectivization.independent_pair_iff_ne a b).2 h
  rw [Projectivization.independent_iff] at h'
  have e : (Projectivization.rep ∘ ![a, b]) = ![a.rep, b.rep] := by
    funext i; fin_cases i <;> rfl
  rw [e] at h'; exact h'

theorem l15_pair {n : ℕ} {P : Fin n → P2 k} (hP : Function.Injective P) :
    ∀ i j, i ≠ j → LinearIndependent k ![(P i).rep, (P j).rep] :=
  fun i j hij => l15_li (fun h => hij (hP h))

theorem l15_not_unit {p : R3 k} {n : ℕ} (hp : p.IsHomogeneous n) (hn : n ≠ 0) (h0 : p ≠ 0) :
    ¬ IsUnit p := by
  intro hu
  obtain ⟨r, -, rfl⟩ := (MvPolynomial.isUnit_iff_eq_C_of_isReduced).1 hu
  exact hn ((MvPolynomial.isHomogeneous_C (Fin 3) r).inj_right hp h0).symm

theorem l15_lin {F G : R3 k} (hcop : IsRelPrime F G) :
    ¬ ∃ ℓ q q' : MvPolynomial (Fin 3) k, ℓ.IsHomogeneous 1 ∧ q.IsHomogeneous 2 ∧
      q'.IsHomogeneous 2 ∧ ℓ ≠ 0 ∧ F = ℓ * q ∧ G = ℓ * q' := by
  rintro ⟨ℓ, q, q', hℓ, -, -, h0, rfl, rfl⟩
  exact l15_not_unit hℓ one_ne_zero h0 (hcop (dvd_mul_right ℓ q) (dvd_mul_right ℓ q'))

theorem l15_con {F G : R3 k} (hcop : IsRelPrime F G) :
    ¬ ∃ q m m' : MvPolynomial (Fin 3) k, q.IsHomogeneous 2 ∧ m.IsHomogeneous 1 ∧
      m'.IsHomogeneous 1 ∧ q ≠ 0 ∧ F = m * q ∧ G = m' * q := by
  rintro ⟨q, m, m', hq, -, -, h0, rfl, rfl⟩
  exact l15_not_unit hq two_ne_zero h0 (hcop (dvd_mul_left q m) (dvd_mul_left q m'))

theorem l15_indep {F G : R3 k} (hF : IsCubic F) (hG : IsCubic G) (hcop : IsRelPrime F G) :
    LinearIndependent k ![F, G] := by
  rw [linearIndependent_fin2]
  refine ⟨hG.2, fun a ha => ?_⟩
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at ha
  apply l15_not_unit hG.1 three_ne_zero hG.2
  apply hcop _ dvd_rfl
  rw [← ha, MvPolynomial.smul_eq_C_mul]; exact dvd_mul_left _ _

theorem l15_mem {n : ℕ} {P : Fin n → P2 k} {F : R3 k} :
    F ∈ cubicsThrough P ↔ F.IsHomogeneous 3 ∧ ∀ i, Vanishes F (P i) := by
  simp only [cubicsThrough, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    MvPolynomial.mem_homogeneousSubmodule, AlgHom.toLinearMap_apply, Vanishes]
  exact Iff.rfl

theorem l15_li3_iff (a b c : Fin 3 → k) :
    LinearIndependent k ![a, b, c] ↔ Matrix.det ![a, b, c] ≠ 0 := by
  have := Matrix.linearIndependent_rows_iff_isUnit (A := (![a, b, c] : Matrix (Fin 3) (Fin 3) k))
  exact this.trans ((Matrix.isUnit_iff_isUnit_det (A := _)).trans isUnit_iff_ne_zero)

theorem l15_pcol_iff (A B X : P2 k) :
    PCollinear A B X ↔ X.rep ⬝ᵥ (A.rep ⨯₃ B.rep) = 0 := by
  unfold PCollinear
  rw [l15_li3_iff, not_not, ← triple_product_eq_det, triple_product_permutation,
    triple_product_permutation]

theorem l15_det_of (X A B : Fin 3 → k) (h : X ⬝ᵥ A ⨯₃ B = 0) : Matrix.det ![X, A, B] = 0 := by
  rw [← triple_product_eq_det]; exact h

theorem l15_det_of' (X A B : Fin 3 → k) (h : X ⬝ᵥ B ⨯₃ A = 0) : Matrix.det ![X, A, B] = 0 := by
  rw [← triple_product_eq_det, ← cross_anticomm, dotProduct_neg, h, neg_zero]

theorem l15_col_of (X Y Z : Fin 3 → k) (h : Matrix.det ![X, Y, Z] = 0) : Z ⬝ᵥ X ⨯₃ Y = 0 := by
  rw [← triple_product_eq_det, triple_product_permutation, triple_product_permutation] at h
  exact h

theorem l15_col_of' (X Y Z : Fin 3 → k) (h : Matrix.det ![X, Z, Y] = 0) : Z ⬝ᵥ X ⨯₃ Y = 0 := by
  rw [← triple_product_eq_det, ← cross_anticomm, dotProduct_neg, neg_eq_zero,
    triple_product_permutation, triple_product_permutation] at h
  exact h

/-- Two lines `AB`, `DE` (with `D ∉ AB`, `A ∉ DE`) meet in exactly one projective point. -/
theorem l15_meet (A B D E : P2 k) (h : ¬ PCollinear A B D) (h' : ¬ PCollinear D E A) :
    ∃! X, PCollinear A B X ∧ PCollinear D E X := by
  rw [l15_pcol_iff] at h h'
  have hv : D.rep ⨯₃ E.rep ≠ 0 := by intro hv; apply h'; rw [hv, dotProduct_zero]
  have huv : A.rep ⨯₃ B.rep ⨯₃ (D.rep ⨯₃ E.rep) ≠ 0 := by
    intro h0
    obtain ⟨c, hc⟩ := (PlaneCubic.cross_eq_zero_iff_eq_smul hv).1 h0
    apply h
    rw [hc, dotProduct_smul, dot_self_cross, smul_zero]
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep k _ huv
  refine ⟨Projectivization.mk k _ huv, ⟨?_, ?_⟩, ?_⟩
  · rw [l15_pcol_iff, ← ha, Units.smul_def, smul_dotProduct, PlaneCubic.cross_dot_left,
      smul_zero]
  · rw [l15_pcol_iff, ← ha, Units.smul_def, smul_dotProduct, PlaneCubic.cross_dot_right,
      smul_zero]
  · rintro Y ⟨hY1, hY2⟩
    rw [l15_pcol_iff] at hY1 hY2
    obtain ⟨c, hc⟩ := l14b_on_two huv hY1 hY2
    rw [← Projectivization.mk_rep Y]
    exact (Projectivization.mk_eq_mk_iff' k _ _ Y.rep_nonzero huv).2 ⟨c, hc.symm⟩

/-- `W ∉ UV` when `U ≠ V` lie on the line `m = 0` and `W` does not. -/
theorem l15_noncol_line {m : R3 k} (hm : IsLine m) {W U V : P2 k} (hU : Vanishes m U)
    (hV : Vanishes m V) (hUV : U ≠ V) (hW : ¬ Vanishes m W) : ¬ PCollinear W U V := by
  rw [l15_pcol_iff]
  intro h
  rw [triple_product_permutation, dotProduct_comm] at h
  obtain ⟨s, t, hst⟩ := PlaneCubic.exists_smul_add_smul (l14b_cross (l15_li hUV)) h
  apply hW
  unfold Vanishes at hU hV ⊢
  rw [l14b_eval1 hm.1] at hU hV ⊢
  rw [hst, dotProduct_add, dotProduct_smul, dotProduct_smul, hU, hV]; simp

theorem l15_irr {q : R3 k} (hq : IsConic q) (hirr : Irreducible q) :
    ∀ ℓ m : MvPolynomial (Fin 3) k, ℓ.IsHomogeneous 1 → m.IsHomogeneous 1 → q ≠ ℓ * m := by
  intro ℓ m hℓ hm h
  have hℓ0 : ℓ ≠ 0 := by rintro rfl; exact hq.2 (by rw [h, zero_mul])
  have hm0 : m ≠ 0 := by rintro rfl; exact hq.2 (by rw [h, mul_zero])
  rcases hirr.isUnit_or_isUnit h with hu | hu
  · exact l15_not_unit hℓ one_ne_zero hℓ0 hu
  · exact l15_not_unit hm one_ne_zero hm0 hu

theorem l15_noncol_conic {q : R3 k} (hq : IsConic q) (hirr : Irreducible q) {a b c : P2 k}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (ha : Vanishes q a) (hb : Vanishes q b)
    (hc : Vanishes q c) : ¬ PCollinear a b c := by
  rw [l15_pcol_iff, dotProduct_comm]
  unfold Vanishes at ha hb hc
  rw [l14b_eval2 hq.1] at ha hb hc
  exact PlaneCubic.noncollinear_of_irreducible (l14b_irr hq.1 (l15_irr hq hirr))
    (l14b_cross (l15_li hab)) (l14b_cross (l15_li hac)) (l14b_cross (l15_li hbc)) ha hb hc

/-- Core Cayley–Bacharach in the writer's encoding (no `F ≠ 0` needed). -/
theorem l15_cb (F₁ F₂ F : R3 k) (h₁ : IsCubic F₁) (h₂ : IsCubic F₂) (hcop : IsRelPrime F₁ F₂)
    (P : Fin 9 → P2 k) (hP : Function.Injective P)
    (hP₁ : ∀ i, Vanishes F₁ (P i)) (hP₂ : ∀ i, Vanishes F₂ (P i))
    (hF : F.IsHomogeneous 3) (hF8 : ∀ i : Fin 9, i ≠ 8 → Vanishes F (P i)) :
    Vanishes F (P 8) :=
  l14_cayley_bacharach_of_no_common_factor_any (fun i => (P i).rep) (l15_pair hP) F₁ F₂ h₁.1
    h₂.1 (l15_indep h₁ h₂ hcop) hP₁ hP₂ (l15_lin hcop) (l15_con hcop) F hF
    (fun i => hF8 _ (Fin.castSucc_lt_last i).ne)

/-! ### CB1 -/

theorem cov_CB1_a : classical_CB1_a (k := k) := by
  intro F₁ F₂ F h₁ h₂ hcop P hP hP₁ hP₂ hF hF8
  exact l15_cb F₁ F₂ F h₁ h₂ hcop P hP hP₁ hP₂ hF.1 hF8

theorem cov_CB1_a_linear : classical_CB1_a_linear (k := k) := by
  intro F₁ F₂ F h₁ h₂ hcop P hP hP₁ hP₂ hF hF8
  have hp := l14b_pairwise (l15_pair hP)
  by_cases hK : PlaneCubic.AtLeastThree k
  · have hp' : ∀ i j : Fin 8, i ≠ j →
        (P (Fin.castSucc i)).rep ⨯₃ (P (Fin.castSucc j)).rep ≠ 0 :=
      fun i j hij => hp _ _ (fun h => hij (Fin.castSucc_injective _ h))
    have e1 : ∀ i, PlaneCubic.eval (cv E3 F₁) (P i).rep = 0 := fun i => by
      rw [← l14b_eval3 h₁.1]; exact hP₁ i
    have e2 : ∀ i, PlaneCubic.eval (cv E3 F₂) (P i).rep = 0 := fun i => by
      rw [← l14b_eval3 h₂.1]; exact hP₂ i
    obtain ⟨h4, hcon8⟩ := PlaneCubic.general_position_of_no_common_factor
      (fun i : Fin 8 => (P (Fin.castSucc i)).rep) hp' _ _ (fun i => e1 _) (fun i => e2 _)
      ((l14b_lin h₁.1 h₂.1).1 (l15_lin hcop)) ((l14b_con h₁.1 h₂.1).1 (l15_con hcop))
    have hmem := PlaneCubic.mem_span_of_eight (fun i => (P i).rep) hp
      (fun ℓ hℓ s hs => (h4 ℓ hℓ s hs).trans (by decide)) hcon8 _ _
      (l14b_linIndep h₁.1 h₂.1 (l15_indep h₁ h₂ hcop)) e1 e2 (cv E3 F)
      (fun i => by rw [← l14b_eval3 hF.1]; exact hF8 _ (Fin.castSucc_lt_last i).ne)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 hmem
    refine ⟨c 0, c 1, ?_⟩
    rw [Fin.sum_univ_two] at hc
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hc
    rw [← cv3 hF.1, ← hc, toP_add, toP_smul, toP_smul, cv3 h₁.1, cv3 h₂.1,
      MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul]
  · exact absurd (PlaneCubic.card_le_seven_of_not_atLeastThree hK _ hp) (by norm_num)

/-! ### CB2 -/

theorem cov_CB2_a : classical_CB2_a (k := k) := by
  intro P hP
  obtain ⟨hinj, h4, h7⟩ := hP
  refine (l14_finrank_eq_two_iff (fun i => (P i).rep) (l15_pair hinj)).2 ⟨?_, ?_⟩
  · intro ℓ hℓ h0 s hs
    by_contra hlt
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (show 4 ≤ s.card by omega)
    exact h4 t htc ⟨ℓ, ⟨hℓ, h0⟩, fun i hi => hs i (hts hi)⟩
  · intro q hq hv
    by_contra h0
    exact h7 (Finset.univ.erase 0) (by rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp)
      ⟨q, ⟨hq, h0⟩, fun i _ => hv i⟩

/-- Existence half of `classical_CB2_b_distinct` (the ninth point is `Q`). -/
theorem cov_CB2_b_distinct_part (P : Fin 8 → P2 k) (hP : EightPointGeneral P)
    (F₁ F₂ : R3 k) (hF₁ : F₁ ∈ cubicsThrough P) (hF₂ : F₂ ∈ cubicsThrough P)
    (h₁ : F₁ ≠ 0) (h₂ : F₂ ≠ 0) (hcop : IsRelPrime F₁ F₂)
    (Q : P2 k) (hQ : Q ∉ Set.range P) (hQ₁ : Vanishes F₁ Q) (hQ₂ : Vanishes F₂ Q) :
    ∃ P₉ : P2 k, P₉ ∉ Set.range P ∧ ∀ F ∈ cubicsThrough P, Vanishes F P₉ := by
  obtain ⟨hF₁3, hF₁v⟩ := l15_mem.1 hF₁
  obtain ⟨hF₂3, hF₂v⟩ := l15_mem.1 hF₂
  refine ⟨Q, hQ, fun F hF => ?_⟩
  obtain ⟨hF3, hFv⟩ := l15_mem.1 hF
  have hinj : Function.Injective (Fin.snoc P Q : Fin 9 → P2 k) :=
    Fin.snoc_injective_iff.2 ⟨hP.1, hQ⟩
  have key : Vanishes F ((Fin.snoc P Q : Fin 9 → P2 k) 8) :=
    l15_cb F₁ F₂ F ⟨hF₁3, h₁⟩ ⟨hF₂3, h₂⟩ hcop (Fin.snoc P Q) hinj
      (fun i => by
        induction i using Fin.lastCases with
        | last => rw [Fin.snoc_last]; exact hQ₁
        | cast j => simpa using hF₁v j)
      (fun i => by
        induction i using Fin.lastCases with
        | last => rw [Fin.snoc_last]; exact hQ₂
        | cast j => simpa using hF₂v j)
      hF3
      (fun i hi => by
        induction i using Fin.lastCases with
        | last => exact absurd rfl hi
        | cast j => simpa using hFv j)
  rw [show (8 : Fin 9) = Fin.last 8 from rfl, Fin.snoc_last] at key
  exact key

/-! ### CB3 -/

theorem cov_CB3_a_part (hK : ∃ s : Finset k, 10 < s.card) : classical_CB3_a (k := k) := by
  intro q hq hirr A B C D E F hdist hA hB hC hD hE hF X Y Z hX hY hZ
  simp only [l15_pcol_iff] at hX hY hZ ⊢
  have e : ∀ i, (![A, B, C, D, E, F] i).rep = ![A.rep, B.rep, C.rep, D.rep, E.rep, F.rep] i := by
    intro i; fin_cases i <;> rfl
  have hpair : ∀ i j, i ≠ j → LinearIndependent k
      ![![A.rep, B.rep, C.rep, D.rep, E.rep, F.rep] i,
        ![A.rep, B.rep, C.rep, D.rep, E.rep, F.rep] j] := by
    intro i j hij; rw [← e, ← e]; exact l15_li (fun h => hij (hdist h))
  exact l15_col_of _ _ _ (l14_pascal_points hK A.rep B.rep C.rep D.rep E.rep F.rep hpair q hq.1
    (l15_irr hq hirr) hA hB hC hD hE hF X.rep Y.rep Z.rep
    (l15_det_of _ _ _ hX.1) (l15_det_of _ _ _ hX.2) (l15_det_of _ _ _ hY.1)
    (l15_det_of _ _ _ hY.2) (l15_det_of _ _ _ hZ.1) (l15_det_of _ _ _ hZ.2))

theorem cov_CB3_a_obligation : classical_CB3_a_obligation (k := k) := by
  intro q hq hirr A B C D E F hdist hA hB hC hD hE hF
  have d : ∀ i j : Fin 6, i ≠ j → ![A, B, C, D, E, F] i ≠ ![A, B, C, D, E, F] j :=
    fun i j h e => h (hdist e)
  refine ⟨l15_meet A B D E ?_ ?_, l15_meet B C E F ?_ ?_, l15_meet C D F A ?_ ?_⟩
  · exact l15_noncol_conic hq hirr (d 0 1 (by decide)) (d 0 3 (by decide)) (d 1 3 (by decide)) hA hB hD
  · exact l15_noncol_conic hq hirr (d 3 4 (by decide)) (d 3 0 (by decide)) (d 4 0 (by decide)) hD hE hA
  · exact l15_noncol_conic hq hirr (d 1 2 (by decide)) (d 1 4 (by decide)) (d 2 4 (by decide)) hB hC hE
  · exact l15_noncol_conic hq hirr (d 4 5 (by decide)) (d 4 1 (by decide)) (d 5 1 (by decide)) hE hF hB
  · exact l15_noncol_conic hq hirr (d 2 3 (by decide)) (d 2 5 (by decide)) (d 3 5 (by decide)) hC hD hF
  · exact l15_noncol_conic hq hirr (d 5 0 (by decide)) (d 5 2 (by decide)) (d 0 2 (by decide)) hF hA hC

theorem cov_CB3_b_obligation : classical_CB3_b_obligation (k := k) := by
  intro A B C D E F hgen
  exact ⟨l15_meet A B D E (hgen 0 1 3 (by decide) (by decide) (by decide))
      (hgen 3 4 0 (by decide) (by decide) (by decide)),
    l15_meet B C E F (hgen 1 2 4 (by decide) (by decide) (by decide))
      (hgen 4 5 1 (by decide) (by decide) (by decide)),
    l15_meet C D F A (hgen 2 3 5 (by decide) (by decide) (by decide))
      (hgen 5 0 2 (by decide) (by decide) (by decide))⟩

/-! ### CB4 -/

theorem cov_CB4_a_part (hK : ∃ s : Finset k, 10 < s.card) : classical_CB4_a (k := k) := by
  intro l m hl hm hlm A B C A' B' C' hA hB hC hA' hB' hC' hABC hABC' hoff X Y Z hX hY hZ
  obtain ⟨hmA, hmB, hmC, hlA', hlB', hlC'⟩ := hoff
  simp only [l15_pcol_iff] at hX hY hZ ⊢
  unfold Vanishes at hA hB hC hA' hB' hC' hmA hmB hmC hlA' hlB' hlC'
  rw [l14b_eval1 hl.1] at hA hB hC hlA' hlB' hlC'
  rw [l14b_eval1 hm.1] at hA' hB' hC' hmA hmB hmC
  exact l15_col_of' _ _ _ (l14_pappus_points hK A.rep B'.rep C.rep A'.rep B.rep C'.rep
    (cv E1 l) (cv E1 m) hA hC hB hB' hA' hC' hmA hmC hmB hlB' hlA' hlC'
    (l15_li hABC.2.2) (l15_li hABC.1) (l15_li hABC.2.1.symm) (l15_li hABC'.1.symm)
    (l15_li hABC'.2.1) (l15_li hABC'.2.2) X.rep Z.rep Y.rep
    (l15_det_of _ _ _ hX.1) (l15_det_of _ _ _ hX.2) (l15_det_of _ _ _ hZ.2)
    (l15_det_of _ _ _ hZ.1) (l15_det_of' _ _ _ hY.2) (l15_det_of' _ _ _ hY.1))

theorem cov_CB4_a_obligation : classical_CB4_a_obligation (k := k) := by
  intro l m hl hm hlm A B C A' B' C' hA hB hC hA' hB' hC' hABC hABC' hoff
  obtain ⟨hmA, hmB, hmC, hlA', hlB', hlC'⟩ := hoff
  obtain ⟨hAB, hBC, hAC⟩ := hABC
  obtain ⟨hAB', hBC', hAC'⟩ := hABC'
  exact ⟨l15_meet A B' A' B (l15_noncol_line hm hB' hA' (Ne.symm hAB') hmA)
      (l15_noncol_line hl hB hA (Ne.symm hAB) hlA'),
    l15_meet A C' A' C (l15_noncol_line hm hC' hA' (Ne.symm hAC') hmA)
      (l15_noncol_line hl hC hA (Ne.symm hAC) hlA'),
    l15_meet B C' B' C (l15_noncol_line hm hC' hB' (Ne.symm hBC') hmB)
      (l15_noncol_line hl hC hB (Ne.symm hBC) hlB')⟩

theorem cov_CB4_b_part (hK : ∃ s : Finset k, 10 < s.card) : classical_CB4_b (k := k) := by
  intro l m hl hm V hL hM hlm hV hoff X Y Z hX hY hZ
  obtain ⟨h0, h2, h4⟩ := hL
  obtain ⟨h1, h3, h5⟩ := hM
  obtain ⟨n0, n2, n4, n1, n3, n5⟩ := hoff
  simp only [l15_pcol_iff] at hX hY hZ ⊢
  unfold Vanishes at h0 h1 h2 h3 h4 h5 n0 n1 n2 n3 n4 n5
  rw [l14b_eval1 hl.1] at h0 h2 h4 n1 n3 n5
  rw [l14b_eval1 hm.1] at h1 h3 h5 n0 n2 n4
  have d : ∀ i j : Fin 6, i ≠ j → V i ≠ V j := fun i j h e => h (hV e)
  exact l15_col_of _ _ _ (l14_pappus_points hK (V 0).rep (V 1).rep (V 2).rep (V 3).rep
    (V 4).rep (V 5).rep (cv E1 l) (cv E1 m) h0 h2 h4 h1 h3 h5 n0 n2 n4 n1 n3 n5
    (l15_li (d 0 2 (by decide))) (l15_li (d 0 4 (by decide))) (l15_li (d 2 4 (by decide)))
    (l15_li (d 1 3 (by decide))) (l15_li (d 1 5 (by decide))) (l15_li (d 3 5 (by decide)))
    X.rep Y.rep Z.rep
    (l15_det_of _ _ _ hX.1) (l15_det_of _ _ _ hX.2) (l15_det_of _ _ _ hY.1)
    (l15_det_of _ _ _ hY.2) (l15_det_of _ _ _ hZ.1) (l15_det_of _ _ _ hZ.2))

theorem cov_CB4_b_obligation : classical_CB4_b_obligation (k := k) := by
  intro l m hl hm V hL hM hlm hV hoff
  obtain ⟨h0, h2, h4⟩ := hL
  obtain ⟨h1, h3, h5⟩ := hM
  obtain ⟨n0, n2, n4, n1, n3, n5⟩ := hoff
  have d : ∀ i j : Fin 6, i ≠ j → V i ≠ V j := fun i j h e => h (hV e)
  exact ⟨l15_meet (V 0) (V 1) (V 3) (V 4) (l15_noncol_line hm h1 h3 (d 1 3 (by decide)) n0)
      (l15_noncol_line hl h4 h0 (d 4 0 (by decide)) n3),
    l15_meet (V 1) (V 2) (V 4) (V 5) (l15_noncol_line hl h2 h4 (d 2 4 (by decide)) n1)
      (l15_noncol_line hm h5 h1 (d 5 1 (by decide)) n4),
    l15_meet (V 2) (V 3) (V 5) (V 0) (l15_noncol_line hm h3 h5 (d 3 5 (by decide)) n2)
      (l15_noncol_line hl h0 h2 (d 0 2 (by decide)) n5)⟩

/-! ### NEW PROOF: Pappus over every field (no `|K| > 10`), via an explicit polynomial identity -/

theorem l15_papid (A B A' B' : Fin 3 → k) (s t s' t' : k) :
    ((A ⨯₃ B') ⨯₃ (A' ⨯₃ B)) ⬝ᵥ (((A ⨯₃ (s' • A' + t' • B')) ⨯₃ (A' ⨯₃ (s • A + t • B))) ⨯₃
      ((B ⨯₃ (s' • A' + t' • B')) ⨯₃ (B' ⨯₃ (s • A + t • B)))) = 0 := by
  simp only [cross_apply, dotProduct, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

theorem l15_cross_ne {P Q R S : Fin 3 → k} (h1 : R ⬝ᵥ P ⨯₃ Q ≠ 0) (h2 : P ⬝ᵥ R ⨯₃ S ≠ 0) :
    P ⨯₃ Q ⨯₃ (R ⨯₃ S) ≠ 0 := by
  have hv : R ⨯₃ S ≠ 0 := by intro hv; apply h2; rw [hv, dotProduct_zero]
  intro h0
  obtain ⟨c, hc⟩ := (PlaneCubic.cross_eq_zero_iff_eq_smul hv).1 h0
  apply h1; rw [hc, dotProduct_smul, dot_self_cross, smul_zero]

/-- `U ⬝ (W × V) ≠ 0` when `U ≠ V` lie on the line `m = 0` and `W` does not. -/
theorem l15_tri_ne {m : R3 k} (hm : IsLine m) {W U V : P2 k} (hU : Vanishes m U)
    (hV : Vanishes m V) (hUV : U ≠ V) (hW : ¬ Vanishes m W) :
    U.rep ⬝ᵥ W.rep ⨯₃ V.rep ≠ 0 := by
  have h := l15_noncol_line hm hU hV hUV hW
  rw [l15_pcol_iff] at h
  intro h0; apply h
  rw [triple_product_permutation] at h0
  rw [← cross_anticomm, dotProduct_neg, ← triple_product_permutation, h0, neg_zero]

theorem l15_on_line {l : R3 k} (hl : IsLine l) {A B C : P2 k} (hA : Vanishes l A)
    (hB : Vanishes l B) (hC : Vanishes l C) (hAB : A ≠ B) :
    ∃ s t : k, C.rep = s • A.rep + t • B.rep := by
  unfold Vanishes at hA hB hC
  rw [l14b_eval1 hl.1] at hA hB hC
  have huv := l14b_cross (l15_li hAB)
  obtain ⟨c, hc⟩ := PlaneCubic.lin_two huv hA hB
  have hc0 : c ≠ 0 := by
    rintro rfl; apply l14b_cv1_ne hl.1 hl.2; rw [hc, zero_smul]
  apply PlaneCubic.exists_smul_add_smul huv
  rw [hc, smul_dotProduct, smul_eq_mul] at hC
  exact (mul_eq_zero.mp hC).resolve_left hc0

theorem l15_pappus_core {l m : R3 k} (hl : IsLine l) (hm : IsLine m) {A B C A' B' C' : P2 k}
    (hA : Vanishes l A) (hB : Vanishes l B) (hC : Vanishes l C)
    (hA' : Vanishes m A') (hB' : Vanishes m B') (hC' : Vanishes m C')
    (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C) (hAB' : A' ≠ B') (hBC' : B' ≠ C') (hAC' : A' ≠ C')
    (nA : ¬ Vanishes m A) (nB : ¬ Vanishes m B) (nA' : ¬ Vanishes l A') (nB' : ¬ Vanishes l B')
    {X Y Z : P2 k}
    (hX1 : X.rep ⬝ᵥ A.rep ⨯₃ B'.rep = 0) (hX2 : X.rep ⬝ᵥ A'.rep ⨯₃ B.rep = 0)
    (hY1 : Y.rep ⬝ᵥ A.rep ⨯₃ C'.rep = 0) (hY2 : Y.rep ⬝ᵥ A'.rep ⨯₃ C.rep = 0)
    (hZ1 : Z.rep ⬝ᵥ B.rep ⨯₃ C'.rep = 0) (hZ2 : Z.rep ⬝ᵥ B'.rep ⨯₃ C.rep = 0) :
    Z.rep ⬝ᵥ X.rep ⨯₃ Y.rep = 0 := by
  obtain ⟨x, hx⟩ := l14b_on_two (l15_cross_ne (l15_tri_ne hm hA' hB' hAB' nA)
    (l15_tri_ne hl hA hB hAB nA')) hX1 hX2
  obtain ⟨y, hy⟩ := l14b_on_two (l15_cross_ne (l15_tri_ne hm hA' hC' hAC' nA)
    (l15_tri_ne hl hA hC hAC nA')) hY1 hY2
  obtain ⟨z, hz⟩ := l14b_on_two (l15_cross_ne (l15_tri_ne hm hB' hC' hBC' nB)
    (l15_tri_ne hl hB hC hBC nB')) hZ1 hZ2
  obtain ⟨s, t, hc⟩ := l15_on_line hl hA hB hC hAB
  obtain ⟨s', t', hc'⟩ := l15_on_line hm hA' hB' hC' hAB'
  rw [hx, hy, hz, LinearMap.map_smul, LinearMap.map_smul, LinearMap.smul_apply,
    smul_dotProduct, dotProduct_smul, dotProduct_smul, triple_product_permutation, hc, hc',
    l15_papid]
  simp

theorem l15_pcol_flip (P Q X : P2 k) (h : PCollinear P Q X) : X.rep ⬝ᵥ Q.rep ⨯₃ P.rep = 0 := by
  rw [l15_pcol_iff] at h
  rw [← cross_anticomm, dotProduct_neg, h, neg_zero]

/-- **NEW PROOF.** `classical_CB4_a` over every field. -/
theorem cov_CB4_a : classical_CB4_a (k := k) := by
  intro l m hl hm hlm A B C A' B' C' hA hB hC hA' hB' hC' hABC hABC' hoff X Y Z hX hY hZ
  obtain ⟨hmA, hmB, hmC, hlA', hlB', hlC'⟩ := hoff
  simp only [l15_pcol_iff] at hX hY hZ ⊢
  exact l15_pappus_core hl hm hA hB hC hA' hB' hC' hABC.1 hABC.2.1 hABC.2.2 hABC'.1 hABC'.2.1
    hABC'.2.2 hmA hmB hlA' hlB' hX.1 hX.2 hY.1 hY.2 hZ.1 hZ.2

/-- **NEW PROOF.** `classical_CB4_b` over every field. -/
theorem cov_CB4_b : classical_CB4_b (k := k) := by
  intro l m hl hm V hL hM hlm hV hoff X Y Z hX hY hZ
  obtain ⟨h0, h2, h4⟩ := hL
  obtain ⟨h1, h3, h5⟩ := hM
  obtain ⟨n0, n2, n4, n1, n3, n5⟩ := hoff
  have d : ∀ i j : Fin 6, i ≠ j → V i ≠ V j := fun i j h e => h (hV e)
  -- A = V0, B = V4, C = V2 on L; A' = V3, B' = V1, C' = V5 on M
  have core := l15_pappus_core hl hm h0 h4 h2 h3 h1 h5 (d 0 4 (by decide)) (d 4 2 (by decide))
    (d 0 2 (by decide)) (d 3 1 (by decide)) (d 1 5 (by decide)) (d 3 5 (by decide)) n0 n4 n3 n1
    (Z := Y) ((l15_pcol_iff _ _ _).1 hX.1) ((l15_pcol_iff _ _ _).1 hX.2)
    (l15_pcol_flip _ _ _ hZ.2) (l15_pcol_flip _ _ _ hZ.1)
    ((l15_pcol_iff _ _ _).1 hY.2) ((l15_pcol_iff _ _ _).1 hY.1)
  rw [l15_pcol_iff]
  rw [triple_product_permutation, ← cross_anticomm, dotProduct_neg, neg_eq_zero] at core
  rw [triple_product_permutation]; exact core

/-! ### NEW PROOF: Braikenridge–Maclaurin (CB3(b)) over every field, explicit conic -/

/-- The bilinear form whose diagonal is the Braikenridge–Maclaurin conic through `A,…,E`:
`p ↦ [X, (BC ∩ Ep), (CD ∩ pA)]` with `X = AB ∩ DE`. -/
def l15Qb (A B C D E p p' : Fin 3 → k) : k :=
  (A ⨯₃ B ⨯₃ (D ⨯₃ E)) ⬝ᵥ ((B ⨯₃ C ⨯₃ (E ⨯₃ p)) ⨯₃ (C ⨯₃ D ⨯₃ (p' ⨯₃ A)))

def l15e3 (i : Fin 3) : Fin 3 → k := Pi.single i 1

theorem l15Qb_quad (A B C D E v : Fin 3 → k) : l15Qb A B C D E v v =
    l15Qb A B C D E (l15e3 0) (l15e3 0) * v 0 ^ 2 +
    (l15Qb A B C D E (l15e3 0) (l15e3 1) + l15Qb A B C D E (l15e3 1) (l15e3 0)) * (v 0 * v 1) +
    (l15Qb A B C D E (l15e3 0) (l15e3 2) + l15Qb A B C D E (l15e3 2) (l15e3 0)) * (v 0 * v 2) +
    l15Qb A B C D E (l15e3 1) (l15e3 1) * v 1 ^ 2 +
    (l15Qb A B C D E (l15e3 1) (l15e3 2) + l15Qb A B C D E (l15e3 2) (l15e3 1)) * (v 1 * v 2) +
    l15Qb A B C D E (l15e3 2) (l15e3 2) * v 2 ^ 2 := by
  have hv : v = v 0 • l15e3 0 + v 1 • l15e3 1 + v 2 • l15e3 2 := by
    ext i; fin_cases i <;> simp [l15e3]
  have key : l15Qb A B C D E v v = l15Qb A B C D E (v 0 • l15e3 0 + v 1 • l15e3 1 + v 2 • l15e3 2)
      (v 0 • l15e3 0 + v 1 • l15e3 1 + v 2 • l15e3 2) := by rw [← hv]
  rw [key]
  simp only [l15Qb, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, dotProduct_add,
    dotProduct_smul, smul_eq_mul]
  ring

theorem l15Qb_A (A B C D E : Fin 3 → k) : l15Qb A B C D E A A = 0 := by
  simp [l15Qb, cross_self]

theorem l15Qb_E (A B C D E : Fin 3 → k) : l15Qb A B C D E E E = 0 := by
  simp [l15Qb, cross_self]

theorem l15Qb_B (A B C D E : Fin 3 → k) : l15Qb A B C D E B B = 0 := by
  simp only [l15Qb, cross_apply, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem l15Qb_C (A B C D E : Fin 3 → k) : l15Qb A B C D E C C = 0 := by
  simp only [l15Qb, cross_apply, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem l15Qb_D (A B C D E : Fin 3 → k) : l15Qb A B C D E D D = 0 := by
  simp only [l15Qb, cross_apply, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem l15Qb_AB (A B C D E : Fin 3 → k) : l15Qb A B C D E (A + B) (A + B) =
    (A ⬝ᵥ B ⨯₃ C) * (A ⬝ᵥ B ⨯₃ D) * (A ⬝ᵥ B ⨯₃ E) * (C ⬝ᵥ D ⨯₃ E) := by
  simp only [l15Qb, cross_apply, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Pi.add_apply]
  ring

/-- The coefficient vector (library order `x², xy, xz, y², yz, z²`) of the BM conic. -/
def l15Qc (A B C D E : Fin 3 → k) : Fin 6 → k :=
  ![l15Qb A B C D E (l15e3 0) (l15e3 0),
    l15Qb A B C D E (l15e3 0) (l15e3 1) + l15Qb A B C D E (l15e3 1) (l15e3 0),
    l15Qb A B C D E (l15e3 0) (l15e3 2) + l15Qb A B C D E (l15e3 2) (l15e3 0),
    l15Qb A B C D E (l15e3 1) (l15e3 1),
    l15Qb A B C D E (l15e3 1) (l15e3 2) + l15Qb A B C D E (l15e3 2) (l15e3 1),
    l15Qb A B C D E (l15e3 2) (l15e3 2)]

theorem l15_eval_Qc (A B C D E v : Fin 3 → k) :
    MvPolynomial.eval v (toP E2 (l15Qc A B C D E)) = l15Qb A B C D E v v := by
  rw [eval_toP2, PlaneCubic.evalC_expand, l15Qb_quad]
  simp [l15Qc]

theorem l15_tri (a b c : P2 k) (h : ¬ PCollinear a b c) : a.rep ⬝ᵥ b.rep ⨯₃ c.rep ≠ 0 := by
  rw [l15_pcol_iff] at h
  rwa [triple_product_permutation, triple_product_permutation]

theorem l15_tri' (a b c : P2 k) (h : ¬ PCollinear a b c) : c.rep ⬝ᵥ a.rep ⨯₃ b.rep ≠ 0 := by
  rw [l15_pcol_iff] at h; exact h

/-- **NEW PROOF.** `classical_CB3_b` (Braikenridge–Maclaurin) over every field. -/
theorem cov_CB3_b : classical_CB3_b (k := k) := by
  intro A B C D E F hgen X Y Z hX hY hZ hXYZ
  have g : ∀ i j l : Fin 6, i ≠ j → i ≠ l → j ≠ l →
      ¬ PCollinear (![A, B, C, D, E, F] i) (![A, B, C, D, E, F] j) (![A, B, C, D, E, F] l) := hgen
  set a := A.rep; set b := B.rep; set c := C.rep; set d := D.rep; set e := E.rep; set f := F.rep
  refine ⟨toP E2 (l15Qc a b c d e), ⟨toP_isHomogeneous E2 E2_deg _, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h0
    have := l15_eval_Qc a b c d e (a + b)
    rw [h0, map_zero, l15Qb_AB] at this
    have n1 := l15_tri A B C (g 0 1 2 (by decide) (by decide) (by decide))
    have n2 := l15_tri A B D (g 0 1 3 (by decide) (by decide) (by decide))
    have n3 := l15_tri A B E (g 0 1 4 (by decide) (by decide) (by decide))
    have n4 := l15_tri C D E (g 2 3 4 (by decide) (by decide) (by decide))
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero n1 n2) n3) n4) this.symm
  · unfold Vanishes; rw [l15_eval_Qc]; exact l15Qb_A _ _ _ _ _
  · unfold Vanishes; rw [l15_eval_Qc]; exact l15Qb_B _ _ _ _ _
  · unfold Vanishes; rw [l15_eval_Qc]; exact l15Qb_C _ _ _ _ _
  · unfold Vanishes; rw [l15_eval_Qc]; exact l15Qb_D _ _ _ _ _
  · unfold Vanishes; rw [l15_eval_Qc]; exact l15Qb_E _ _ _ _ _
  · unfold Vanishes; rw [l15_eval_Qc]
    rw [l15_pcol_iff, l15_pcol_iff] at hX hY hZ
    obtain ⟨x, hx⟩ := l14b_on_two (l15_cross_ne
      (l15_tri' A B D (g 0 1 3 (by decide) (by decide) (by decide)))
      (l15_tri' D E A (g 3 4 0 (by decide) (by decide) (by decide)))) hX.1 hX.2
    obtain ⟨y, hy⟩ := l14b_on_two (l15_cross_ne
      (l15_tri' B C E (g 1 2 4 (by decide) (by decide) (by decide)))
      (l15_tri' E F B (g 4 5 1 (by decide) (by decide) (by decide)))) hY.1 hY.2
    obtain ⟨z, hz⟩ := l14b_on_two (l15_cross_ne
      (l15_tri' C D F (g 2 3 5 (by decide) (by decide) (by decide)))
      (l15_tri' F A C (g 5 0 2 (by decide) (by decide) (by decide)))) hZ.1 hZ.2
    have hx0 : x ≠ 0 := by rintro rfl; exact X.rep_nonzero (by rw [hx, zero_smul])
    have hy0 : y ≠ 0 := by rintro rfl; exact Y.rep_nonzero (by rw [hy, zero_smul])
    have hz0 : z ≠ 0 := by rintro rfl; exact Z.rep_nonzero (by rw [hz, zero_smul])
    have h := l15_tri' X Y Z
    rw [l15_pcol_iff] at hXYZ
    rw [triple_product_permutation, triple_product_permutation, hx, hy, hz,
      LinearMap.map_smul, LinearMap.map_smul, LinearMap.smul_apply, smul_dotProduct,
      dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at hXYZ
    have := (mul_eq_zero.mp hXYZ).resolve_left hy0
    have := (mul_eq_zero.mp this).resolve_left hx0
    have h3 := (mul_eq_zero.mp this).resolve_left hz0
    unfold l15Qb
    rw [triple_product_permutation]; exact h3

/-! ### NEW PROOF: Pascal (CB3(a)) over every field, via the BM conic and `conics_le_one` -/

theorem l15_not_col4 {x y z w : Fin 3 → k} (hxy : x ⨯₃ y ≠ 0) (h : x ⨯₃ y ⬝ᵥ z ≠ 0) :
    ¬ PlaneCubic.Col4 x y z w := by
  rintro ⟨M, hM, ha, hb, hc, -⟩
  obtain ⟨c', rfl⟩ := PlaneCubic.lin_two hxy ha hb
  have hc0 : c' ≠ 0 := by rintro rfl; exact hM (zero_smul _ _)
  rw [smul_dotProduct, smul_eq_mul] at hc
  exact h ((mul_eq_zero.mp hc).resolve_left hc0)

theorem l15_evalC_Qc (A B C D E v : Fin 3 → k) :
    PlaneCubic.evalC (l15Qc A B C D E) v = l15Qb A B C D E v v := by
  rw [← eval_toP2, l15_eval_Qc]

/-- **NEW PROOF.** `classical_CB3_a` (Pascal) over every field. -/
theorem cov_CB3_a : classical_CB3_a (k := k) := by
  intro q hq hirr A B C D E F hdist hA hB hC hD hE hF X Y Z hX hY hZ
  have dd : ∀ i j : Fin 6, i ≠ j → ![A, B, C, D, E, F] i ≠ ![A, B, C, D, E, F] j :=
    fun i j h e => h (hdist e)
  have hirr' := l14b_irr hq.1 (l15_irr hq hirr)
  set qc := cv E2 q
  have ev : ∀ P : P2 k, Vanishes q P → PlaneCubic.evalC qc P.rep = 0 := fun P h => by
    unfold Vanishes at h; rwa [l14b_eval2 hq.1] at h
  set a := A.rep; set b := B.rep; set c := C.rep; set d := D.rep; set e := E.rep; set f := F.rep
  have cr : ∀ i j : Fin 6, i ≠ j →
      (![A, B, C, D, E, F] i).rep ⨯₃ (![A, B, C, D, E, F] j).rep ≠ 0 :=
    fun i j h => l14b_cross (l15_li (dd i j h))
  have nc : ∀ i j l : Fin 6, i ≠ j → i ≠ l → j ≠ l →
      (![A, B, C, D, E, F] i).rep ⨯₃ (![A, B, C, D, E, F] j).rep ⬝ᵥ
        (![A, B, C, D, E, F] l).rep ≠ 0 := by
    intro i j l hij hil hjl
    have hv : ∀ i, Vanishes q (![A, B, C, D, E, F] i) := by
      intro i; fin_cases i
      exacts [hA, hB, hC, hD, hE, hF]
    exact PlaneCubic.noncollinear_of_irreducible hirr' (cr i j hij) (cr i l hil) (cr j l hjl)
      (ev _ (hv i)) (ev _ (hv j)) (ev _ (hv l))
  -- the conics through `a, b, c, d, e` form a space of dimension ≤ 1
  have hdim : Module.finrank k (PlaneCubic.conicsThrough ({a, b, c, d, e} : Set (Fin 3 → k)))
      ≤ 1 :=
    PlaneCubic.conics_le_one (d := a) (e := b) (f := c) (g := d) (h := e) _ (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]) (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true])
      (cr 0 1 (by decide)) (cr 0 2 (by decide)) (cr 0 3 (by decide)) (cr 0 4 (by decide))
      (cr 1 2 (by decide)) (cr 1 3 (by decide)) (cr 1 4 (by decide))
      (cr 2 3 (by decide)) (cr 2 4 (by decide)) (cr 3 4 (by decide))
      (l15_not_col4 (cr 0 1 (by decide)) (nc 0 1 2 (by decide) (by decide) (by decide)))
      (l15_not_col4 (cr 0 1 (by decide)) (nc 0 1 2 (by decide) (by decide) (by decide)))
      (l15_not_col4 (cr 0 1 (by decide)) (nc 0 1 3 (by decide) (by decide) (by decide)))
      (l15_not_col4 (cr 0 2 (by decide)) (nc 0 2 3 (by decide) (by decide) (by decide)))
      (l15_not_col4 (cr 1 2 (by decide)) (nc 1 2 3 (by decide) (by decide) (by decide)))
  obtain ⟨v, hv⟩ := (finrank_le_one_iff).1 hdim
  have memq : qc ∈ PlaneCubic.conicsThrough ({a, b, c, d, e} : Set (Fin 3 → k)) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    exacts [ev _ hA, ev _ hB, ev _ hC, ev _ hD, ev _ hE]
  have memQ : l15Qc a b c d e ∈ PlaneCubic.conicsThrough ({a, b, c, d, e} : Set (Fin 3 → k)) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> rw [l15_evalC_Qc]
    exacts [l15Qb_A _ _ _ _ _, l15Qb_B _ _ _ _ _, l15Qb_C _ _ _ _ _, l15Qb_D _ _ _ _ _,
      l15Qb_E _ _ _ _ _]
  obtain ⟨c1, hc1⟩ := hv ⟨qc, memq⟩
  obtain ⟨c2, hc2⟩ := hv ⟨_, memQ⟩
  have hc1' : c1 • (v : Fin 6 → k) = qc := congrArg Subtype.val hc1
  have hc2' : c2 • (v : Fin 6 → k) = l15Qc a b c d e := congrArg Subtype.val hc2
  have hq0 : qc ≠ 0 := l14b_cv2_ne hq.1 hq.2
  have c10 : c1 ≠ 0 := by rintro rfl; rw [zero_smul] at hc1'; exact hq0 hc1'.symm
  have hvf : PlaneCubic.evalC (v : Fin 6 → k) f = 0 := by
    have := ev F hF
    rw [← hc1', PlaneCubic.evalC_smul] at this
    exact (mul_eq_zero.mp this).resolve_left c10
  have hQf : l15Qb a b c d e f f = 0 := by
    rw [← l15_evalC_Qc, ← hc2', PlaneCubic.evalC_smul, hvf, mul_zero]
  -- transfer to the given X, Y, Z
  simp only [l15_pcol_iff] at hX hY hZ ⊢
  have tri : ∀ i j l : Fin 6, i ≠ j → i ≠ l → j ≠ l →
      (![A, B, C, D, E, F] l).rep ⬝ᵥ (![A, B, C, D, E, F] i).rep ⨯₃
        (![A, B, C, D, E, F] j).rep ≠ 0 := by
    intro i j l hij hil hjl h0; apply nc i j l hij hil hjl
    rw [dotProduct_comm]; exact h0
  obtain ⟨x, hx⟩ := l14b_on_two (l15_cross_ne (tri 0 1 3 (by decide) (by decide) (by decide))
    (tri 3 4 0 (by decide) (by decide) (by decide))) hX.1 hX.2
  obtain ⟨y, hy⟩ := l14b_on_two (l15_cross_ne (tri 1 2 4 (by decide) (by decide) (by decide))
    (tri 4 5 1 (by decide) (by decide) (by decide))) hY.1 hY.2
  obtain ⟨z, hz⟩ := l14b_on_two (l15_cross_ne (tri 2 3 5 (by decide) (by decide) (by decide))
    (tri 5 0 2 (by decide) (by decide) (by decide))) hZ.1 hZ.2
  rw [hx, hy, hz, LinearMap.map_smul, LinearMap.map_smul, LinearMap.smul_apply, smul_dotProduct,
    dotProduct_smul, dotProduct_smul, triple_product_permutation]
  unfold l15Qb at hQf
  change z • y • x • ((a ⨯₃ b ⨯₃ (d ⨯₃ e)) ⬝ᵥ ((b ⨯₃ c ⨯₃ (e ⨯₃ f)) ⨯₃ (c ⨯₃ d ⨯₃ (f ⨯₃ a)))) = 0
  rw [hQf]; simp

/-! ### CB1(b): partial (distinct-points case), via a bridge for the writer's `intMult` -/

theorem l15_aeval_hom {F : R3 k} {d : ℕ} (hF : F.IsHomogeneous d) (v : Fin 3 → k) :
    MvPolynomial.aeval (fun i => Polynomial.C (v i) * Polynomial.X) F =
      Polynomial.C (MvPolynomial.eval v F) * Polynomial.X ^ d := by
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [MvPolynomial.aeval_monomial, MvPolynomial.eval_monomial, hF.degree_eq_sum_deg_support hs]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod,
    Finset.prod_pow_eq_pow_sum, Polynomial.algebraMap_eq, map_mul, mul_assoc]

theorem l15_mem_pointIdeal {F : R3 k} {d : ℕ} (hF : F.IsHomogeneous d) (v : Fin 3 → k) :
    F ∈ pointIdeal v ↔ MvPolynomial.eval v F = 0 := by
  unfold pointIdeal
  rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, l15_aeval_hom hF]
  constructor
  · intro h
    have := congrArg (Polynomial.coeff · d) h
    simpa using this
  · intro h; rw [h]; simp

/-- `intMult F G P ≠ 0` iff both forms vanish at `P`. -/
theorem l15_intMult_ne_zero_iff {F G : R3 k} {a b : ℕ} (hF : F.IsHomogeneous a)
    (hG : G.IsHomogeneous b) (P : P2 k) :
    intMult F G P ≠ 0 ↔ Vanishes F P ∧ Vanishes G P := by
  unfold intMult
  rw [ne_eq, Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff]
  have hm := fun x : R3 k => IsLocalization.AtPrime.to_map_mem_maximal_iff
    (Localization.AtPrime (pointIdeal P.rep)) (pointIdeal P.rep) x
  constructor
  · intro h
    by_contra hn
    apply h
    rcases not_and_or.1 hn with h1 | h1
    · rw [Vanishes, ← l15_mem_pointIdeal hF, ← hm] at h1
      exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_insert _ _))
        (by simpa [IsLocalRing.mem_maximalIdeal] using h1)
    · rw [Vanishes, ← l15_mem_pointIdeal hG, ← hm] at h1
      exact Ideal.eq_top_of_isUnit_mem _
        (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
        (by simpa [IsLocalRing.mem_maximalIdeal] using h1)
  · rintro ⟨h1, h2⟩ htop
    rw [Vanishes, ← l15_mem_pointIdeal hF, ← hm] at h1
    rw [Vanishes, ← l15_mem_pointIdeal hG, ← hm] at h2
    have : Ideal.span {algebraMap (R3 k) (Localization.AtPrime (pointIdeal P.rep)) F,
        algebraMap (R3 k) (Localization.AtPrime (pointIdeal P.rep)) G} ≤
        IsLocalRing.maximalIdeal _ := by
      rw [Ideal.span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      exacts [h1, h2]
    rw [htop] at this
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.1 this)


/-- **Partial CB1(b)** (any field, no `IsAlgClosed`, no simple-point hypothesis): if the
nine cycle points are distinct, then `Q = P₉`. -/
theorem cov_CB1_b_part (F₁ F₂ F : R3 k) (h₁ : IsCubic F₁) (h₂ : IsCubic F₂) (hF : IsCubic F)
    (hcop : IsRelPrime F₁ F₂) (P : Fin 9 → P2 k) (hP : Function.Injective P)
    (hcyc : ∀ X, intMult F₁ F₂ X = (Nat.card {i // P i = X} : ℕ∞))
    (Q : P2 k)
    (hcyc' : ∀ X, intMult F₁ F X =
      (Nat.card {i : Fin 8 // P i.castSucc = X} : ℕ∞) + (if Q = X then 1 else 0)) :
    Q = P 8 := by
  have v12 : ∀ i, Vanishes F₁ (P i) ∧ Vanishes F₂ (P i) := fun i => by
    rw [← l15_intMult_ne_zero_iff h₁.1 h₂.1, hcyc]
    have : 0 < Nat.card {j // P j = P i} :=
      Nat.card_pos_iff.2 ⟨⟨⟨i, rfl⟩⟩, inferInstance⟩
    exact_mod_cast this.ne'
  have vF : ∀ X, Vanishes F₁ X ∧ Vanishes F X ↔
      (∃ i : Fin 8, P i.castSucc = X) ∨ Q = X := fun X => by
    rw [← l15_intMult_ne_zero_iff h₁.1 hF.1, hcyc', ne_eq, add_eq_zero]
    have hc : (Nat.card {i : Fin 8 // P i.castSucc = X} : ℕ∞) = 0 ↔
        ¬ ∃ i : Fin 8, P i.castSucc = X := by
      rw [Nat.cast_eq_zero, Nat.card_eq_zero]
      constructor
      · rintro (h | h)
        · rintro ⟨i, hi⟩; exact h.false ⟨i, hi⟩
        · exact absurd h (not_infinite_iff_finite.2 inferInstance)
      · intro h; left; exact ⟨fun ⟨i, hi⟩ => h ⟨i, hi⟩⟩
    rw [hc]
    by_cases hQ : Q = X
    · simp [hQ]
    · simp [hQ]
  have hF8 : ∀ i : Fin 9, i ≠ 8 → Vanishes F (P i) := by
    intro i hi
    obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 hi
    exact ((vF _).2 (Or.inl ⟨j, rfl⟩)).2
  have h9 := l15_cb F₁ F₂ F h₁ h₂ hcop P hP (fun i => (v12 i).1) (fun i => (v12 i).2) hF.1 hF8
  rcases (vF (P 8)).1 ⟨(v12 8).1, h9⟩ with ⟨i, hi⟩ | hQ
  · exact absurd (hP hi) (Fin.castSucc_lt_last i).ne
  · exact hQ

/-- **Partial CB1(b), irreducible reading**: same distinct-points case. -/
theorem cov_CB1_b_irreducible_part (F₁ F₂ F : R3 k) (h₁ : IsCubic F₁) (h₂ : IsCubic F₂)
    (hF : IsCubic F) (hcop : IsRelPrime F₁ F₂) (_hirr : Irreducible F₁)
    (P : Fin 9 → P2 k) (hP : Function.Injective P)
    (hcyc : ∀ X, intMult F₁ F₂ X = (Nat.card {i // P i = X} : ℕ∞))
    (Q : P2 k)
    (hcyc' : ∀ X, intMult F₁ F X =
      (Nat.card {i : Fin 8 // P i.castSucc = X} : ℕ∞) + (if Q = X then 1 else 0)) :
    Q = P 8 :=
  cov_CB1_b_part F₁ F₂ F h₁ h₂ hF hcop P hP hcyc Q hcyc'

end CayleyBacharach.Classical

end
