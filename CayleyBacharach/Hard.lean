import CayleyBacharach.Through

/-!
# The hard direction of the general-position criterion
-/

open Matrix

namespace PlaneCubic

variable {K : Type*} [Field K]

theorem cross_dot_left (u v : Fin 3 → K) : u ⨯₃ v ⬝ᵥ u = 0 := by
  rw [dotProduct_comm]; exact dot_self_cross u v

theorem cross_dot_right (u v : Fin 3 → K) : u ⨯₃ v ⬝ᵥ v = 0 := by
  rw [dotProduct_comm]; exact dot_cross_self u v

theorem conicsThrough_anti {S T : Set (Fin 3 → K)} (h : S ⊆ T) :
    conicsThrough T ≤ conicsThrough S := fun _ hq v hv => hq v (h hv)

theorem cubicsThrough_anti {S T : Set (Fin 3 → K)} (h : S ⊆ T) :
    cubicsThrough T ≤ cubicsThrough S := fun _ hq v hv => hq v (h hv)

theorem linMul_eq_zero {ℓ m : Fin 3 → K} (hℓ : ℓ ≠ 0) (h : linMul ℓ m = 0) : m = 0 := by
  have E : ∀ i : Fin 6, linMul ℓ m i = 0 := fun i => by rw [h]; rfl
  have e0 : ℓ 0 * m 0 = 0 := by simpa [linMul] using E 0
  have e1 : ℓ 0 * m 1 + ℓ 1 * m 0 = 0 := by simpa [linMul] using E 1
  have e2 : ℓ 0 * m 2 + ℓ 2 * m 0 = 0 := by simpa [linMul] using E 2
  have e3 : ℓ 1 * m 1 = 0 := by simpa [linMul] using E 3
  have e4 : ℓ 1 * m 2 + ℓ 2 * m 1 = 0 := by simpa [linMul] using E 4
  have e5 : ℓ 2 * m 2 = 0 := by simpa [linMul] using E 5
  have key : m 0 = 0 ∧ m 1 = 0 ∧ m 2 = 0 := by
    by_cases h0 : ℓ 0 = 0
    · by_cases h1 : ℓ 1 = 0
      · have h2 : ℓ 2 ≠ 0 := by
          intro h2; apply hℓ; funext i; fin_cases i <;> simp [h0, h1, h2]
        have m2 : m 2 = 0 := by simpa [h2] using e5
        have m0 : m 0 = 0 := by simpa [h0, h2] using e2
        have m1 : m 1 = 0 := by simpa [h1, h2] using e4
        exact ⟨m0, m1, m2⟩
      · have m1 : m 1 = 0 := by simpa [h1] using e3
        have m0 : m 0 = 0 := by simpa [h0, h1] using e1
        have m2 : m 2 = 0 := by simpa [h1, m1] using e4
        exact ⟨m0, m1, m2⟩
    · have m0 : m 0 = 0 := by simpa [h0] using e0
      have m1 : m 1 = 0 := by simpa [h0, m0] using e1
      have m2 : m 2 = 0 := by simpa [h0, m0] using e2
      exact ⟨m0, m1, m2⟩
  obtain ⟨m0, m1, m2⟩ := key
  funext i; fin_cases i <;> simp [m0, m1, m2]

theorem ne_zero_of_cross {u v : Fin 3 → K} (h : u ⨯₃ v ≠ 0) : v ≠ 0 := by
  rintro rfl; simp at h

theorem ne_zero_of_cross' {u v : Fin 3 → K} (h : u ⨯₃ v ≠ 0) : u ≠ 0 := by
  rintro rfl; simp at h

theorem cross_add_right (u v : Fin 3 → K) : u ⨯₃ (u + v) = u ⨯₃ v := by
  ext i; fin_cases i <;> simp [cross_apply] <;> ring

theorem cross_add_right' (u v : Fin 3 → K) : v ⨯₃ (u + v) = -(u ⨯₃ v) := by
  ext i; fin_cases i <;> simp [cross_apply] <;> ring

theorem cross_add_dot (u v : Fin 3 → K) : u ⨯₃ v ⬝ᵥ (u + v) = 0 := by
  rw [dotProduct_add, cross_dot_left, cross_dot_right, add_zero]

/-- **C4.** Four distinct, not all collinear points impose at least 4 conditions on conics. -/
theorem conics_le_two {u v w z : Fin 3 → K} (T : Set (Fin 3 → K))
    (hu : u ∈ T) (hv : v ∈ T) (hw : w ∈ T) (hz : z ∈ T)
    (huv : u ⨯₃ v ≠ 0) (huw : u ⨯₃ w ≠ 0) (hvw : v ⨯₃ w ≠ 0)
    (huz : u ⨯₃ z ≠ 0) (hvz : v ⨯₃ z ≠ 0) (hwz : w ⨯₃ z ≠ 0)
    (hcol : ∀ ℓ : Fin 3 → K, ℓ ≠ 0 → ℓ ⬝ᵥ u = 0 → ℓ ⬝ᵥ v = 0 → ℓ ⬝ᵥ w = 0 → ℓ ⬝ᵥ z = 0 →
      False) :
    Module.finrank K (conicsThrough T) ≤ 2 := by
  set ℓ := u ⨯₃ v
  have lu : ℓ ⬝ᵥ u = 0 := cross_dot_left u v
  have lv : ℓ ⬝ᵥ v = 0 := cross_dot_right u v
  by_cases lw : ℓ ⬝ᵥ w = 0
  · by_cases lz : ℓ ⬝ᵥ z = 0
    · exact (hcol ℓ huv lu lv lw lz).elim
    · calc _ ≤ _ := conics_resid huv huv huw hvw lu lv lw T hu hv hw
        _ ≤ 2 := lines_le_two (ne_zero_of_cross huz) _ ⟨hz, lz⟩
  · by_cases lz : ℓ ⬝ᵥ z = 0
    · calc _ ≤ _ := conics_resid huv huv huz hvz lu lv lz T hu hv hz
        _ ≤ 2 := lines_le_two (ne_zero_of_cross huw) _ ⟨hw, lw⟩
    · have hQ1 : u ⨯₃ (u + v) ≠ 0 := by rw [cross_add_right]; exact huv
      have hQ2 : v ⨯₃ (u + v) ≠ 0 := by rw [cross_add_right']; exact neg_ne_zero.mpr huv
      calc _ ≤ Module.finrank K (conicsThrough (insert (u + v) T)) + 1 := conics_insert _ _
        _ ≤ Module.finrank K (linesThrough {x | x ∈ insert (u + v) T ∧ ℓ ⬝ᵥ x ≠ 0}) + 1 := by
          gcongr
          exact conics_resid huv huv hQ1 hQ2 lu lv (cross_add_dot u v) _
            (Set.mem_insert_of_mem _ hu) (Set.mem_insert_of_mem _ hv) (Set.mem_insert _ _)
        _ ≤ 1 + 1 := by
          gcongr
          exact lines_le_one hwz _ ⟨Set.mem_insert_of_mem _ hw, lw⟩
            ⟨Set.mem_insert_of_mem _ hz, lz⟩

/-- Four points on a common line. -/
def Col4 (x y z w : Fin 3 → K) : Prop :=
  ∃ ℓ : Fin 3 → K, ℓ ≠ 0 ∧ ℓ ⬝ᵥ x = 0 ∧ ℓ ⬝ᵥ y = 0 ∧ ℓ ⬝ᵥ z = 0 ∧ ℓ ⬝ᵥ w = 0

/-- **C5.** Five distinct points, no four collinear, impose at least 5 conditions on conics. -/
theorem conics_le_one {d e f g h : Fin 3 → K} (T : Set (Fin 3 → K))
    (hd : d ∈ T) (he : e ∈ T) (hf : f ∈ T) (hg : g ∈ T) (hh : h ∈ T)
    (hde : d ⨯₃ e ≠ 0) (hdf : d ⨯₃ f ≠ 0) (hdg : d ⨯₃ g ≠ 0) (hdh : d ⨯₃ h ≠ 0)
    (hef : e ⨯₃ f ≠ 0) (heg : e ⨯₃ g ≠ 0) (heh : e ⨯₃ h ≠ 0)
    (hfg : f ⨯₃ g ≠ 0) (hfh : f ⨯₃ h ≠ 0) (hgh : g ⨯₃ h ≠ 0)
    (n1 : ¬ Col4 d e f g) (n2 : ¬ Col4 d e f h) (n3 : ¬ Col4 d e g h)
    (n4 : ¬ Col4 d f g h) (n5 : ¬ Col4 e f g h) :
    Module.finrank K (conicsThrough T) ≤ 1 := by
  set m := d ⨯₃ e
  have md : m ⬝ᵥ d = 0 := cross_dot_left d e
  have me : m ⬝ᵥ e = 0 := cross_dot_right d e
  by_cases mf : m ⬝ᵥ f = 0
  · have mg : m ⬝ᵥ g ≠ 0 := fun mg => n1 ⟨m, hde, md, me, mf, mg⟩
    have mh : m ⬝ᵥ h ≠ 0 := fun mh => n2 ⟨m, hde, md, me, mf, mh⟩
    exact (conics_resid hde hde hdf hef md me mf T hd he hf).trans
      (lines_le_one hgh _ ⟨hg, mg⟩ ⟨hh, mh⟩)
  by_cases mg : m ⬝ᵥ g = 0
  · have mh : m ⬝ᵥ h ≠ 0 := fun mh => n3 ⟨m, hde, md, me, mg, mh⟩
    exact (conics_resid hde hde hdg heg md me mg T hd he hg).trans
      (lines_le_one hfh _ ⟨hf, mf⟩ ⟨hh, mh⟩)
  by_cases mh : m ⬝ᵥ h = 0
  · exact (conics_resid hde hde hdh heh md me mh T hd he hh).trans
      (lines_le_one hfg _ ⟨hf, mf⟩ ⟨hg, mg⟩)
  set m' := f ⨯₃ g
  have m'f : m' ⬝ᵥ f = 0 := cross_dot_left f g
  have m'g : m' ⬝ᵥ g = 0 := cross_dot_right f g
  by_cases m'h : m' ⬝ᵥ h = 0
  · have m'd : m' ⬝ᵥ d ≠ 0 := fun m'd => n4 ⟨m', hfg, m'd, m'f, m'g, m'h⟩
    have m'e : m' ⬝ᵥ e ≠ 0 := fun m'e => n5 ⟨m', hfg, m'e, m'f, m'g, m'h⟩
    exact (conics_resid hfg hfg hfh hgh m'f m'g m'h T hf hg hh).trans
      (lines_le_one hde _ ⟨hd, m'd⟩ ⟨he, m'e⟩)
  have hQ1 : d ⨯₃ (d + e) ≠ 0 := by rw [cross_add_right]; exact hde
  have hQ2 : e ⨯₃ (d + e) ≠ 0 := by rw [cross_add_right']; exact neg_ne_zero.mpr hde
  calc _ ≤ Module.finrank K (conicsThrough (insert (d + e) T)) + 1 := conics_insert _ _
    _ ≤ Module.finrank K (linesThrough {x | x ∈ insert (d + e) T ∧ m ⬝ᵥ x ≠ 0}) + 1 := by
      gcongr
      exact conics_resid hde hde hQ1 hQ2 md me (cross_add_dot d e) _
        (Set.mem_insert_of_mem _ hd) (Set.mem_insert_of_mem _ he) (Set.mem_insert _ _)
    _ = 0 + 1 := by
      rw [lines_eq_zero (S := {x | x ∈ insert (d + e) T ∧ m ⬝ᵥ x ≠ 0}) m'h
        (⟨Set.mem_insert_of_mem _ hf, mf⟩ : f ∈ {x | x ∈ insert (d + e) T ∧ m ⬝ᵥ x ≠ 0})
        ⟨Set.mem_insert_of_mem _ hg, mg⟩ ⟨Set.mem_insert_of_mem _ hh, mh⟩]

theorem exists_ne_zero_of_one_le {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {W : Submodule K V} (h : 1 ≤ Module.finrank K W) :
    ∃ x ∈ W, x ≠ 0 := by
  apply Submodule.exists_mem_ne_zero_of_ne_bot
  intro hb
  rw [← Submodule.finrank_eq_zero] at hb
  omega

/-- **Lemma X.** If the cubics through `S` have dimension `≥ 3` and `u, v ∈ S` are distinct
points, some nonzero conic vanishes at every point of `S` off the line `uv`. -/
theorem exists_conic_off_line [AtLeastThree K] {S : Set (Fin 3 → K)} {u v : Fin 3 → K}
    (hu : u ∈ S) (hv : v ∈ S) (huv : u ⨯₃ v ≠ 0)
    (hd : 3 ≤ Module.finrank K (cubicsThrough S)) :
    ∃ q : Fin 6 → K, q ≠ 0 ∧ ∀ x ∈ S, u ⨯₃ v ⬝ᵥ x ≠ 0 → evalC q x = 0 := by
  obtain ⟨t, ht⟩ := AtLeastThree.exists_ne (K := K)
  set Q1 := u + v
  set Q2 := u + t • v
  have e1 : u ⨯₃ Q1 ≠ 0 := by rw [cross_add_right]; exact huv
  have e2 : v ⨯₃ Q1 ≠ 0 := by rw [cross_add_right']; exact neg_ne_zero.mpr huv
  have e3 : u ⨯₃ Q2 ≠ 0 := by
    have : u ⨯₃ Q2 = t • (u ⨯₃ v) := by
      ext i; fin_cases i <;> simp [Q2, cross_apply] <;> ring
    rw [this]; exact smul_ne_zero ht.1 huv
  have e4 : v ⨯₃ Q2 ≠ 0 := by
    have : v ⨯₃ Q2 = -(u ⨯₃ v) := by
      ext i; fin_cases i <;> simp [Q2, cross_apply] <;> ring
    rw [this]; exact neg_ne_zero.mpr huv
  have e5 : Q1 ⨯₃ Q2 ≠ 0 := by
    have : Q1 ⨯₃ Q2 = (t - 1) • (u ⨯₃ v) := by
      ext i; fin_cases i <;> simp [Q1, Q2, cross_apply] <;> ring
    rw [this]; exact smul_ne_zero (sub_ne_zero.mpr ht.2) huv
  set ℓ := u ⨯₃ v
  have l1 : ℓ ⬝ᵥ Q1 = 0 := cross_add_dot u v
  have l2 : ℓ ⬝ᵥ Q2 = 0 := by
    rw [dotProduct_add, dotProduct_smul, cross_dot_left, cross_dot_right]; simp
  set S' := insert Q1 (insert Q2 S)
  have hS'1 := cubics_insert Q1 (insert Q2 S)
  have hS'2 := cubics_insert Q2 S
  have hr := cubics_resid huv huv e1 e2 e3 e4 e5 (cross_dot_left u v) (cross_dot_right u v)
    l1 l2 S' (by simp [S', hu]) (by simp [S', hv]) (by simp [S']) (by simp [S'])
  have hr' : 1 ≤ Module.finrank K (conicsThrough {x | x ∈ S' ∧ ℓ ⬝ᵥ x ≠ 0}) := by
    have : 1 ≤ Module.finrank K (cubicsThrough S') := by simp only [S']; omega
    exact this.trans hr
  obtain ⟨q, hq, hq0⟩ := exists_ne_zero_of_one_le hr'
  exact ⟨q, hq0, fun x hx hl => hq x ⟨by simp [S', hx], hl⟩⟩

/-- In a space of dimension `≤ 1`, a vanishing statement transfers between nonzero vectors. -/
theorem proportional {W : Submodule K (Fin 6 → K)} (hW : Module.finrank K W ≤ 1)
    {q r : Fin 6 → K} (hq : q ∈ W) (hr : r ∈ W) (hq0 : q ≠ 0) (hr0 : r ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ q = c • r := by
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hW
  obtain ⟨a, ha⟩ := hv ⟨q, hq⟩
  obtain ⟨b, hb⟩ := hv ⟨r, hr⟩
  have ha' : a • (v : Fin 6 → K) = q := congrArg Subtype.val ha
  have hb' : b • (v : Fin 6 → K) = r := congrArg Subtype.val hb
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb'; exact hr0 hb'.symm
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha'; exact hq0 ha'.symm
  refine ⟨a * b⁻¹, mul_ne_zero ha0 (inv_ne_zero hb0), ?_⟩
  rw [← ha', ← hb', smul_smul, mul_assoc, inv_mul_cancel₀ hb0, mul_one]

/-- **Lemma Y.** If three distinct points `u, v, w ∈ S` are collinear and the cubics through
`S` have dimension `≥ 3`, the conics through the points of `S` off that line have
dimension `≥ 2`. -/
theorem conics_off_line_ge_two [AtLeastThree K] {S : Set (Fin 3 → K)} {u v w : Fin 3 → K}
    (hu : u ∈ S) (hv : v ∈ S) (hw : w ∈ S) (huv : u ⨯₃ v ≠ 0) (huw : u ⨯₃ w ≠ 0)
    (hvw : v ⨯₃ w ≠ 0) (hlw : u ⨯₃ v ⬝ᵥ w = 0)
    (hd : 3 ≤ Module.finrank K (cubicsThrough S)) :
    2 ≤ Module.finrank K (conicsThrough {x | x ∈ S ∧ u ⨯₃ v ⬝ᵥ x ≠ 0}) := by
  classical
  obtain ⟨s, r, rfl⟩ := exists_smul_add_smul huv hlw
  obtain ⟨t, ht⟩ := AtLeastThree.exists_ne_zero_ne (r / s)
  set Q := u + t • v
  have e1 : u ⨯₃ Q = t • (u ⨯₃ v) := by
    ext i; fin_cases i <;> simp [Q, cross_apply] <;> ring
  have e2 : v ⨯₃ Q = -(u ⨯₃ v) := by
    ext i; fin_cases i <;> simp [Q, cross_apply] <;> ring
  have e3 : (s • u + r • v) ⨯₃ Q = (s * t - r) • (u ⨯₃ v) := by
    ext i; fin_cases i <;> simp [Q, cross_apply] <;> ring
  have hr : r ≠ 0 := by
    rintro rfl
    apply huw
    rw [(cross_combo u v s 0).1, zero_smul]
  have hst : s * t - r ≠ 0 := by
    intro h0
    by_cases hs : s = 0
    · rw [hs] at h0; exact hr (by linear_combination -h0)
    · apply ht.2
      field_simp
      linear_combination h0
  have hQu : u ⨯₃ Q ≠ 0 := by rw [e1]; exact smul_ne_zero ht.1 huv
  have hQv : v ⨯₃ Q ≠ 0 := by rw [e2]; exact neg_ne_zero.mpr huv
  have hQw : (s • u + r • v) ⨯₃ Q ≠ 0 := by rw [e3]; exact smul_ne_zero hst huv
  have lQ : u ⨯₃ v ⬝ᵥ Q = 0 := by
    rw [dotProduct_add, dotProduct_smul, cross_dot_left, cross_dot_right]; simp
  have h1 := cubics_insert Q S
  have h2 := cubics_resid huv huv huw hvw hQu hQv hQw (cross_dot_left u v)
    (cross_dot_right u v) hlw lQ (insert Q S) (Set.mem_insert_of_mem _ hu)
    (Set.mem_insert_of_mem _ hv) (Set.mem_insert_of_mem _ hw) (Set.mem_insert _ _)
  have h3 : Module.finrank K (conicsThrough {x | x ∈ insert Q S ∧ u ⨯₃ v ⬝ᵥ x ≠ 0}) ≤
      Module.finrank K (conicsThrough {x | x ∈ S ∧ u ⨯₃ v ⬝ᵥ x ≠ 0}) :=
    Submodule.finrank_mono (conicsThrough_anti fun x hx => ⟨Set.mem_insert_of_mem _ hx.1, hx.2⟩)
  omega

end PlaneCubic
