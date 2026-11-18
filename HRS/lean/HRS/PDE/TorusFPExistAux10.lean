import HRS.PDE.TorusFPExistAux9

/-!
# D1 existence, helper 10: difference quotients of the solution operator
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS

variable {n : ℕ}

section DiffQuot

variable (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)

/-- Uniform convergence of the difference quotients: `(U^{0,h} φ - φ)/h → L φ` as `h → 0⁺`. -/
theorem d1_P_diff_quot {φ : Torus n → ℝ} (hφ : Torus.IsSmooth φ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : ℝ, 0 < h → h < δ → ∀ x : Torus n,
      |(d1_P hn hκ hU h φ x - φ x) / h - d1_gen κ (d1_gradDrift U) φ x| ≤ ε := by
  have h1 : (0 : ℝ) < 1 := one_pos
  have hf := d1_sol_spec hn hκ hU h1 hφ
  set f := d1_sol hn hκ hU 1 φ with hfdef
  have hC := hf.isC12Test
  have hFc := hf.cont_time_deriv
  have hFu : UniformContinuous fun p : Set.Icc (0 : ℝ) 1 × Torus n =>
      d1_gen κ (d1_gradDrift U) (f p.1) p.2 :=
    CompactSpace.uniformContinuous_of_continuous hFc
  obtain ⟨δ₀, hδ₀, hδ⟩ := Metric.uniformContinuous_iff.1 hFu ε hε
  refine ⟨min δ₀ 1, lt_min hδ₀ one_pos, fun h hpos hlt x => ?_⟩
  have hlt1 : h < 1 := lt_of_lt_of_le hlt (min_le_right _ _)
  have hltδ : h < δ₀ := lt_of_lt_of_le hlt (min_le_left _ _)
  set Lφ := d1_gen κ (d1_gradDrift U) φ x with hLφ
  set G : ℝ → ℝ := fun r => f r x + r * Lφ with hG
  have hder : ∀ r ∈ Set.Icc (1 - h) 1, HasDerivWithinAt G
      (-(d1_gen κ (d1_gradDrift U) (f r) x) + Lφ) (Set.Icc (1 - h) 1) r := by
    intro r hr
    have hr' : r ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hr.1], hr.2⟩
    have h1 := (hC.hasDerivWithinAt_Icc h1 x hr').mono (Set.Icc_subset_Icc_left (by linarith : (0 : ℝ) ≤ 1 - h))
    have h2 : HasDerivWithinAt (fun r : ℝ => r * Lφ) Lφ (Set.Icc (1 - h) 1) r := by
      simpa using ((hasDerivAt_id r).mul_const Lφ).hasDerivWithinAt
    exact h1.add h2
  have hbound : ∀ r ∈ Set.Icc (1 - h) 1, ‖-(d1_gen κ (d1_gradDrift U) (f r) x) + Lφ‖ ≤ ε := by
    intro r hr
    have hr' : r ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hr.1], hr.2⟩
    have hd := hδ (a := (⟨r, hr'⟩, x)) (b := (⟨1, h1.le, le_rfl⟩, x)) (by
      rw [Prod.dist_eq]
      simp only [dist_self, Subtype.dist_eq, Real.dist_eq]
      rw [max_eq_left (abs_nonneg _), abs_of_nonpos (by linarith [hr.2])]
      linarith [hr.1])
    simp only [Real.dist_eq] at hd
    have e : d1_gen κ (d1_gradDrift U) (f 1) x = Lφ := by rw [hf.terminal]
    rw [e] at hd
    rw [Real.norm_eq_abs]
    have : -(d1_gen κ (d1_gradDrift U) (f r) x) + Lφ = -(d1_gen κ (d1_gradDrift U) (f r) x - Lφ) := by ring
    rw [this, abs_neg]
    exact hd.le
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound (convex_Icc (1 - h) 1)
    (⟨le_rfl, by linarith⟩ : (1 - h) ∈ Set.Icc (1 - h) 1) (⟨by linarith, le_rfl⟩ : (1 : ℝ) ∈ Set.Icc (1 - h) 1)
  have hP : d1_P hn hκ hU h φ x = f (1 - h) x := d1_P_eq hn hκ hU h1 hφ hf ⟨hpos.le, hlt1.le⟩ x
  have hG1 : G 1 = φ x + Lφ := by simp [hG, hf.terminal]
  have hG0 : G (1 - h) = d1_P hn hκ hU h φ x + (1 - h) * Lφ := by simp [hG, hP]
  simp only [Real.norm_eq_abs] at hmv
  rw [hG1, hG0, show (1 : ℝ) - (1 - h) = h by ring, abs_of_pos hpos] at hmv
  have : (d1_P hn hκ hU h φ x - φ x) / h - Lφ =
      -((φ x + Lφ - (d1_P hn hκ hU h φ x + (1 - h) * Lφ)) / h) := by
    field_simp; ring
  rw [this, abs_neg, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  linarith

end DiffQuot

end HRS
