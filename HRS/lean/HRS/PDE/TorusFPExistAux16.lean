import HRS.PDE.TorusFPExistAux15

/-!
# D1 existence, helper 16: continuity of `s ↦ ∫ H_s dμ_s` and a uniform mean-value estimate
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS

variable {n : ℕ}

section TimeDep

variable (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
  (μ₀ : Measure (Torus n)) [IsProbabilityMeasure μ₀]

theorem d1_continuousOn_integral_H {τ : ℝ} {H : ℝ → Torus n → ℝ}
    (hH : Continuous fun p : Set.Icc (0 : ℝ) τ × Torus n => H p.1 p.2) :
    ContinuousOn (fun s => ∫ x, H s x ∂(d1_mu hn hκ hU μ₀ s)) (Set.Icc 0 τ) := by
  intro s₀ hs₀
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hu : UniformContinuous fun p : Set.Icc (0 : ℝ) τ × Torus n => H p.1 p.2 :=
    CompactSpace.uniformContinuous_of_continuous hH
  obtain ⟨δ₁, hδ₁, hu'⟩ := Metric.uniformContinuous_iff.1 hu (ε / 2) (half_pos hε)
  have hHs₀ : Continuous (H s₀) :=
    hH.comp (Continuous.prodMk continuous_const continuous_id : Continuous fun x : Torus n =>
      ((⟨s₀, hs₀⟩ : Set.Icc (0 : ℝ) τ), x))
  have hN := d1_narrow hn hκ hU μ₀ hHs₀ τ s₀ hs₀
  rw [Metric.continuousWithinAt_iff] at hN
  obtain ⟨δ₂, hδ₂, hN'⟩ := hN (ε / 2) (half_pos hε)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun s hs hdist => ?_⟩
  have h1 : dist s s₀ < δ₁ := lt_of_lt_of_le hdist (min_le_left _ _)
  have h2 : dist s s₀ < δ₂ := lt_of_lt_of_le hdist (min_le_right _ _)
  have := d1_mu_prob hn hκ hU μ₀ s
  have hHs : Continuous (H s) :=
    hH.comp (Continuous.prodMk continuous_const continuous_id : Continuous fun x : Torus n =>
      ((⟨s, hs⟩ : Set.Icc (0 : ℝ) τ), x))
  have hb : ∀ x, |H s x - H s₀ x| ≤ ε / 2 := by
    intro x
    have hd := hu' (a := (⟨s, hs⟩, x)) (b := (⟨s₀, hs₀⟩, x)) (by
      rw [Prod.dist_eq]
      simp only [dist_self, Subtype.dist_eq]
      rw [max_eq_left dist_nonneg]; exact h1)
    rw [Real.dist_eq] at hd
    exact hd.le
  have t1 := d1_abs_integral_sub_le (ρ := d1_mu hn hκ hU μ₀ s) hHs hHs₀ hb
  have t2 := hN' hs h2
  rw [Real.dist_eq] at t2 ⊢
  calc |∫ x, H s x ∂(d1_mu hn hκ hU μ₀ s) - ∫ x, H s₀ x ∂(d1_mu hn hκ hU μ₀ s₀)|
      ≤ |∫ x, H s x ∂(d1_mu hn hκ hU μ₀ s) - ∫ x, H s₀ x ∂(d1_mu hn hκ hU μ₀ s)| +
        |∫ x, H s₀ x ∂(d1_mu hn hκ hU μ₀ s) - ∫ x, H s₀ x ∂(d1_mu hn hκ hU μ₀ s₀)| := abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := lt_of_le_of_lt (add_le_add t1 le_rfl) (by linarith)
    _ = ε := by ring

end TimeDep

/-- Uniform mean value estimate in time. -/
theorem d1_time_diff_quot {τ : ℝ} {f ft : ℝ → Torus n → ℝ} (hτ : 0 < τ) (hf : IsC12Test τ f ft)
    {s : ℝ} (hs : s ∈ Set.Icc 0 τ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : ℝ, 0 < h → h < δ → s + h ≤ τ → ∀ x : Torus n,
      |(f (s + h) x - f s x) / h - ft s x| ≤ ε := by
  have hFu : UniformContinuous fun p : Set.Icc (0 : ℝ) τ × Torus n => ft p.1 p.2 :=
    CompactSpace.uniformContinuous_of_continuous hf.cont_time_deriv
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuous_iff.1 hFu ε hε
  refine ⟨δ, hδ, fun h hpos hlt hsh x => ?_⟩
  set G : ℝ → ℝ := fun r => f r x - r * ft s x with hG
  have hsub : Set.Icc s (s + h) ⊆ Set.Icc 0 τ := fun r hr => ⟨by linarith [hr.1, hs.1], by linarith [hr.2]⟩
  have hder : ∀ r ∈ Set.Icc s (s + h), HasDerivWithinAt G (ft r x - ft s x) (Set.Icc s (s + h)) r := by
    intro r hr
    have h1 := (hf.hasDerivWithinAt_Icc hτ x (hsub hr)).mono hsub
    have h2 : HasDerivWithinAt (fun r : ℝ => r * ft s x) (ft s x) (Set.Icc s (s + h)) r := by
      simpa using ((hasDerivAt_id r).mul_const (ft s x)).hasDerivWithinAt
    exact h1.sub h2
  have hbound : ∀ r ∈ Set.Icc s (s + h), ‖ft r x - ft s x‖ ≤ ε := by
    intro r hr
    have hd := hu (a := (⟨r, hsub hr⟩, x)) (b := (⟨s, hs⟩, x)) (by
      rw [Prod.dist_eq]
      simp only [dist_self, Subtype.dist_eq, Real.dist_eq]
      rw [max_eq_left (abs_nonneg _), abs_of_nonneg (by linarith [hr.1])]
      linarith [hr.2])
    rw [Real.dist_eq] at hd
    rw [Real.norm_eq_abs]
    exact hd.le
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbound (convex_Icc s (s + h))
    (⟨le_rfl, by linarith⟩ : s ∈ Set.Icc s (s + h)) (⟨by linarith, le_rfl⟩ : s + h ∈ Set.Icc s (s + h))
  simp only [Real.norm_eq_abs] at hmv
  rw [show s + h - s = h by ring, abs_of_pos hpos] at hmv
  have e : (f (s + h) x - f s x) / h - ft s x = (G (s + h) - G s) / h := by
    simp only [hG]; field_simp; ring
  rw [e, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  linarith

end HRS
