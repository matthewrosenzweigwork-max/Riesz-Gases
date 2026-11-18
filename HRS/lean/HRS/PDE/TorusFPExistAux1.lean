import HRS.PDE.TorusFPSpec

/-!
# D1 existence, helper 1: calculus at a minimum point on the torus

Used by the backward maximum principle in `HRS/PDE/TorusFPExistAux2.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS

variable {n : ℕ}

/-- At a local minimum of a `C²` function the second derivative is nonnegative along every
direction. -/
theorem d1_secondDeriv_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → ℝ}
    (hF : ContDiff ℝ 2 F) {y : E} (hy : IsLocalMin F y) (v : E) :
    0 ≤ fderiv ℝ (fderiv ℝ F) y v v := by
  by_contra hneg
  rw [not_le] at hneg
  have hdiffF : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hF1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (m := 1) (by norm_num)
  have hdiff1 : Differentiable ℝ (fderiv ℝ F) := hF1.differentiable one_ne_zero
  have hcont2 : Continuous (fderiv ℝ (fderiv ℝ F)) := hF1.continuous_fderiv one_ne_zero
  set g : ℝ → ℝ := fun s => F (y + s • v) with hg
  set G : ℝ → ℝ := fun s => fderiv ℝ F (y + s • v) v with hG
  have hline : ∀ s : ℝ, HasDerivAt (fun s : ℝ => y + s • v) v s := by
    intro s
    simpa using ((hasDerivAt_id s).smul_const v).const_add y
  have hg' : ∀ s, HasDerivAt g (G s) s := by
    intro s
    have := (hdiffF (y + s • v)).hasFDerivAt.comp_hasDerivAt s (hline s)
    exact this
  have hG' : ∀ s, HasDerivAt G (fderiv ℝ (fderiv ℝ F) (y + s • v) v v) s := by
    intro s
    have h1 := (hdiff1 (y + s • v)).hasFDerivAt.comp_hasDerivAt s (hline s)
    have h2 := h1.clm_apply (hasDerivAt_const s v)
    simpa [hG] using h2
  have hG0 : G 0 = 0 := by
    have hmin : IsLocalMin g 0 := by
      have hc : ContinuousAt (fun s : ℝ => y + s • v) 0 := (hline 0).continuousAt
      have : ∀ᶠ z in 𝓝 y, F y ≤ F z := hy
      have h2 := hc.eventually (by simpa using this)
      filter_upwards [h2] with s hs
      simpa [hg] using hs
    have := hmin.hasDerivAt_eq_zero (hg' 0)
    exact this
  have hcontG2 : Continuous fun s : ℝ => fderiv ℝ (fderiv ℝ F) (y + s • v) v v :=
    ((hcont2.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply
      continuous_const).clm_apply continuous_const
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), fderiv ℝ (fderiv ℝ F) (y + s • v) v v < 0 := by
    have : fderiv ℝ (fderiv ℝ F) (y + (0 : ℝ) • v) v v < 0 := by simpa using hneg
    exact hcontG2.continuousAt.eventually_lt continuousAt_const this
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 hev
  have hmin' : ∀ᶠ s in 𝓝 (0 : ℝ), F y ≤ g s := by
    have hc : ContinuousAt (fun s : ℝ => y + s • v) 0 := (hline 0).continuousAt
    have : ∀ᶠ z in 𝓝 y, F y ≤ F z := hy
    have h2 := hc.eventually (by simpa using this)
    filter_upwards [h2] with s hs
    simpa [hg] using hs
  obtain ⟨ε, hε, hε'⟩ := Metric.eventually_nhds_iff.1 hmin'
  set s₀ : ℝ := min δ ε / 2 with hs₀
  have hs0pos : 0 < s₀ := by positivity
  have hs0δ : s₀ < δ := by have := min_le_left δ ε; simp only [hs₀]; linarith [lt_min hδ hε]
  have hs0ε : s₀ < ε := by have := min_le_right δ ε; simp only [hs₀]; linarith [lt_min hδ hε]
  have hneg2 : ∀ s ∈ Set.Icc (0 : ℝ) s₀, fderiv ℝ (fderiv ℝ F) (y + s • v) v v < 0 := by
    intro s hs
    refine hδ' ?_
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
    linarith [hs.2]
  have hGanti : StrictAntiOn G (Set.Icc 0 s₀) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) (fun s _ => (hG' s).continuousAt.continuousWithinAt)
      fun s hs => ?_
    rw [interior_Icc] at hs
    rw [(hG' s).deriv]
    exact hneg2 s ⟨hs.1.le, hs.2.le⟩
  have hGneg : ∀ s ∈ Set.Ioc (0 : ℝ) s₀, G s < 0 := by
    intro s hs
    have := hGanti ⟨le_rfl, hs0pos.le⟩ ⟨hs.1.le, hs.2⟩ hs.1
    rwa [hG0] at this
  have hganti : StrictAntiOn g (Set.Icc 0 s₀) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc _ _) (fun s _ => (hg' s).continuousAt.continuousWithinAt)
      fun s hs => ?_
    rw [interior_Icc] at hs
    rw [(hg' s).deriv]
    exact hGneg s ⟨hs.1, hs.2.le⟩
  have h1 : g s₀ < g 0 := hganti ⟨le_rfl, hs0pos.le⟩ ⟨hs0pos.le, le_rfl⟩ hs0pos
  have h2 : F y ≤ g s₀ := by
    refine hε' ?_
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hs0pos.le]
    exact hs0ε
  have h3 : g 0 = F y := by simp [hg]
  linarith

end HRS
