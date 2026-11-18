import HRS.MS.R26T8AZ3m

/-!
# S8.2 T8A Z3i: integrability of `K(z-v) • DG(v)` for the singular source of Z3m
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_Z3i_int (hd : 2 ≤ d) (nu : ℝ) {G : Euc d → ℝ}
    (hG1 : ContDiffOn ℝ 1 G {0}ᶜ) (hGc : ∀ w, 2 < ‖w‖ → G w = 0) {c1 s1 : ℝ}
    (hc1 : ∀ w, w ≠ 0 → ‖fderiv ℝ G w‖ ≤ c1 * ‖w‖ ^ (-s1)) (hs1 : 0 < s1) (hs1d : s1 < d)
    {z' : Euc d} (hz' : z' ≠ 0) :
    Integrable (fun v => newtonKernel d nu (z' - v) • fderiv ℝ G v) := by
  haveI := r26t8a_nontrivial hd
  set K : Euc d → ℝ := newtonKernel d nu with hK
  have hKm : Measurable K := r26t8a_K_measurable nu
  have hae0 := r26t8a_ae_ne_zero hd
  have hder0 : ∀ w, 2 < ‖w‖ → fderiv ℝ G w = 0 := fun w hw => by
    have : G =ᶠ[𝓝 w] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hw] with u hu using hGc u hu
    rw [this.fderiv_eq]; exact fderiv_const_apply 0
  have hind : ∀ v : Euc d, ‖v‖ ≤ 2 → (closedBall (0 : Euc d) 2).indicator (fun v => ‖v‖ ^ (-s1)) v = ‖v‖ ^ (-s1) :=
    fun v hv => Set.indicator_of_mem (by simpa [mem_closedBall_zero_iff] using hv) _
  have hind0 : ∀ v : Euc d, 0 ≤ (closedBall (0 : Euc d) 2).indicator (fun v => ‖v‖ ^ (-s1)) v := fun v =>
    Set.indicator_nonneg (fun v _ => Real.rpow_nonneg (norm_nonneg v) _) v
  have hdGm : AEStronglyMeasurable (fderiv ℝ G) (volume : Measure (Euc d)) := by
    have h1 := (hG1.continuousOn_fderiv_of_isOpen isOpen_compl_singleton le_rfl).aestronglyMeasurable
      (measurableSet_singleton (0 : Euc d)).compl (μ := (volume : Measure (Euc d)))
    have hae0' : ∀ᵐ x : Euc d ∂(volume : Measure (Euc d)), x ∈ ({0}ᶜ : Set (Euc d)) := hae0
    rwa [Measure.restrict_eq_self_of_ae_mem hae0'] at h1
  have hc10 : 0 ≤ c1 := by
    obtain ⟨w0, hw0⟩ := exists_ne (0 : Euc d)
    have h := hc1 w0 hw0
    have hp : 0 < ‖w0‖ ^ (-s1) := Real.rpow_pos_of_pos (norm_pos_iff.2 hw0) _
    by_contra hneg
    push Not at hneg
    nlinarith [norm_nonneg (fderiv ℝ G w0)]
  refine Integrable.mono' ((r26t8a_p07_major hd nu hs1 hs1d hz').const_mul c1)
    ((hKm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable.smul hdGm) ?_
  filter_upwards [hae0] with v hv
  rw [norm_smul, Real.norm_eq_abs]
  by_cases hv2 : ‖v‖ ≤ 2
  · rw [hind v hv2]
    calc |K (z' - v)| * ‖fderiv ℝ G v‖ ≤ |K (z' - v)| * (c1 * ‖v‖ ^ (-s1)) :=
          mul_le_mul_of_nonneg_left (hc1 v hv) (abs_nonneg _)
      _ = _ := by ring
  · rw [hder0 v (not_le.1 hv2), norm_zero, mul_zero]
    have := hind0 v
    positivity

end HRS.MS.R26T8A
