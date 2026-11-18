import HRS.MS.R26T8AP07h

/-!
# S8.2 local Newton layer, packet T8A.P07 (part i): integrable majorant of the raw Newton integrand
`r26t8a_p07_major`: for `w != 0` and `0 < s < d`, `z |-> |K(w-z)| * 1_{|z|<=2} * |z|^(-s)` is integrable.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_p07_K_continuousOn (nu : ℝ) : ContinuousOn (newtonKernel d nu) {u : Euc d | u ≠ 0} := by
  unfold newtonKernel
  by_cases h : d = 2
  · simp only [h, ↓reduceIte]
    exact ((Real.continuousOn_log.comp continuous_norm.continuousOn
      (fun u hu => norm_ne_zero_iff.2 hu)).neg).div_const _
  · simp only [h, ↓reduceIte]
    exact (continuous_norm.continuousOn.rpow_const (fun u hu => Or.inl (norm_ne_zero_iff.2 hu))).div_const _

theorem r26t8a_p07_major (hd : 2 ≤ d) (nu : ℝ) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) {w : Euc d} (hw : w ≠ 0) :
    Integrable (fun z : Euc d => |newtonKernel d nu (w - z)| *
      (closedBall (0 : Euc d) 2).indicator (fun z => ‖z‖ ^ (-s)) z) := by
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw
  set ρ : ℝ := ‖w‖ / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  -- bound of K on the annulus
  have hcomp : IsCompact ({u : Euc d | ρ ≤ ‖u‖} ∩ closedBall (0 : Euc d) (3 * ρ)) :=
    (isCompact_closedBall _ _).inter_left (isClosed_le continuous_const continuous_norm)
  obtain ⟨Km, hKm⟩ := hcomp.exists_bound_of_continuousOn ((r26t8a_p07_K_continuousOn (d := d) nu).mono
    (fun u hu => norm_pos_iff.1 (lt_of_lt_of_le hρ0 hu.1)))
  have hun : ‖(ρ / ‖w‖) • w‖ = ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]; field_simp
  have hKm0 : 0 ≤ Km := le_trans (norm_nonneg _) (hKm ((ρ / ‖w‖) • w) ⟨by simp only [Set.mem_setOf_eq]; rw [hun],
    by simp only [mem_closedBall, dist_zero_right]; rw [hun]; linarith⟩)
  -- two dominating integrable functions
  have hI1 : Integrable ((ball (0 : Euc d) ρ).indicator (fun z : Euc d => Km * ‖z‖ ^ (-s))) :=
    (integrable_indicator_iff measurableSet_ball).2
      ((r26t8a_integrableOn_ball_rpow (by omega) hsd ρ).const_mul Km)
  have hKint : Integrable ((ball (0 : Euc d) (‖w‖ + 3)).indicator (newtonKernel d nu)) :=
    (integrable_indicator_iff measurableSet_ball).2 (r26t8a_K_integrableOn hd nu _)
  have hI2 : Integrable (fun z : Euc d => ρ ^ (-s) * ((ball (0 : Euc d) (‖w‖ + 3)).indicator
      (fun u => |newtonKernel d nu u|) (w - z))) := by
    have : Integrable (fun u : Euc d => (ball (0 : Euc d) (‖w‖ + 3)).indicator
        (fun u => |newtonKernel d nu u|) u) := by
      have := hKint.norm
      refine this.congr (Eventually.of_forall fun u => ?_)
      by_cases hu : u ∈ ball (0 : Euc d) (‖w‖ + 3)
      · simp [Set.indicator_of_mem hu]
      · simp [Set.indicator_of_notMem hu]
    exact (this.comp_sub_left w).const_mul _
  refine Integrable.mono' (hI1.add hI2) ?_ (Eventually.of_forall fun z => ?_)
  · have hm1 : Measurable (fun z : Euc d => |newtonKernel d nu (w - z)|) :=
      continuous_abs.measurable.comp ((r26t8a_K_measurable nu).comp (measurable_const.sub measurable_id))
    have hm2 : Measurable ((closedBall (0 : Euc d) 2).indicator (fun z : Euc d => ‖z‖ ^ (-s))) :=
      Measurable.indicator (measurable_norm.pow_const _) measurableSet_closedBall
    exact (hm1.mul hm2).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (Set.indicator_nonneg
      (fun u _ => Real.rpow_nonneg (norm_nonneg u) _) z))]
    by_cases hz : z ∈ closedBall (0 : Euc d) 2
    · rw [Set.indicator_of_mem hz]
      have hz2 : ‖z‖ ≤ 2 := by simpa using hz
      by_cases hzr : ‖z‖ < ρ
      · have hzb : z ∈ ball (0 : Euc d) ρ := by simpa using hzr
        have hKb : |newtonKernel d nu (w - z)| ≤ Km := by
          have := hKm (w - z) ⟨?_, ?_⟩
          · simpa using this
          · simp only [Set.mem_setOf_eq]
            have := norm_sub_norm_le w z
            rw [hρ]; linarith
          · simp only [mem_closedBall, dist_zero_right]
            have := norm_sub_le w z
            rw [hρ]; linarith
        simp only [Pi.add_apply, Set.indicator_of_mem hzb]
        have h2 : 0 ≤ (ball (0 : Euc d) (‖w‖ + 3)).indicator (fun u => |newtonKernel d nu u|) (w - z) :=
          Set.indicator_nonneg (fun u _ => abs_nonneg _) _
        have h3 : 0 ≤ ρ ^ (-s) * (ball (0 : Euc d) (‖w‖ + 3)).indicator (fun u => |newtonKernel d nu u|) (w - z) :=
          mul_nonneg (Real.rpow_nonneg hρ0.le _) h2
        nlinarith [mul_le_mul_of_nonneg_right hKb (Real.rpow_nonneg (norm_nonneg z) (-s))]
      · push Not at hzr
        have hzb : z ∉ ball (0 : Euc d) ρ := by simpa using hzr
        have hwz : w - z ∈ ball (0 : Euc d) (‖w‖ + 3) := by
          simp only [mem_ball, dist_zero_right]
          have := norm_sub_le w z
          linarith
        simp only [Pi.add_apply, Set.indicator_of_notMem hzb, Set.indicator_of_mem hwz, zero_add]
        have hpow : ‖z‖ ^ (-s) ≤ ρ ^ (-s) := Real.rpow_le_rpow_of_nonpos hρ0 hzr (by linarith)
        calc |newtonKernel d nu (w - z)| * ‖z‖ ^ (-s) ≤ |newtonKernel d nu (w - z)| * ρ ^ (-s) :=
              mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
          _ = _ := mul_comm _ _
    · rw [Set.indicator_of_notMem hz, mul_zero]
      simp only [Pi.add_apply]
      have h1 : 0 ≤ (ball (0 : Euc d) ρ).indicator (fun z : Euc d => Km * ‖z‖ ^ (-s)) z :=
        Set.indicator_nonneg (fun u _ => mul_nonneg hKm0 (Real.rpow_nonneg (norm_nonneg u) _)) z
      have h2 : 0 ≤ ρ ^ (-s) * (ball (0 : Euc d) (‖w‖ + 3)).indicator (fun u => |newtonKernel d nu u|) (w - z) :=
        mul_nonneg (Real.rpow_nonneg hρ0.le _) (Set.indicator_nonneg (fun u _ => abs_nonneg _) _)
      linarith

end HRS.MS.R26T8A
