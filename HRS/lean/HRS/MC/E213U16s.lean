import HRS.MC.E213U16r

/-!
# Packet e213u16, file s: `cond_removal_drift`
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U16

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Q HRS.MC.E213U13 HRS.MC.E213Plan
open HRS.MC.E213U10

variable {d : ℕ}

section Drift

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem cond_removal_drift_proof (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ)
    (hΦ : MemCb 5 Φ) :
    ∫ ω, rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
        (fun v => NegSobolev.embed m (gd.B v ω)) ∂gd.P₀ =
      ∫ ω, fderiv ℝ Φ (gd.Zwin T a ω) (gd.Dwin T a ω) ∂gd.P₀ := by
  obtain ⟨K, hK, hbd⟩ := u16_Sn_bound gd T hT a ha Φ hΦ
  have hcb : 0 ≤ cbNorm 5 Φ := (norm_nonneg _).trans (u16_norm_fderiv_le hΦ 0)
  have hH : 0 < a + T := by linarith
  have hlim := tendsto_integral_of_dominated_convergence
    (F := fun n ω => SnD gd T a ha Φ n ω)
    (f := fun ω => rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
        (fun v => NegSobolev.embed m (gd.B v ω)))
    (bound := fun ω => cbNorm 5 Φ * K * Gblk gd (a + T) ω)
    (fun n => ?_) ((u16_Gblk_integrable gd (a + T)).const_mul (cbNorm 5 Φ * K)) (fun n => ?_)
    (u16_Sn_tendsto gd T hT a ha Φ hΦ)
  · have hconst : Tendsto (fun n : ℕ => ∫ ω, SnD gd T a ha Φ n ω ∂gd.P₀) atTop
        (𝓝 (∫ ω, fderiv ℝ Φ (gd.Zwin T a ω) (gd.Dwin T a ω) ∂gd.P₀)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact (u16_Sn_integral gd T hT a ha Φ hΦ hn).symm
    exact tendsto_nhds_unique hlim hconst
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [SnD, Finset.range_zero, Finset.sum_empty]
      exact aestronglyMeasurable_const
    · exact (u16_Sn_integrable gd T hT a ha Φ hΦ hn).aestronglyMeasurable
  · filter_upwards [hbd] with ω hω using hω n

end Drift

end HRS.MC.E213U16

end
