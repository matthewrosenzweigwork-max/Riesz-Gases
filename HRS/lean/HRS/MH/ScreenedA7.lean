import HRS.MH.ScreenedDefs
import HRS.Whole.MovtrAux2
import HRS.Whole.Q34Aux1

/-!
# Packet A7 of `B:lem:screened` (S.B.4): kernel gradient bound and ball integral of `‖u‖^{-t}`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

theorem kernel_bound_proof {s : ℝ} (hs0 : 0 ≤ s) (u : Euc d) (hu : u ≠ 0) :
    ‖rieszKernelGrad d s u‖ ≤ max 1 s * ‖u‖ ^ (-s - 1) := by
  rw [HRS.Whole.movtr_rieszKernelGrad_norm s hs0 hu]
  have hσ : HRS.Whole.movtr_sigma s ≤ max 1 s := by
    unfold HRS.Whole.movtr_sigma
    split_ifs with h
    · rw [h]; exact le_max_left _ _
    · exact le_max_right _ _
  exact mul_le_mul_of_nonneg_right hσ (Real.rpow_nonneg (norm_nonneg _) _)

theorem lintegral_ball_rpow_le_proof (hd : 1 ≤ d) {t : ℝ} (ht : t < d) :
    ∃ CK : ℝ, 0 ≤ CK ∧ ∀ R : ℝ, 0 < R →
      ∫⁻ u in Metric.closedBall (0 : Euc d) R, ENNReal.ofReal (‖u‖ ^ (-t)) ≤
        ENNReal.ofReal (CK * R ^ ((d : ℝ) - t)) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hda : (0 : ℝ) < (d : ℝ) - t := by linarith
  have hsA : 0 ≤ HRS.sphereArea d := by
    unfold HRS.sphereArea
    have : 0 < Real.Gamma ((d : ℝ) / 2) := Real.Gamma_pos_of_pos (div_pos hdpos two_pos)
    exact div_nonneg (by positivity) this.le
  refine ⟨HRS.sphereArea d / ((d : ℝ) - t), div_nonneg hsA hda.le, fun R hR => ?_⟩
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hsph : volume (Metric.sphere (0 : Euc d) R) = 0 := Measure.addHaar_sphere volume 0 R
  have hball := HRS.Whole.Q34.lintegral_ball_rpow hd hR ht
  calc ∫⁻ u in Metric.closedBall (0 : Euc d) R, ENNReal.ofReal (‖u‖ ^ (-t))
      = ∫⁻ u in Metric.ball (0 : Euc d) R ∪ Metric.sphere (0 : Euc d) R,
          ENNReal.ofReal (‖u‖ ^ (-t)) := by
        rw [Metric.ball_union_sphere]
    _ ≤ (∫⁻ u in Metric.ball (0 : Euc d) R, ENNReal.ofReal (‖u‖ ^ (-t))) +
          (∫⁻ u in Metric.sphere (0 : Euc d) R, ENNReal.ofReal (‖u‖ ^ (-t))) :=
        lintegral_union_le _ _ _
    _ = ENNReal.ofReal (HRS.sphereArea d * (R ^ ((d : ℝ) - t) / ((d : ℝ) - t))) := by
        rw [setLIntegral_measure_zero _ _ hsph, add_zero, hball]
    _ = ENNReal.ofReal (HRS.sphereArea d / ((d : ℝ) - t) * R ^ ((d : ℝ) - t)) := by
        congr 1; ring

end HRS.MH.Screened
