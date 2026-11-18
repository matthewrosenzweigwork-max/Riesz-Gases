import HRS.MS.R26T8AP05e

/-!
# S8.2 local Newton layer, packet T8A.P05 (part f): pointwise bound of the integrand of the convolution formula
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_nested_zero {chi : Euc d → ℝ} {R : ℝ} {F : Euc d → Euc d → ℝ} {w0 : Euc d}
    (h : w0 ∉ tsupport (r26t8a_annulus chi R)) (p q : ℕ) (X : Euc d) :
    iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (fun w => r26t8a_annulus chi R w * midPair F Y w) w0) X = 0 := by
  have hev : r26t8a_annulus chi R =ᶠ[𝓝 w0] 0 := notMem_tsupport_iff_eventuallyEq.1 h
  have h1 : ∀ Y : Euc d, iteratedFDeriv ℝ q (fun w => r26t8a_annulus chi R w * midPair F Y w) w0 = 0 := fun Y => by
    have : (fun w => r26t8a_annulus chi R w * midPair F Y w) =ᶠ[𝓝 w0] fun _ => 0 := by
      filter_upwards [hev] with w hw
      simp [hw]
    rw [(this.iteratedFDeriv ℝ q).eq_of_nhds]
    simp
  simp only [h1]
  simp

theorem r26t8a_nontrivial (hd : 2 ≤ d) : Nontrivial (Euc d) := by
  rw [← Module.finrank_pos_iff (R := ℝ), finrank_euclideanSpace_fin]; omega

theorem r26t8a_ball_volume' (hd : 2 ≤ d) {R : ℝ} (hR : 0 < R) :
    (volume (Metric.ball (0 : Euc d) (7 * R))).toReal =
      (volume (Metric.ball (0 : Euc d) 1)).toReal * (7 ^ d * R ^ d) := by
  haveI := r26t8a_nontrivial hd
  rw [Measure.addHaar_ball _ _ (by positivity : (0 : ℝ) ≤ 7 * R), finrank_euclideanSpace_fin,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), mul_pow]
  ring

theorem r26t8a_ae_ne_zero (hd : 2 ≤ d) : ∀ᵐ u : Euc d ∂volume, u ≠ 0 := by
  haveI := r26t8a_nontrivial hd
  have := (Set.countable_singleton (0 : Euc d)).ae_notMem (volume : Measure (Euc d))
  filter_upwards [this] with u hu h
  exact hu (by simp [h])

end HRS.MS.R26T8A
