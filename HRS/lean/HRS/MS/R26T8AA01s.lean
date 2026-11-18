import HRS.MS.R26T8AA01r

/-!
# S8.2 T8A A01 (part s): the exterior-region limits of the eleven pieces of `3 ρ tripleG`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

/-- Integrability of `ρ ⟨F z, ∇_xQ(z,w)⟩`. -/
theorem r26t8a_a01_Fgrad_int (hd : 2 ≤ d) (a beta M A : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    (hA : 0 ≤ A) {rho : Euc d → ℝ} (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    {f : Euc d → ℝ} {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) (w : Euc d) :
    Integrable (fun z => rho z * inner ℝ (forceMean rho z) (pairGradX Q z w)) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < criticalS d := by unfold criticalS; linarith
  have hprob : HRS.Whole.IsProbDensity rho := hrho.1.1
  have hρs : ContDiff ℝ ∞ rho :=
    (HRS.MS.Mov0.mv0_hgauss hd hs0.le (by unfold criticalS; linarith) ha hbeta hrho).1
  have hQ2 : ContDiffOn ℝ 2 (Function.uncurry Q) {p : Euc d × Euc d | p.1 ≠ p.2} :=
    hQ.smooth.of_le (by norm_num)
  obtain ⟨hFs, hFb⟩ := r26t8a_thermal_force d hd a beta ha hbeta rho hrho
  obtain ⟨BF, hBF0, hBF⟩ := hFb 0
  have hF : ∀ u, ‖forceMean rho u‖ ≤ BF := fun u => by
    have := hBF u
    rw [norm_iteratedFDeriv_zero] at this
    linarith [norm_nonneg (fderiv ℝ (iteratedFDeriv ℝ 0 (forceMean rho)) u u)]
  have hgi := (r26t8a_a01_grad_int hd a beta M A ha hbeta hM hA hrho hQ w).1
  refine Integrable.mono' (hgi.const_mul BF) ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact r26t8a_p10a_aesm hd w ((hρs.continuous.continuousOn).mul
      (ContinuousOn.inner hFs.continuous.continuousOn (r26t8a_a01_gradX_cont_fst hQ2 w)))
  · rw [norm_mul, Real.norm_of_nonneg (hprob.nonneg z)]
    calc rho z * ‖inner ℝ (forceMean rho z) (pairGradX Q z w)‖
        ≤ rho z * (‖forceMean rho z‖ * ‖pairGradX Q z w‖) :=
          mul_le_mul_of_nonneg_left (by rw [Real.norm_eq_abs]; exact abs_real_inner_le_norm _ _) (hprob.nonneg z)
      _ ≤ rho z * (BF * ‖pairGradX Q z w‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hF z) (norm_nonneg _)) (hprob.nonneg z)
      _ = BF * (rho z * ‖pairGradX Q z w‖) := by ring

end HRS.MS.R26T8A
