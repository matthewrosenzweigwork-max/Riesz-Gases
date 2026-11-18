import HRS.MS.R2InterpAux37

/-!
# S10.2 (worker S102), part 38 (packet B2, step C): the derivative bound for the interpolated heat function
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators MatrixOrder Matrix

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MC.Sec7.S7PIL

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}

/-- `|∑ Δ_ij N(Λe_i,Λe_j)| ≤ C_b ‖N‖ (u - v)` for the covariance increment. -/
theorem s102_Delta_bound (hT : 0 < T) (L : ℕ)
    (hG : S102GramInt C m hT L) {Cb : ℝ}
    (hCb : ∀ {ρ : ℝ}, ρ ∈ Icc (0 : ℝ) T → ∀ N : OscPath d m T [×2]→L[ℝ] ℝ,
      |∑ k, ∑ k', s102_rateM C m hT L ρ k k' *
        N ![s102_Lam T L (EuclideanSpace.single k (1 : ℝ)), s102_Lam T L (EuclideanSpace.single k' (1 : ℝ))]| ≤
          Cb * ‖N‖)
    {v u : ℝ} (hv : 0 ≤ v) (hvu : v ≤ u) (huT : u ≤ T) (N : OscPath d m T [×2]→L[ℝ] ℝ) :
    |∑ k, ∑ k', s102_Delta C m hT L v u k k' *
        N ![s102_Lam T L (EuclideanSpace.single k (1 : ℝ)), s102_Lam T L (EuclideanSpace.single k' (1 : ℝ))]| ≤
      Cb * ‖N‖ * (u - v) := by
  have hsub : Ioc v u ⊆ Icc 0 T := Ioc_subset_Icc_self.trans (Icc_subset_Icc hv huT)
  have hint : ∀ k k', IntegrableOn (fun ρ => s102_rateM C m hT L ρ k k' *
      N ![s102_Lam T L (EuclideanSpace.single k (1 : ℝ)), s102_Lam T L (EuclideanSpace.single k' (1 : ℝ))])
      (Ioc v u) := fun k k' => ((s102_rateM_integrableOn hT L hG k k').mono_set hsub).mul_const _
  have e : ∑ k, ∑ k', s102_Delta C m hT L v u k k' *
        N ![s102_Lam T L (EuclideanSpace.single k (1 : ℝ)), s102_Lam T L (EuclideanSpace.single k' (1 : ℝ))] =
      ∫ ρ in Ioc v u, ∑ k, ∑ k', s102_rateM C m hT L ρ k k' *
        N ![s102_Lam T L (EuclideanSpace.single k (1 : ℝ)), s102_Lam T L (EuclideanSpace.single k' (1 : ℝ))] := by
    rw [integral_finsetSum _ (fun k _ => integrable_finset_sum _ fun k' _ => hint k k')]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ (fun k' _ => hint k k')]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [integral_mul_const]
    rfl
  rw [e, ← Real.norm_eq_abs]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc v u)
    (f := fun ρ => ∑ k, ∑ k', s102_rateM C m hT L ρ k k' *
        N ![s102_Lam T L (EuclideanSpace.single k (1 : ℝ)), s102_Lam T L (EuclideanSpace.single k' (1 : ℝ))])
    (C := Cb * ‖N‖) (by simp) (fun ρ hρ => by
      rw [Real.norm_eq_abs]; exact hCb (hsub hρ) N)
  simpa [Real.volume_real_Ioc, hvu, mul_comm, mul_assoc, mul_left_comm] using this

end HRS.MS.R2Interp

end
