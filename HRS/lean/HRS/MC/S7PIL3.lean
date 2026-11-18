import HRS.MC.S7PIL2
import HRS.MC.S7PIS3Cov3
import HRS.MC.S7PIHPde

/-!
# Packet piL, part 3: the Lipschitz bound of `u ↦ gaussHeat obsCov ψ_w u 0`

On each interval `[a,b]` with no observation time inside `(a,b)`, `s7_PIH_heat_pde_proof` (with the rate
`obsRateR a`, which is `obsRate` on `(a,b]`) gives the derivative, bounded by `½ C_B cbNorm 5 Φ ∏‖w‖` through the rate
bound `s7_PIB_rate_bound` applied to the bilinear form `N_x = D^{j+2}Φ(x)[·,·,w]`; the pieces are glued by induction on the
number of observation times inside the interval.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIL

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

/-- The bound of the derivative of the heat function (formula of `s7_PIH_heat_pde`) through the rate bound. -/
theorem S7PIL_deriv_bound (R : Regime d) (m T : ℝ) {q : ℕ} {t : Fin q → ℝ}
    {Λ : EuclideanSpace ℝ (Fin q) →L[ℝ] PathSpace d m T} (φ : Fin q → Torus d → ℝ) (CB : ℝ) (hCB0 : 0 ≤ CB)
    (hCB : ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ N : PathSpace d m T [×2]→L[ℝ] ℝ,
      |∑ i, ∑ j, obsRate R.D R.ρ t φ u i j *
        N ![Λ (EuclideanSpace.single i 1), Λ (EuclideanSpace.single j 1)]| ≤ CB * ‖N‖)
    {Φ : PathSpace d m T → ℝ} (hΦ : MemCb 5 Φ) {j : ℕ} (hj : j ≤ 3) (x0 : PathSpace d m T)
    (w : Fin j → PathSpace d m T) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) :
    |-(1 / 2 : ℝ) * ∑ i, ∑ jj, obsRate R.D R.ρ t φ r i jj *
        ∫ x, iteratedFDeriv ℝ 2 (S7PIL_psi (iteratedFDeriv ℝ j Φ) x0 Λ w) (0 + x)
          ![EuclideanSpace.single i 1, EuclideanSpace.single jj 1]
          ∂(multivariateGaussian 0 (obsCov R.D R.ρ t φ r))| ≤
      1 / 2 * (CB * (cbNorm 5 Φ * ∏ k, ‖w k‖)) := by
  set ψ := S7PIL_psi (iteratedFDeriv ℝ j Φ) x0 Λ w with hψdef
  have hψ : MemCb 2 ψ := S7PIL_psi_memCb hΦ hj x0 Λ w
  set ν := multivariateGaussian (0 : EuclideanSpace ℝ (Fin q)) (obsCov R.D R.ρ t φ r) with hν
  have : IsProbabilityMeasure ν := inferInstance
  have hint : ∀ i jj, Integrable (fun x => iteratedFDeriv ℝ 2 ψ (0 + x)
      ![EuclideanSpace.single i 1, EuclideanSpace.single jj 1]) ν := by
    intro i jj
    obtain ⟨B, hB⟩ := hψ.2 2 le_rfl
    set v : Fin 2 → EuclideanSpace ℝ (Fin q) := ![EuclideanSpace.single i 1, EuclideanSpace.single jj 1] with hv
    refine Integrable.of_bound (C := B * ∏ k, ‖v k‖) ?_ ?_
    · have hc : Continuous fun x : EuclideanSpace ℝ (Fin q) => (S7PIL_ev v) (iteratedFDeriv ℝ 2 ψ (0 + x)) :=
        (S7PIL_ev v).continuous.comp
          ((hψ.1.continuous_iteratedFDeriv (by norm_num)).comp (continuous_const.add continuous_id))
      exact hc.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      refine ((iteratedFDeriv ℝ 2 ψ (0 + x)).le_opNorm v).trans ?_
      exact mul_le_mul_of_nonneg_right (hB ⟨0 + x, rfl⟩) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  have e1 : ∀ i, ∑ jj, obsRate R.D R.ρ t φ r i jj * ∫ x, iteratedFDeriv ℝ 2 ψ (0 + x)
      ![EuclideanSpace.single i 1, EuclideanSpace.single jj 1] ∂ν =
      ∫ x, ∑ jj, obsRate R.D R.ρ t φ r i jj * iteratedFDeriv ℝ 2 ψ (0 + x)
        ![EuclideanSpace.single i 1, EuclideanSpace.single jj 1] ∂ν := by
    intro i
    rw [integral_finsetSum _ (fun jj _ => (hint i jj).const_mul _)]
    exact Finset.sum_congr rfl (fun jj _ => (integral_const_mul _ _).symm)
  have e2 : ∑ i, ∑ jj, obsRate R.D R.ρ t φ r i jj * ∫ x, iteratedFDeriv ℝ 2 ψ (0 + x)
      ![EuclideanSpace.single i 1, EuclideanSpace.single jj 1] ∂ν =
      ∫ x, ∑ i, ∑ jj, obsRate R.D R.ρ t φ r i jj * iteratedFDeriv ℝ 2 ψ (0 + x)
        ![EuclideanSpace.single i 1, EuclideanSpace.single jj 1] ∂ν := by
    rw [Finset.sum_congr rfl (fun i _ => e1 i)]
    exact (integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun jj _ => (hint i jj).const_mul _))).symm
  rw [e2]
  have hpt : ∀ x, ‖∑ i, ∑ jj, obsRate R.D R.ρ t φ r i jj * iteratedFDeriv ℝ 2 ψ (0 + x)
        ![EuclideanSpace.single i 1, EuclideanSpace.single jj 1]‖ ≤ CB * (cbNorm 5 Φ * ∏ k, ‖w k‖) := by
    intro x
    have hF := S7PIL_iter_contDiff hΦ.1 hj
    have h1 : ∀ i jj, iteratedFDeriv ℝ 2 ψ (0 + x) ![EuclideanSpace.single i 1, EuclideanSpace.single jj 1] =
        S7PIL_N (Φ := Φ) j w (x0 + Λ (0 + x))
          ![Λ (EuclideanSpace.single i 1), Λ (EuclideanSpace.single jj 1)] := by
      intro i jj
      rw [hψdef, S7PIL_psi_two hF x0 Λ w]
      rfl
    simp only [h1]
    rw [Real.norm_eq_abs]
    refine (hCB r hr _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hCB0
    refine (S7PIL_N_norm_le hΦ.1 hj w _).trans ?_
    exact mul_le_mul_of_nonneg_right (S7PIL_le_cbNorm hΦ (by omega) _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  have hn := norm_integral_le_of_norm_le_const (μ := ν)
    (f := fun x => ∑ i, ∑ jj, obsRate R.D R.ρ t φ r i jj * iteratedFDeriv ℝ 2 ψ (0 + x)
        ![EuclideanSpace.single i 1, EuclideanSpace.single jj 1]) (Filter.Eventually.of_forall hpt)
  have hu : ν.real Set.univ = 1 := by simp
  rw [hu, mul_one] at hn
  rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  rw [Real.norm_eq_abs] at hn
  linarith

end HRS.MC.Sec7.S7PIL

end
