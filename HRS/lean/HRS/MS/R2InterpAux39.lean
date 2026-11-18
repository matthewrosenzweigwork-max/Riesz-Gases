import HRS.MS.R2InterpAux38

/-!
# S10.2 (worker S102), part 39 (packet B2, step D): the derivative bound along the interpolation path and the one-sided increment bound
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators MatrixOrder Matrix

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MC.Sec7.S7PIL HRS.MC.Sec7.PI

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}

/-- Generic bound of `∑ Δ_ij E D²ψ(e_i,e_j)` through a bilinear-form bound on `Δ`. -/
theorem s102_delta_deriv_bound {q : ℕ} (Λ : EuclideanSpace ℝ (Fin q) →L[ℝ] OscPath d m T)
    (Δ : Matrix (Fin q) (Fin q) ℝ) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ N : OscPath d m T [×2]→L[ℝ] ℝ,
      |∑ i, ∑ j, Δ i j * N ![Λ (EuclideanSpace.single i (1 : ℝ)), Λ (EuclideanSpace.single j (1 : ℝ))]| ≤ B * ‖N‖)
    {Φ : OscPath d m T → ℝ} (hΦ : MemCb 5 Φ) {j : ℕ} (hj : j ≤ 3) (x0 : OscPath d m T)
    (w : Fin j → OscPath d m T) (ν : Measure (EuclideanSpace ℝ (Fin q))) [IsProbabilityMeasure ν] :
    |∑ i, ∑ jj, Δ i jj * ∫ x, iteratedFDeriv ℝ 2 (S7PIL_psi (iteratedFDeriv ℝ j Φ) x0 Λ w) (0 + x)
      ![EuclideanSpace.single i 1, EuclideanSpace.single jj 1] ∂ν| ≤ B * (cbNorm 5 Φ * ∏ k, ‖w k‖) := by
  set ψ := S7PIL_psi (iteratedFDeriv ℝ j Φ) x0 Λ w with hψdef
  have hψ : MemCb 2 ψ := S7PIL_psi_memCb hΦ hj x0 Λ w
  have hint : ∀ i jj, Integrable (fun x => iteratedFDeriv ℝ 2 ψ (0 + x)
      ![EuclideanSpace.single i 1, EuclideanSpace.single jj 1]) ν := by
    intro i jj
    obtain ⟨B', hB'⟩ := hψ.2 2 le_rfl
    set v : Fin 2 → EuclideanSpace ℝ (Fin q) := ![EuclideanSpace.single i 1, EuclideanSpace.single jj 1] with hv
    refine Integrable.of_bound (C := B' * ∏ k, ‖v k‖) ?_ ?_
    · have hc : Continuous fun x : EuclideanSpace ℝ (Fin q) => (S7PIL_ev v) (iteratedFDeriv ℝ 2 ψ (0 + x)) :=
        (S7PIL_ev v).continuous.comp
          ((hψ.1.continuous_iteratedFDeriv (by norm_num)).comp (continuous_const.add continuous_id))
      exact hc.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      refine ((iteratedFDeriv ℝ 2 ψ (0 + x)).le_opNorm v).trans ?_
      exact mul_le_mul_of_nonneg_right (hB' ⟨0 + x, rfl⟩) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  have e1 : ∀ i, ∑ jj, Δ i jj * ∫ x, iteratedFDeriv ℝ 2 ψ (0 + x)
      ![EuclideanSpace.single i 1, EuclideanSpace.single jj 1] ∂ν =
      ∫ x, ∑ jj, Δ i jj * iteratedFDeriv ℝ 2 ψ (0 + x)
        ![EuclideanSpace.single i 1, EuclideanSpace.single jj 1] ∂ν := by
    intro i
    rw [integral_finsetSum _ (fun jj _ => (hint i jj).const_mul _)]
    exact Finset.sum_congr rfl (fun jj _ => (integral_const_mul _ _).symm)
  have e2 : ∑ i, ∑ jj, Δ i jj * ∫ x, iteratedFDeriv ℝ 2 ψ (0 + x)
      ![EuclideanSpace.single i 1, EuclideanSpace.single jj 1] ∂ν =
      ∫ x, ∑ i, ∑ jj, Δ i jj * iteratedFDeriv ℝ 2 ψ (0 + x)
        ![EuclideanSpace.single i 1, EuclideanSpace.single jj 1] ∂ν := by
    rw [Finset.sum_congr rfl (fun i _ => e1 i)]
    exact (integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun jj _ => (hint i jj).const_mul _))).symm
  rw [e2]
  have hpt : ∀ x, ‖∑ i, ∑ jj, Δ i jj * iteratedFDeriv ℝ 2 ψ (0 + x)
        ![EuclideanSpace.single i 1, EuclideanSpace.single jj 1]‖ ≤ B * (cbNorm 5 Φ * ∏ k, ‖w k‖) := by
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
    refine (hB _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hB0
    refine (S7PIL_N_norm_le hΦ.1 hj w _).trans ?_
    exact mul_le_mul_of_nonneg_right (S7PIL_le_cbNorm hΦ (by omega) _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  have hn := norm_integral_le_of_norm_le_const (μ := ν)
    (f := fun x => ∑ i, ∑ jj, Δ i jj * iteratedFDeriv ℝ 2 ψ (0 + x)
        ![EuclideanSpace.single i 1, EuclideanSpace.single jj 1]) (Filter.Eventually.of_forall hpt)
  have hu : ν.real Set.univ = 1 := by simp
  rw [hu, mul_one] at hn
  rw [← Real.norm_eq_abs]
  exact hn

/-- The one-sided increment bound of the projected heat derivative. -/
theorem s102_projHeatD_incr (hT : 0 < T) (L : ℕ) (γ : ℝ → Measure (OscPath d m T))
    (hγp : ∀ u, IsProbabilityMeasure (γ u))
    (hγ : ∀ u ∈ Icc (0 : ℝ) T, IsR2FutureGaussian C m T u (γ u))
    (hG : S102GramInt C m hT L) {Cb : ℝ} (hCb0 : 0 ≤ Cb)
    (hCb : ∀ {ρ : ℝ}, ρ ∈ Icc (0 : ℝ) T → ∀ N : OscPath d m T [×2]→L[ℝ] ℝ,
      |∑ k, ∑ k', s102_rateM C m hT L ρ k k' *
        N ![s102_Lam T L (EuclideanSpace.single k (1 : ℝ)), s102_Lam T L (EuclideanSpace.single k' (1 : ℝ))]| ≤
          Cb * ‖N‖)
    (hD : S101Data C m T r c)
    (hρint : ∀ u ∈ Icc (0 : ℝ) T, Integrable (C.ρ u)) (hρnn : ∀ u ∈ Icc (0 : ℝ) T, ∀ x, 0 ≤ C.ρ u x)
    (hν : 0 ≤ C.ν) {Φ : OscPath d m T → ℝ} (hΦ : MemCb 5 Φ) {j : ℕ} (hj : j ≤ 3) {v u : ℝ}
    (hv : 0 ≤ v) (hvu : v ≤ u) (huT : u ≤ T) (y : OscPath d m T) :
    ‖s102_projHeatD γ Φ (s102_Pj T hT L) j u y - s102_projHeatD γ Φ (s102_Pj T hT L) j v y‖ ≤
      Cb / 2 * cbNorm 5 Φ * (u - v) := by
  have hu : u ∈ Icc (0 : ℝ) T := ⟨hv.trans hvu, huT⟩
  have hvT : v ∈ Icc (0 : ℝ) T := ⟨hv, hvu.trans huT⟩
  refine ContinuousMultilinearMap.opNorm_le_bound (by
    have := S7PIL_cbNorm_nonneg hΦ (0 : OscPath d m T)
    have h2 := sub_nonneg.2 hvu
    positivity) fun w => ?_
  rw [ContinuousMultilinearMap.sub_apply, s102_projHeatD_apply hT L γ hγp hγ hΦ hj hu,
    s102_projHeatD_apply hT L γ hγp hγ hΦ hj hvT]
  set ψ := S7PIL_psi (iteratedFDeriv ℝ j Φ) (s102_Pj T hT L y) (s102_Lam T L) w with hψdef
  have hψ : MemCb 2 ψ := S7PIL_psi_memCb hΦ hj _ _ w
  set S0 := s102_obsCov C m (s102_tauk hT L) (s102_alk L) u with hS0
  set Δ := s102_Delta C m hT L v u with hΔ
  have hS0p : S0.PosSemidef := (s102_obs_law C (hγ u hu) (s102_tauk hT L) (s102_alk L)).1
  have hΔp : Δ.PosSemidef := s102_Delta_psd hD hT L hG hρint hρnn hν hv hvu huT
  have hSv : s102_obsCov C m (s102_tauk hT L) (s102_alk L) v = S0 + Δ := by
    ext k k'
    rw [Matrix.add_apply]
    exact s102_obsCov_eq_rate hT L hG hv hvu huT k k'
  rw [hSv]
  have hK := fun θ (_ : θ ∈ Icc (0 : ℝ) 1) =>
    s102_delta_deriv_bound (s102_Lam T L) Δ (Cb * (u - v)) (mul_nonneg hCb0 (sub_nonneg.2 hvu))
      (fun N => by
        have := s102_Delta_bound hT L hG hCb hv hvu huT N
        exact this.trans (le_of_eq (by ring))) hΦ hj (s102_Pj T hT L y) w
      (multivariateGaussian 0 (S0 + (1 - θ) • Δ))
  have hint := s102_gauss_interp S0 Δ hS0p hΔp (G := ψ) hψ 0
    (K := Cb * (u - v) * (cbNorm 5 Φ * ∏ k, ‖w k‖)) hK
  have hint' : |∫ x, ψ (0 + x) ∂(multivariateGaussian 0 (S0 + Δ)) - ∫ x, ψ (0 + x) ∂(multivariateGaussian 0 S0)| ≤
      Cb * (u - v) * (cbNorm 5 Φ * ∏ k, ‖w k‖) / 2 := hint
  rw [show (∫ x, ψ x ∂(multivariateGaussian 0 S0)) = ∫ x, ψ (0 + x) ∂(multivariateGaussian 0 S0) by simp,
    show (∫ x, ψ x ∂(multivariateGaussian 0 (S0 + Δ))) =
      ∫ x, ψ (0 + x) ∂(multivariateGaussian 0 (S0 + Δ)) by simp]
  rw [norm_sub_rev, Real.norm_eq_abs]
  refine hint'.trans (le_of_eq ?_)
  ring

end HRS.MS.R2Interp

end
