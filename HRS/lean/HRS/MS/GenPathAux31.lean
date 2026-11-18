import HRS.MS.GenPathAux30

/-!
# S5.6 packet P4c: `Ξ_N` is continuous in the configuration and (a.s.) in time
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.GenPath

open HRS.Whole HRS.MP.RdRem

variable {d : ℕ}

theorem s56_oscTestFun_bound (m : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α : MultiIndex d) (x : Euc d), |oscTestFun m α x| ≤ C * oscEigenvalue d α ^ (-(m / 2)) := by
  obtain ⟨C, hC⟩ := hermiteFunD_uniform_bound (d := d)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC (fun _ => 0) 0)
  refine ⟨C, hC0, fun α x => ?_⟩
  unfold oscTestFun
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (oscEigenvalue_pos α).le _), mul_comm]
  exact mul_le_mul_of_nonneg_right (hC α x) (Real.rpow_nonneg (oscEigenvalue_pos α).le _)

theorem s56_oscTestFun_cont (m : ℝ) (α : MultiIndex d) : Continuous (oscTestFun m α) :=
  (contDiff_const.mul (contDiff_hermiteFunD α)).continuous

theorem s56_xi_coord_bound {m : ℝ} (σ C : ℝ) (hC : ∀ (α : MultiIndex d) (x : Euc d),
      |oscTestFun m α x| ≤ C * oscEigenvalue d α ^ (-(m / 2)))
    (μ ν : Measure (Euc d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hm : (d : ℝ) < m)
    (α : MultiIndex d) :
    |OscDual.coord (σ • OscDual.ofMeasureDiff m μ ν) α| ≤ 2 * |σ| * (C * oscEigenvalue d α ^ (-(m / 2))) := by
  rw [OscDual.coord_smul, s56_coord_ofMeasureDiff hm, abs_mul]
  have h1 : ∀ κ : Measure (Euc d), IsProbabilityMeasure κ →
      |∫ x, oscTestFun m α x ∂κ| ≤ C * oscEigenvalue d α ^ (-(m / 2)) := by
    intro κ hκ
    have := norm_integral_le_of_norm_le_const (μ := κ) (f := oscTestFun m α)
      (C := C * oscEigenvalue d α ^ (-(m / 2))) (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hC α x)
    simpa [Real.norm_eq_abs] using this
  have := abs_sub (∫ x, oscTestFun m α x ∂μ) (∫ x, oscTestFun m α x ∂ν)
  have hh := add_le_add (h1 μ inferInstance) (h1 ν inferInstance)
  nlinarith [abs_nonneg σ, abs_nonneg (∫ x, oscTestFun m α x ∂μ - ∫ x, oscTestFun m α x ∂ν)]

theorem s56_summable_bound {m : ℝ} (hd : 1 ≤ d) (hm : (d : ℝ) < m) (c : ℝ) :
    Summable fun α : MultiIndex d => (c * oscEigenvalue d α ^ (-(m / 2))) ^ 2 := by
  have := (summable_oscEigenvalue_rpow_iff hd m).2 hm
  refine (this.mul_left (c ^ 2)).congr fun α => ?_
  have h2 : (oscEigenvalue d α ^ (-(m / 2))) ^ 2 = oscEigenvalue d α ^ (-m) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (oscEigenvalue_pos α).le]
    congr 1
    push_cast
    ring
  rw [mul_pow, h2]

/-- The fluctuation field is continuous in the configuration. -/
theorem s56_xi_cont_config {m : ℝ} (hd : 1 ≤ d) (hm : (d : ℝ) < m) (σ : ℝ) {N : ℕ} (hN : 0 < N)
    (ν : Measure (Euc d)) [IsProbabilityMeasure ν] :
    Continuous fun x : EucConfig d N =>
      σ • OscDual.ofMeasureDiff m (HRS.Whole.empirical x) ν := by
  obtain ⟨C, hC0, hC⟩ := s56_oscTestFun_bound (d := d) m
  refine s56_osc_cont_of_coord _ (fun α => 2 * |σ| * (C * oscEigenvalue d α ^ (-(m / 2))))
    ?_ (fun α => ?_) (fun x α => ?_)
  · simpa [mul_assoc] using (s56_summable_bound hd hm (2 * |σ| * C)).congr fun α => by ring
  · have : ∀ x : EucConfig d N, OscDual.coord (σ • OscDual.ofMeasureDiff m (HRS.Whole.empirical x) ν) α =
        σ * ((N : ℝ)⁻¹ * ∑ i, oscTestFun m α (x i) - ∫ y, oscTestFun m α y ∂ν) := by
      intro x
      have := HRS.Whole.empirical_isProbabilityMeasure hN x
      rw [OscDual.coord_smul, s56_coord_ofMeasureDiff hm]
      congr 2
      exact HRS.Whole.pair_empirical hN x (oscTestFun m α)
    simp_rw [this]
    refine continuous_const.mul (Continuous.sub (continuous_const.mul ?_) continuous_const)
    exact continuous_finsetSum _ fun i _ => (s56_oscTestFun_cont m α).comp (continuous_apply i)
  · have := HRS.Whole.empirical_isProbabilityMeasure hN x
    exact s56_xi_coord_bound σ C hC _ ν hm α

end HRS.MS.GenPath
