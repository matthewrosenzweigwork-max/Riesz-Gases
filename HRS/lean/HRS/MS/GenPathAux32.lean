import HRS.MS.GenPathAux31

/-!
# S5.6 packet P4d: `t ↦ Ξ_N^t` is continuous on `[0,T]` (`B_m`-valued) for continuous particle paths
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.GenPath

open HRS.Whole HRS.MP.RdRem

variable {d : ℕ}

theorem s56_xi_cont_time {m : ℝ} (hd : 1 ≤ d) (hm : (d : ℝ) < m) (σ : ℝ) {N : ℕ} (hN : 0 < N) {T : ℝ}
    (ρ : ℝ → Euc d → ℝ) (hprob : ∀ t ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (ρ t))
    (hcont : ∀ ψ : Euc d → ℝ, Continuous ψ → (∃ B, ∀ x, |ψ x| ≤ B) →
      ContinuousOn (fun r => ∫ x, ψ x * ρ r x) (Set.Icc (0 : ℝ) T))
    (x : ℝ → EucConfig d N) (hx : ∀ i, Continuous fun t => x t i) :
    ContinuousOn (fun t => σ • OscDual.ofMeasureDiff m (HRS.Whole.empirical (x t))
      (HRS.Whole.withDensityReal (ρ t))) (Set.Icc (0 : ℝ) T) := by
  obtain ⟨C, hC0, hC⟩ := s56_oscTestFun_bound (d := d) m
  rw [continuousOn_iff_continuous_restrict]
  refine s56_osc_cont_of_coord _ (fun α => 2 * |σ| * (C * oscEigenvalue d α ^ (-(m / 2))))
    ?_ (fun α => ?_) (fun y α => ?_)
  · simpa [mul_assoc] using (s56_summable_bound hd hm (2 * |σ| * C)).congr fun α => by ring
  · have hφ := s56_oscTestFun_cont m α
    have hbd : ∃ B, ∀ z, |oscTestFun m α z| ≤ B :=
      ⟨C * oscEigenvalue d α ^ (-(m / 2)), fun z => hC α z⟩
    have h2 := (hcont _ hφ hbd)
    have h3 : ContinuousOn (fun t => σ * ((N : ℝ)⁻¹ * ∑ i, oscTestFun m α (x t i) -
        ∫ z, oscTestFun m α z * ρ t z)) (Set.Icc (0 : ℝ) T) := by
      refine continuousOn_const.mul (ContinuousOn.sub (continuousOn_const.mul ?_) h2)
      exact (continuous_finsetSum _ fun i _ => hφ.comp (hx i)).continuousOn
    rw [continuousOn_iff_continuous_restrict] at h3
    refine h3.congr fun y => ?_
    obtain ⟨t, ht⟩ := y
    have hpr := hprob t ht
    haveI := HRS.MS.Thm.cb_withDensityReal_isProb hpr
    haveI := HRS.Whole.empirical_isProbabilityMeasure hN (x t)
    simp only [Set.restrict_apply]
    rw [OscDual.coord_smul, s56_coord_ofMeasureDiff hm,
      mrr_integral_withDensityReal (ρ t) hpr.measurable hpr.nonneg]
    congr 2
    · exact (HRS.Whole.pair_empirical hN (x t) (oscTestFun m α)).symm
    · refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only []; ring
  · obtain ⟨t, ht⟩ := y
    haveI := HRS.MS.Thm.cb_withDensityReal_isProb (hprob t ht)
    haveI := HRS.Whole.empirical_isProbabilityMeasure hN (x t)
    exact s56_xi_coord_bound σ C hC _ _ hm α

end HRS.MS.GenPath
