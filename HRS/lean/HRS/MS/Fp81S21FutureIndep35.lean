import HRS.MS.Fp81S21FutureIndep34
import HRS.MS.Fp81S21RawIncr

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111 HRS.MS.S111X2 HRS.MS.GenPath

/-- Every retained combined-coordinate feature has a continuous time curve;
the increment bound is transferred between covariance representations. -/
theorem fp81s21_combined_coordinate_feature_continuous (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ [IsProbabilityMeasure (r26t3_mu R 0)]
      (Mg : ℝ) (K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0))
      (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg),
      ∀ H : ℝ, 0 < H → ∀ α : MultiIndex p.d,
        Continuous (fun t : Icc (0 : ℝ) H =>
          fp81s21_combinedFeature p R hK t (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) := by
  obtain ⟨δ0, hδ0, hhalf, hb⟩ := fp81s21_gaussian_combined_feature_increment_bound p
  refine ⟨δ0, hδ0, hhalf, ?_⟩
  intro δ hδ hδle R hμ Mg K hK H hH α
  obtain ⟨Mg', K', hK', B, g, g', c, gN, cN, hB, hg, hg', hc, hgN, hcN, hinc⟩ := hb δ hδ hδle R
  obtain ⟨L, hL, hsum, hbound⟩ := hinc H hH
  let F : Icc (0 : ℝ) H → Fp81S21GaussFeatureHilbert p R := fun t =>
    fp81s21_combinedFeature p R hK t (oscTestFun (wholeSpaceIndex p.d : ℝ) α)
  have hsq (s t : Icc (0 : ℝ) H) : ‖F t - F s‖ ^ 2 ≤ L α * |(t : ℝ) - s| := by
    have h1 := fp81s21_combinedFeature_increment_sq_cov p hδ (hδle.trans hhalf)
      R hK s t s.property.1 t.property.1 (oscTestFun (wholeSpaceIndex p.d : ℝ) α)
      (s56_isOscTest (wholeSpaceIndex p.d : ℝ) α)
    have h2 := fp81s21_combinedFeature_increment_sq_cov p hδ (hδle.trans hhalf)
      R hK' s t s.property.1 t.property.1 (oscTestFun (wholeSpaceIndex p.d : ℝ) α)
      (s56_isOscTest (wholeSpaceIndex p.d : ℝ) α)
    have hh := hbound 0 le_rfl s s.property t t.property α
    calc
      _ = ‖fp81s21_combinedFeature p R hK' t (oscTestFun (wholeSpaceIndex p.d : ℝ) α) -
            fp81s21_combinedFeature p R hK' s (oscTestFun (wholeSpaceIndex p.d : ℝ) α)‖ ^ 2 := h1.trans h2.symm
      _ ≤ _ := by simpa using hh
  change Continuous F
  rw [Metric.continuous_iff]
  intro s ε hε
  have hLa : 0 ≤ L α := hL α
  refine ⟨ε ^ 2 / (L α + 1), by positivity, ?_⟩
  intro t ht
  have hdist : |(t : ℝ) - s| < ε ^ 2 / (L α + 1) := by
    change dist (t : ℝ) (s : ℝ) < _ at ht
    simpa [Real.dist_eq] using ht
  have hh := hL α
  have hnorm := hsq s t
  have hsmall : L α * |(t : ℝ) - s| < ε ^ 2 := by
    have he := (lt_div_iff₀ (show 0 < L α + 1 by linarith)).1 hdist
    nlinarith [abs_nonneg ((t : ℝ) - s)]
  have : ‖F t - F s‖ < ε := by nlinarith [norm_nonneg (F t - F s)]
  simpa [dist_eq_norm] using this

#print axioms fp81s21_combined_coordinate_feature_continuous
end HRS.Fp81.S21
end
