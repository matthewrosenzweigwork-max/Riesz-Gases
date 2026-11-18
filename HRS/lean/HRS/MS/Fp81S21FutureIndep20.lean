import HRS.MS.Fp81S21FutureIndep19
import HRS.MS.Fp81S21MovingNoiseBounds2

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111

/-- The feature curve of each oscillator coordinate is continuous on the
physical horizon, under the radius supplied by the existing increment bound. -/
theorem fp81s21_future_coordinate_feature_continuous (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ H : ℝ, 0 < H → ∀ r ∈ Icc (0 : ℝ) H,
      ∀ α : MultiIndex p.d,
        Continuous (fun t : Icc (0 : ℝ) H =>
          fp81s21_futureNoiseSourceFeature p R r t
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) := by
  obtain ⟨δ0, hδ0, hδhalf, hb⟩ := movingNoiseFeature_bounds p
  refine ⟨δ0, hδ0, hδhalf, ?_⟩
  intro δ hδ hδle R H hH r hr α
  obtain ⟨L, hL, hinc⟩ := (hb δ hδ hδle R H hH).2.2
  let F : Icc (0 : ℝ) H → Fp81S21GaussFeatureHilbert p R := fun t =>
    fp81s21_futureNoiseSourceFeature p R r t (oscTestFun (wholeSpaceIndex p.d : ℝ) α)
  have hsq (s t : Icc (0 : ℝ) H) : ‖F t - F s‖ ^ 2 ≤ L * |(t : ℝ) - s| := by
    have hsum := hinc r hr s s.property t t.property
    have hα := hsum.1.le_tsum α (fun _ _ => sq_nonneg _)
    have hn : ‖F t - F s‖ ^ 2 =
        ‖movingNoiseCoordinate R r t α - movingNoiseCoordinate R r s α‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
      have hp := WithLp.prod_inner_apply (𝕜 := ℝ) (F t - F s) (F t - F s)
      simpa [F, fp81s21_futureNoiseSourceFeature, movingNoiseCoordinate] using hp
    rw [hn]
    exact hα.trans hsum.2
  change Continuous F
  rw [Metric.continuous_iff]
  intro s ε hε
  refine ⟨ε ^ 2 / (L + 1), by positivity, ?_⟩
  intro t ht
  have hdist : |(t : ℝ) - s| < ε ^ 2 / (L + 1) := by
    change dist (t : ℝ) (s : ℝ) < _ at ht
    simpa [Real.dist_eq] using ht
  have hbound := hsq s t
  have hp : L * |(t : ℝ) - s| < ε ^ 2 := by
    have : |(t : ℝ) - s| * (L + 1) < ε ^ 2 := (lt_div_iff₀ (by linarith)).1 hdist
    nlinarith [abs_nonneg ((t : ℝ) - s)]
  have hn : ‖F t - F s‖ < ε := by nlinarith [norm_nonneg (F t - F s)]
  simpa [dist_eq_norm] using hn

#print axioms fp81s21_future_coordinate_feature_continuous
end HRS.Fp81.S21
end
