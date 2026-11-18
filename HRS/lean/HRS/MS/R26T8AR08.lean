import HRS.MS.CritForceAssemblyMaj
import HRS.MS.S82P2Dis4
import HRS.MS.S82P2Sum3

/-!
# S8.2 observed-time layer, packet T8A.R08: positive finite pinned partition functions

For a calibrated reference exponent with nonnegative short-range kernel `q`, the one-body part is at most `1 + 1/1000`
per particle (small row and `|h| ≤ 1`), while the pair and pin interactions are nonpositive. Hence the exponential of
the reference exponent is bounded and measurable on the finite product of the thermal density, so it is integrable,
and its integral is strictly positive.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_pinned_partition {d p n : ℕ} (hd : 2 ≤ d) {a beta C0 : ℝ}
    (hbeta : 0 < beta) {rho q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (hcal : CalibratedReferenceData d a beta rho q h C0) (N : ℕ) (hN : 2 ≤ N)
    (hnp : n + p ≤ N) (pins : Fin p → Euc d) :
    Integrable (fun X => Real.exp (referenceExponent q h (HRS.Whole.withDensityReal rho) beta N pins X))
      (Measure.pi (fun _ : Fin n => HRS.Whole.withDensityReal rho)) ∧
    0 < ∫ X, Real.exp (referenceExponent q h (HRS.Whole.withDensityReal rho) beta N pins X)
      ∂Measure.pi (fun _ : Fin n => HRS.Whole.withDensityReal rho) := by
  haveI hprob : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) :=
    HRS.Whole.Q09A.measure_isProb hrho.2.1
  have hq : Measurable q := hcal.short.measurable
  have hqn : ∀ z, 0 ≤ q z := hcal.short.nonneg
  have hconv : Measurable (HRS.Whole.convMeasure q (HRS.Whole.withDensityReal rho)) :=
    HRS.MS.S82P2.s82p2_conv_measurable hq _
  set g : HRS.Whole.EucConfig d n → ℝ := fun X => referenceExponent q h (HRS.Whole.withDensityReal rho) beta N pins X with hg
  have hgm : Measurable g := by
    rw [hg]
    have hhN : Measurable (h N) := hcal.hmeas N
    simp only [HRS.MS.Phase2S82.referenceExponent, HRS.MS.Phase2S82.pairSum]
    fun_prop
  -- uniform bound on the exponent
  have hbnd : ∀ X : HRS.Whole.EucConfig d n, g X ≤ (n : ℝ) * (1 + 1 / 1000) := by
    intro X
    rw [hg]
    simp only [HRS.MS.Phase2S82.referenceExponent, HRS.MS.Phase2S82.pairSum]
    have h1 : ∑ i, (beta * HRS.Whole.convMeasure q (HRS.Whole.withDensityReal rho) (X i) + h N (X i)) ≤
        (n : ℝ) * (1 + 1 / 1000) := by
      calc ∑ i, (beta * HRS.Whole.convMeasure q (HRS.Whole.withDensityReal rho) (X i) + h N (X i))
          ≤ ∑ _i : Fin n, (1 + 1 / 1000 : ℝ) := by
            refine Finset.sum_le_sum fun i _ => ?_
            have hs := hcal.small_row (X i)
            have hh := (abs_le.1 (hcal.hsmall N hN (X i))).2
            linarith
        _ = (n : ℝ) * (1 + 1 / 1000) := by simp; ring
    have h2 : 0 ≤ (beta / (2 * N)) * ∑ i, ∑ j ∈ Finset.univ.erase i, q (X i - X j) := by
      refine mul_nonneg (div_nonneg hbeta.le (by positivity)) (Finset.sum_nonneg fun i _ => ?_)
      exact Finset.sum_nonneg fun j _ => hqn _
    have h3 : 0 ≤ (beta / N) * ∑ i, ∑ j, q (X i - pins j) := by
      refine mul_nonneg (div_nonneg hbeta.le (by positivity)) (Finset.sum_nonneg fun i _ => ?_)
      exact Finset.sum_nonneg fun j _ => hqn _
    linarith
  have hbd : ∀ X : HRS.Whole.EucConfig d n,
      ‖Real.exp (g X)‖ ≤ Real.exp ((n : ℝ) * (1 + 1 / 1000)) := by
    intro X
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (hbnd X)
  have hint : Integrable (fun X => Real.exp (g X))
      (Measure.pi (fun _ : Fin n => HRS.Whole.withDensityReal rho)) :=
    Integrable.of_bound (Real.measurable_exp.comp hgm).aestronglyMeasurable _
      (Filter.Eventually.of_forall hbd)
  refine ⟨hint, ?_⟩
  rw [integral_pos_iff_support_of_nonneg (fun X => (Real.exp_pos _).le) hint]
  have hsupp : Function.support (fun X => Real.exp (g X)) = Set.univ :=
    Set.eq_univ_of_forall fun X => (Real.exp_pos _).ne'
  rw [hsupp, measure_univ]
  exact one_pos

end HRS.MS.R26T8A

end
