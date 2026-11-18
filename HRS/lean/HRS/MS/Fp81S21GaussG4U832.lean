import HRS.MS.Fp81S21CovCoreBound

/-!
# HRS S2.1(iii), G4 U832: centered variance domination

For probability measures ordered by a scalar measure bound, compare centered
variances by centering both functions at the reference-measure mean, applying
measure domination to that common square, and using that variance minimizes
mean-square error over constant centers.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS (Euc)

/-- Centered variance is dominated under a scalar comparison of probability
measures.  The `MemLp` hypotheses provide the finite second moments needed for
both centered variances. -/
theorem fp81s21_g4_centered_variance_domination
    {d : ℕ} {μ ν : Measure (Euc d)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {K : ℝ} (hK : 0 ≤ K) (hμν : μ ≤ ENNReal.ofReal K • ν)
    {f : Euc d → ℝ} (hfμ : MemLp f 2 μ) (hfν : MemLp f 2 ν) :
    HRS.MS.S111X2.s111x2_centeredSquare μ f ≤
      K * HRS.MS.S111X2.s111x2_centeredSquare ν f := by
  let g : Euc d → ℝ := fun x => f x - HRS.Whole.pair ν f
  have hgm : MemLp g 2 μ := hfμ.sub (memLp_const _)
  have hgn : MemLp g 2 ν := hfν.sub (memLp_const _)
  have hvarμ :
      HRS.MS.S111X2.s111x2_centeredSquare μ f = ProbabilityTheory.variance f μ := by
    unfold HRS.MS.S111X2.s111x2_centeredSquare
    rw [ProbabilityTheory.variance_eq_integral hfμ.aemeasurable]
    rfl
  have hshift : ProbabilityTheory.variance f μ = ProbabilityTheory.variance g μ := by
    simpa [g, sub_eq_add_neg] using
      (ProbabilityTheory.variance_add_const hfμ.aestronglyMeasurable
        (-HRS.Whole.pair ν f)).symm
  have hvarle : ProbabilityTheory.variance g μ ≤ ∫ x, g x ^ 2 ∂μ :=
    ProbabilityTheory.variance_le_expectation_sq hgm.aestronglyMeasurable
  have hscaled : Integrable (fun x => g x ^ 2) (ENNReal.ofReal K • ν) :=
    hgn.integrable_sq.smul_measure ENNReal.ofReal_ne_top
  have hmeasure := integral_mono_measure hμν
    (Filter.Eventually.of_forall fun x => sq_nonneg (g x)) hscaled
  rw [integral_smul_measure, ENNReal.toReal_ofReal hK, smul_eq_mul] at hmeasure
  calc
    HRS.MS.S111X2.s111x2_centeredSquare μ f = ProbabilityTheory.variance f μ := hvarμ
    _ = ProbabilityTheory.variance g μ := hshift
    _ ≤ ∫ x, g x ^ 2 ∂μ := hvarle
    _ ≤ K * ∫ x, g x ^ 2 ∂ν := hmeasure
    _ = K * HRS.MS.S111X2.s111x2_centeredSquare ν f := by
      simp [g, HRS.MS.S111X2.s111x2_centeredSquare, HRS.Whole.projMean]

#print axioms fp81s21_g4_centered_variance_domination

end HRS.Fp81.S21
