import HRS.MS.Fp81S21RankKernel2

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.Fp81.S21

open HRS.Whole
open HRS.MS.R26T3

/-- An `L²` bound on a real difference implies the corresponding mean-square error,
including integrability of the squared error. -/
theorem fp81s21_SqErr_of_eLpNorm_sub
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f g : Ω → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hfg : Measurable (fun ω => f ω - g ω))
    (hL2 : eLpNorm (fun ω => f ω - g ω) 2 P ≤ ENNReal.ofReal ε) :
    fp81s21_SqErr P f g ε := by
  let e : Ω → ℝ := fun ω => f ω - g ω
  have he : Measurable e := hfg
  have heAE : AEStronglyMeasurable e P := he.aestronglyMeasurable
  have hPowerEq : (∫⁻ ω, ENNReal.ofReal (‖e ω‖ ^ 2) ∂P) =
      eLpNorm e 2 P ^ 2 := by
    have h := HRS.MS.R2Chaos.s94_lintegral_sq_eq heAE
    calc
      ∫⁻ ω, ENNReal.ofReal (‖e ω‖ ^ 2) ∂P =
          ∫⁻ ω, ‖e ω‖ₑ ^ 2 ∂P := by
            refine lintegral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
            calc
              ENNReal.ofReal (‖e ω‖ ^ 2) = ENNReal.ofReal (|e ω| ^ 2) := by
                rw [Real.norm_eq_abs]
              _ = ENNReal.ofReal |e ω| ^ 2 := by
                rw [ENNReal.ofReal_pow (abs_nonneg _)]
              _ = ‖e ω‖ₑ ^ 2 := by rw [Real.enorm_eq_ofReal_abs]
      _ = eLpNorm e 2 P ^ 2 := h
  have hPower : ∫⁻ ω, ENNReal.ofReal (‖e ω‖ ^ 2) ∂P ≤ ENNReal.ofReal (ε ^ 2) := by
    rw [hPowerEq]
    calc
      eLpNorm e 2 P ^ 2 ≤ ENNReal.ofReal ε ^ 2 := pow_le_pow_left' hL2 2
      _ = ENNReal.ofReal (ε ^ 2) := by rw [ENNReal.ofReal_pow hε]
  have hNonneg : ∀ ω, 0 ≤ ‖e ω‖ ^ 2 := fun ω => by positivity
  have hIntegrable : Integrable (fun ω => ‖e ω‖ ^ 2) P := by
    refine ⟨((measurable_norm.comp he).pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hNonneg)]
    exact lt_of_le_of_lt hPower ENNReal.ofReal_lt_top
  refine ⟨hIntegrable, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hNonneg)
    hIntegrable.aestronglyMeasurable]
  have hReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hPower
  rwa [ENNReal.toReal_ofReal (sq_nonneg ε)] at hReal

/-- A Gibbs law is an actual law with any exponent above one and any density bound
at least one, since its Radon--Nikodym derivative with respect to itself is one. -/
theorem fp81s21_gibbs_actualDensity
    {d N : ℕ} {s b p K : ℝ} {μ : Measure (Euc d)}
    {Q : Measure (EucConfig d N)}
    (hQprob : IsProbabilityMeasure Q)
    (hQ : Q = HRS.Whole.modulatedGibbs (rieszKernel d s) N b μ)
    (hp : 1 < p) (hK : 1 ≤ K) :
    HasR2ActualDensity s b p K μ Q := by
  refine ⟨hQprob, hQ ▸ Measure.AbsolutelyContinuous.refl _, ?_⟩
  rw [← hQ]
  have hOne : (fun X => ((Q.rnDeriv Q) X).toReal) =ᵐ[Q] fun _ => (1 : ℝ) := by
    filter_upwards [Measure.rnDeriv_self Q] with X hX
    simp [hX]
  have hConst : eLpNorm (fun _ : EucConfig d N => (1 : ℝ)) (ENNReal.ofReal p) Q = 1 := by
    rw [eLpNorm_const _ (ENNReal.ofReal_pos.2 (by linarith : 0 < p)).ne'
      (IsProbabilityMeasure.ne_zero Q)]
    simp
  rw [eLpNorm_congr_ae hOne, hConst]
  simpa using ENNReal.ofReal_le_ofReal hK

#print axioms fp81s21_SqErr_of_eLpNorm_sub
#print axioms fp81s21_gibbs_actualDensity

end HRS.Fp81.S21
