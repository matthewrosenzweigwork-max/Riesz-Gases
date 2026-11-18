import HRS.MS.PROS15EChaosTiltContinuity
import HRS.Prob.Gaussian

/-! Conversion of reference Gaussian L² convergence into normalized tilted L²
convergence for the closed quadratic Gaussian chaos. -/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS.MC.E213U13

theorem s15e_second_chaos_tilted_of_tendstoL2
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} {hξ : IsStdGaussianSeq P ξ}
    {V : Ω → ℝ}
    (hV : AEMeasurable V P)
    (hExp2 : Integrable (fun ω => Real.exp (-(2 * V ω))) P)
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hY : ∀ n, InQ2 hξ (Y n)) (hZ : InQ2 hξ Z)
    (hT : HRS.TendstoL2 P Y Z) :
    Tendsto (fun n => ∫ ω, (Y n ω - Z ω) ^ 2
      ∂(r26t3_tilt P V)) atTop (𝓝 0) := by
  have hDiff : ∀ n, MemLp (fun ω => Y n ω - Z ω) 2 P :=
    fun n => (hY n).1.sub hZ.1
  have hId : ∀ n, ENNReal.ofReal
      (∫ ω, (Y n ω - Z ω) ^ 2 ∂P) =
      ∫⁻ ω, ‖Y n ω - Z ω‖ₑ ^ 2 ∂P := by
    intro n
    rw [ofReal_integral_eq_lintegral_ofReal (hDiff n).integrable_sq
      (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
    refine lintegral_congr fun ω => ?_
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
      Real.norm_eq_abs, sq_abs]
  have hIdR : ∀ n, ∫ ω, (Y n ω - Z ω) ^ 2 ∂P =
      (∫⁻ ω, ‖Y n ω - Z ω‖ₑ ^ 2 ∂P).toReal := by
    intro n
    calc
      (∫ ω, (Y n ω - Z ω) ^ 2 ∂P) =
        (ENNReal.ofReal (∫ ω, (Y n ω - Z ω) ^ 2 ∂P)).toReal :=
          (ENNReal.toReal_ofReal (integral_nonneg fun ω => sq_nonneg _)).symm
      _ = _ := by rw [hId n]
  have hRef : Tendsto (fun n => ∫ ω, (Y n ω - Z ω) ^ 2 ∂P)
      atTop (𝓝 0) := by
    have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hT.2
    change Tendsto (fun n =>
      (∫⁻ ω, ‖Y n ω - Z ω‖ₑ ^ 2 ∂P).toReal) atTop (𝓝 0) at ht
    simpa only [ENNReal.toReal_zero, ← hIdR] using ht
  exact s15e_second_chaos_tilted_second_convergence P hV hExp2
    Y Z hY hZ hRef

#print axioms s15e_second_chaos_tilted_of_tendstoL2
end HRS.MS.R26T3
