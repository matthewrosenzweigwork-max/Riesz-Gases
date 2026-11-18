import HRS.Uniform.Q45Fnl1

/-!
# Q45: assembly of Proposition 3.21 (the discrepancy as an `ℝ≥0∞`-integral)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]

lemma lintegral_disc_eq {ℱ : Filtration ℝ mΩ} {T : ℝ} {M : ℝ → Ω → H}
    {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)} (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg)
    {Cb : ℝ → (H →L[ℝ] H →L[ℝ] ℝ)} (hCb : IsDetCovDensity T Cb) :
    ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (Sg r ω - Cb r))) ∂P =
      ENNReal.ofReal (covDiscrepancy P T Sg Cb) := by
  have hint := discrepancy_integrable P hM hCb
  have hpath := discrepancy_pathint P hM hCb
  unfold covDiscrepancy
  rw [ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun ω => setIntegral_nonneg measurableSet_Icc fun σ _ => traceNormForm_nonneg _)]
  refine lintegral_congr_ae ?_
  filter_upwards [hpath] with ω hω
  rw [ofReal_integral_eq_lintegral_ofReal hω.1
    (ae_of_all _ fun σ => traceNormForm_nonneg _)]

end HRS.Uniform.Q45
