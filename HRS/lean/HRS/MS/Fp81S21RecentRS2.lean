import HRS.MS.Fp81S21RecentRS

/-!
# S2.1(iii), packet 34a: measurable and integrable RS values

The operator-family Lipschitz hypothesis makes the RS functional jointly
continuous on the prediction and variation carriers.  Consequently it is
measurable on their product carrier, and its absolute value is integrable
whenever the two variation norms are integrable.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory

namespace HRS.Fp81.S21

/-- Product-carrier form of the paired recent RS value. -/
def fp81s21_recentRSProductValue {C D J : Type*}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup J] [NormedSpace ℝ J] {C_RS : ℝ}
    (F : fp81s21_RecentRSFunctional C D J C_RS) (z : C × (D × J)) : ℝ :=
  fp81s21_recentRSValue F z.1 z.2.1 z.2.2

/-- Joint continuity of the abstract RS value on the path and variation
product carrier. -/
theorem fp81s21_recentRSProductValue_continuous
    {C D J : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup J] [NormedSpace ℝ J] {C_RS : ℝ}
    (F : fp81s21_RecentRSFunctional C D J C_RS) :
    Continuous (fp81s21_recentRSProductValue F) := by
  have hKd : Continuous F.driftKernel :=
    LipschitzWith.continuous (LipschitzWith.of_dist_le_mul
      (K := ⟨C_RS, F.constant_nonneg⟩) fun y y' => by
      change dist (F.driftKernel y) (F.driftKernel y') ≤ C_RS * dist y y'
      simpa [dist_eq_norm] using F.drift_lipschitz y y')
  have hKj : Continuous F.covarianceKernel :=
    LipschitzWith.continuous (LipschitzWith.of_dist_le_mul
      (K := ⟨C_RS, F.constant_nonneg⟩) fun y y' => by
      change dist (F.covarianceKernel y) (F.covarianceKernel y') ≤ C_RS * dist y y'
      simpa [dist_eq_norm] using F.covariance_lipschitz y y')
  have hEvalD : Continuous fun z : (D →L[ℝ] ℝ) × D => z.1 z.2 :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := D) (F := ℝ)).continuous
  have hEvalJ : Continuous fun z : (J →L[ℝ] ℝ) × J => z.1 z.2 :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := J) (F := ℝ)).continuous
  have hd : Continuous (fun z : C × (D × J) => F.driftKernel z.1 z.2.1) := by
    exact hEvalD.comp ((hKd.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd))
  have hj : Continuous (fun z : C × (D × J) => F.covarianceKernel z.1 z.2.2) := by
    exact hEvalJ.comp ((hKj.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd))
  change Continuous (fun z : C × (D × J) =>
    F.driftKernel z.1 z.2.1 + F.covarianceKernel z.1 z.2.2)
  exact hd.add hj

/-- Measurability of the integral value on the product carrier. -/
theorem fp81s21_recentRSProductValue_measurable
    {C D J : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup J] [NormedSpace ℝ J]
    [MeasurableSpace C] [SecondCountableTopology C] [BorelSpace C]
    [MeasurableSpace D] [SecondCountableTopology D] [BorelSpace D]
    [MeasurableSpace J] [SecondCountableTopology J] [BorelSpace J] {C_RS : ℝ}
    (F : fp81s21_RecentRSFunctional C D J C_RS) :
    Measurable (fp81s21_recentRSProductValue F) :=
  (fp81s21_recentRSProductValue_continuous F).measurable

/-- Measurability after inserting three measurable random inputs. -/
theorem fp81s21_recentRSValue_measurable
    {C D J Ω : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup J] [NormedSpace ℝ J]
    [MeasurableSpace Ω]
    [MeasurableSpace C] [SecondCountableTopology C] [BorelSpace C]
    [MeasurableSpace D] [SecondCountableTopology D] [BorelSpace D]
    [MeasurableSpace J] [SecondCountableTopology J] [BorelSpace J] {C_RS : ℝ}
    (F : fp81s21_RecentRSFunctional C D J C_RS)
    {y : Ω → C} {d : Ω → D} {j : Ω → J}
    (hy : Measurable y) (hd : Measurable d) (hj : Measurable j) :
    Measurable (fun ω => fp81s21_recentRSValue F (y ω) (d ω) (j ω)) := by
  have hpair : Measurable (fun ω : Ω => Prod.mk (y ω) (Prod.mk (d ω) (j ω))) :=
    hy.prodMk (hd.prodMk hj)
  exact (fp81s21_recentRSProductValue_measurable F).comp hpair

/-- Integrability of RS values follows from integrability of the two variation
norms. -/
theorem fp81s21_recentRSProductValue_integrable
    {C D J : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup J] [NormedSpace ℝ J]
    [MeasurableSpace C] [SecondCountableTopology C] [BorelSpace C]
    [MeasurableSpace D] [SecondCountableTopology D] [BorelSpace D]
    [MeasurableSpace J] [SecondCountableTopology J] [BorelSpace J] {C_RS : ℝ}
    (F : fp81s21_RecentRSFunctional C D J C_RS)
    (μ : Measure (C × (D × J)))
    (hd : Integrable (fun z : C × (D × J) => ‖z.2.1‖) μ)
    (hj : Integrable (fun z : C × (D × J) => ‖z.2.2‖) μ) :
    Integrable (fp81s21_recentRSProductValue F) μ := by
  have hsum : Integrable (fun z : C × (D × J) => ‖z.2.1‖ + ‖z.2.2‖) μ := hd.add hj
  have hbound : Integrable
      (fun z : C × (D × J) => C_RS * (‖z.2.1‖ + ‖z.2.2‖)) μ := by
    simpa using hsum.const_mul C_RS
  have hmeas := fp81s21_recentRSProductValue_measurable F
  exact hbound.mono' hmeas.aestronglyMeasurable (ae_of_all μ fun z => by
    rw [Real.norm_eq_abs]
    simpa [fp81s21_recentRSProductValue, fp81s21_recentRSTotalVariation] using
      fp81s21_recentRS_linear_bound F z.1 z.2.1 z.2.2)

#print axioms fp81s21_recentRSProductValue_continuous
#print axioms fp81s21_recentRSProductValue_measurable
#print axioms fp81s21_recentRSValue_measurable
#print axioms fp81s21_recentRSProductValue_integrable

end HRS.Fp81.S21

end
