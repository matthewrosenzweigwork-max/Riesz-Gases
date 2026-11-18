import HRS.MS.Fp81S21CenteredAdapter
import HRS.ME.BiasC

/-!
# S2.1(iii), centered adapter: Banach barycenters and W₁ centering

The generic theorem below states the SOL30 centering bound for integrable
Banach-valued random variables. Its proof uses the barycenter estimate obtained
by testing against a norming functional, followed by translation and the
Wasserstein triangle inequality.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HRS.Fp81.S21

open HRS

/-- The distance between Bochner barycenters is bounded by `W₁`. -/
theorem fp81s21_barycenter_wasserstein
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B] [CompleteSpace B]
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Q : Measure Ω'} [IsProbabilityMeasure Q]
    (Y : Ω → B) (Z : Ω' → B)
    (hY : Integrable Y P) (hZ : Integrable Z Q) :
    ENNReal.ofReal ‖(∫ ω, Y ω ∂P) - (∫ ω, Z ω ∂Q)‖ ≤
      wassersteinE 1 (law P Y) (law Q Z) := by
  let μ : Measure B := law P Y
  let ν : Measure B := law Q Z
  have hμp : IsProbabilityMeasure μ := by
    dsimp [μ, law]
    exact (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).2 inferInstance
  have hνp : IsProbabilityMeasure ν := by
    dsimp [ν, law]
    exact (Measure.isProbabilityMeasure_map_iff hZ.aemeasurable).2 inferInstance
  have hμi : Integrable (fun x : B => x) μ := by
    exact (integrable_map_measure aestronglyMeasurable_id hY.aemeasurable).2 hY
  have hνi : Integrable (fun x : B => x) ν := by
    exact (integrable_map_measure aestronglyMeasurable_id hZ.aemeasurable).2 hZ
  obtain ⟨L, hL, hLm⟩ := exists_dual_vector'' ℝ
    ((∫ ω, Y ω ∂P) - (∫ ω, Z ω ∂Q))
  have hLμ : Integrable (fun x : B => L x) μ := by
    refine Integrable.mono' (hμi.norm.const_mul ‖L‖)
      (L.continuous.aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), mul_comm] using
      (ContinuousLinearMap.le_opNorm L x)
  have hLν : Integrable (fun x : B => L x) ν := by
    refine Integrable.mono' (hνi.norm.const_mul ‖L‖)
      (L.continuous.aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), mul_comm] using
      (ContinuousLinearMap.le_opNorm L x)
  have hdual := HRS.ME.Bias.le_wassersteinE_one_of_dual L hL hLμ hLν
  have hLY : ∫ x, L x ∂μ = L (∫ ω, Y ω ∂P) := by
    dsimp [μ, law]
    rw [integral_map hY.aemeasurable L.continuous.aestronglyMeasurable]
    exact ContinuousLinearMap.integral_comp_comm L hY
  have hLZ : ∫ x, L x ∂ν = L (∫ ω, Z ω ∂Q) := by
    dsimp [ν, law]
    rw [integral_map hZ.aemeasurable L.continuous.aestronglyMeasurable]
    exact ContinuousLinearMap.integral_comp_comm L hZ
  rw [hLY, hLZ, ← map_sub] at hdual
  have hLm' : L ((∫ ω, Y ω ∂P) - (∫ ω, Z ω ∂Q)) =
      ‖(∫ ω, Y ω ∂P) - (∫ ω, Z ω ∂Q)‖ := by simpa using hLm
  have habs : |L ((∫ ω, Y ω ∂P) - (∫ ω, Z ω ∂Q))| =
      ‖(∫ ω, Y ω ∂P) - (∫ ω, Z ω ∂Q)‖ := by
    rw [hLm']
    exact abs_of_nonneg (norm_nonneg _)
  rw [← habs]
  exact hdual

/-- Centering the first law at its Bochner barycenter costs at most twice the
original `W₁` distance to a zero-barycenter law. -/
theorem fp81s21_wasserstein_center_bounded
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B] [CompleteSpace B]
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Q : Measure Ω'} [IsProbabilityMeasure Q]
    (Y : Ω → B) (Z : Ω' → B)
    (hY : Integrable Y P) (hZ : Integrable Z Q)
    (hZ0 : ∫ ω, Z ω ∂Q = 0) :
    wassersteinE 1
      (law P (fun ω => Y ω - ∫ ω', Y ω' ∂P)) (law Q Z) ≤
      2 * wassersteinE 1 (law P Y) (law Q Z) := by
  let m : B := ∫ ω, Y ω ∂P
  have hYmeas : AEMeasurable Y P := hY.aemeasurable
  have hYc : AEMeasurable (fun ω => Y ω - m) P := hYmeas.sub_const m
  have hμ : IsProbabilityMeasure (law P Y) :=
    (Measure.isProbabilityMeasure_map_iff hYmeas).2 inferInstance
  have hν : IsProbabilityMeasure (law Q Z) :=
    (Measure.isProbabilityMeasure_map_iff hZ.aemeasurable).2 inferInstance
  have hcenter : IsProbabilityMeasure (law P (fun ω => Y ω - m)) :=
    (Measure.isProbabilityMeasure_map_iff hYc).2 inferInstance
  have htrans : wassersteinE 1 (law P (fun ω => Y ω - m)) (law P Y) ≤
      ENNReal.ofReal ‖m‖ := by
    have h := HRS.wassersteinE_translate P 1 le_rfl Y hYmeas (-m) 0
    simpa [law, sub_eq_add_neg] using h
  have hbary := fp81s21_barycenter_wasserstein Y Z hY hZ
  have hmean : ENNReal.ofReal ‖m‖ ≤ wassersteinE 1 (law P Y) (law Q Z) := by
    simpa [m, hZ0, sub_zero] using hbary
  calc wassersteinE 1 (law P (fun ω => Y ω - m)) (law Q Z)
      ≤ wassersteinE 1 (law P (fun ω => Y ω - m)) (law P Y) +
          wassersteinE 1 (law P Y) (law Q Z) :=
        wassersteinE_triangle 1 le_rfl _ _ _
    _ ≤ ENNReal.ofReal ‖m‖ + wassersteinE 1 (law P Y) (law Q Z) :=
      add_le_add htrans le_rfl
    _ ≤ wassersteinE 1 (law P Y) (law Q Z) + wassersteinE 1 (law P Y) (law Q Z) :=
      add_le_add hmean le_rfl
    _ = 2 * wassersteinE 1 (law P Y) (law Q Z) := by rw [two_mul]

#print axioms fp81s21_barycenter_wasserstein
#print axioms fp81s21_wasserstein_center_bounded

end HRS.Fp81.S21

end
