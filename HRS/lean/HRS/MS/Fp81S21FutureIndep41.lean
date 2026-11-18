import HRS.MS.Fp81S21FutureIndep40
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R2Interp

/-- Independent future integration with an arbitrary integrable past increment
and a bounded continuous function of both the prediction and the future. -/
theorem fp81s21_independent_past_future_integral
    {d : ℕ} {m H : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Ω → ℝ) (hD : Integrable D P)
    (Y X : Ω → OscPath d m H) (hY : Measurable Y) (hX : Measurable X)
    (hind : IndepFun (fun ω => (D ω, Y ω)) X P)
    (γ : Measure (OscPath d m H)) [IsProbabilityMeasure γ] (hlaw : P.map X = γ)
    (f : OscPath d m H × OscPath d m H → ℝ) (hf : Continuous f)
    (C : ℝ) (hC : ∀ yz, ‖f yz‖ ≤ C) :
    Integrable (fun ω => D ω * f (Y ω, X ω)) P ∧
    (∫ ω, D ω * f (Y ω, X ω) ∂P) =
      ∫ ω, D ω * (∫ z, f (Y ω, z) ∂γ) ∂P := by
  let U := fun ω => (D ω, Y ω)
  let μ := P.map U
  have hU : AEMeasurable U P := hD.aestronglyMeasurable.aemeasurable.prodMk hY.aemeasurable
  have hfst : Integrable (fun a : ℝ × OscPath d m H => a.1) μ := by
    apply (integrable_map_measure continuous_fst.aestronglyMeasurable hU).2
    simpa [U, Function.comp_def] using hD
  let F : (ℝ × OscPath d m H) × OscPath d m H → ℝ :=
    fun a => a.1.1 * f (a.1.2, a.2)
  have hFm : Continuous F := by dsimp [F]; fun_prop
  have hFi : Integrable F (μ.prod γ) := by
    have hg := (hfst.comp_fst γ).bdd_mul (hf.comp (by fun_prop :
      Continuous (fun a : (ℝ × OscPath d m H) × OscPath d m H => (a.1.2, a.2)))).aestronglyMeasurable
      (Eventually.of_forall fun a => hC (a.1.2, a.2))
    simpa only [F, Function.comp_def, mul_comm] using hg
  have hpair : P.map (fun ω => (U ω, X ω)) = μ.prod γ := by
    simpa [μ, hlaw] using hind.map_prod_eq_prod_map_map hU hX.aemeasurable
  have hi : Integrable (fun ω => D ω * f (Y ω, X ω)) P := by
    rw [← hpair] at hFi
    have := hFi.comp_aemeasurable (hU.prodMk hX.aemeasurable)
    rw [hpair] at hFi
    simpa [F, U, Function.comp_def] using this
  refine ⟨hi, ?_⟩
  calc
    (∫ ω, D ω * f (Y ω, X ω) ∂P) = ∫ a, F a ∂(μ.prod γ) := by
      rw [← hpair, integral_map (hU.prodMk hX.aemeasurable) hFm.aestronglyMeasurable]
    _ = ∫ a, ∫ z, F (a, z) ∂γ ∂μ := integral_prod F hFi
    _ = ∫ a, a.1 * (∫ z, f (a.2, z) ∂γ) ∂μ := by
      congr 1
      funext a
      simp only [F, integral_const_mul]
    _ = ∫ ω, D ω * (∫ z, f (Y ω, z) ∂γ) ∂P := by
      have hm : AEStronglyMeasurable (fun a : ℝ × OscPath d m H =>
          a.1 * ∫ z, f (a.2, z) ∂γ) μ := by
        apply AEStronglyMeasurable.mul continuous_fst.aestronglyMeasurable
        exact ((hf.stronglyMeasurable.integral_prod_right').comp_measurable measurable_snd).aestronglyMeasurable
      exact integral_map hU hm

#print axioms fp81s21_independent_past_future_integral
end HRS.Fp81.S21
end
