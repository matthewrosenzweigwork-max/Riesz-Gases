import HRS.MS.S21G2_S15a
import HRS.MS.S21L_G11F1
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space

/-!
An analytic input to R26-T3.S15e: fourth moments under the reference law and
the square-integrability of the exponential tilt imply second moments under
the tilted law. This is a separate intermediate result, not the frozen S15e.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.R26T3

theorem s15e_exp_memLp_two {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {V : Ω → ℝ}
    (hV : AEMeasurable V P)
    (hE2 : Integrable (fun ω => Real.exp (-(2 * V ω))) P) :
    MemLp (fun ω => Real.exp (-V ω)) 2 P := by
  have hm : AEStronglyMeasurable (fun ω => Real.exp (-V ω)) P :=
    (Real.measurable_exp.comp_aemeasurable hV.neg).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).2
  convert hE2 using 1
  funext ω
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

theorem s15e_tilt_memLp_two {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {V Q : Ω → ℝ}
    (hV : AEMeasurable V P)
    (hE : Integrable (fun ω => Real.exp (-V ω)) P)
    (hW2 : MemLp (fun ω => Real.exp (-V ω)) 2 P)
    (hQ4 : MemLp Q 4 P) :
    MemLp Q 2 (r26t3_tilt P V) := by
  have hQsq : MemLp (fun ω => Q ω ^ 2) 2 P := by
    have hpow := hQ4.norm_rpow_div (2 : ℝ≥0∞)
    have hdiv : (4 : ℝ≥0∞) / 2 = 2 := by
      calc
        (4 : ℝ≥0∞) / 2 = 2 * (2 * 2⁻¹) := by
          rw [div_eq_mul_inv, ← mul_assoc]
          congr 1
          norm_num
        _ = 2 := by
          rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
          simp
    rw [hdiv] at hpow
    convert hpow using 1
    funext ω
    simp [Real.norm_eq_abs, sq_abs, Real.rpow_natCast]
  have hprod : Integrable (fun ω => Real.exp (-V ω) * Q ω ^ 2) P :=
    hW2.integrable_mul hQsq
  have hmeas : AEMeasurable
      (fun ω => ENNReal.ofReal (Real.exp (-V ω))) P :=
    (Real.measurable_exp.comp_aemeasurable hV.neg).ennreal_ofReal
  have hD : Integrable (fun ω => Q ω ^ 2)
      (P.withDensity (fun ω => ENNReal.ofReal (Real.exp (-V ω)))) := by
    apply (integrable_withDensity_iff_integrable_smul₀'
      hmeas (Filter.Eventually.of_forall fun ω => ENNReal.ofReal_lt_top)).2
    convert hprod using 1
    funext ω
    simp [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  have hZpos := s21g2_s15a_Z_pos P hV hE
  have hsq : Integrable (fun ω => Q ω ^ 2) (r26t3_tilt P V) := by
    unfold r26t3_tilt
    exact hD.smul_measure
      (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hZpos).ne')
  have hac : r26t3_tilt P V ≪ P := by
    intro s hs
    unfold r26t3_tilt
    simp [withDensity_absolutelyContinuous P _ hs]
  exact (memLp_two_iff_integrable_sq
    (hQ4.aestronglyMeasurable.mono_ac hac)).2 hsq

/-- The L2 conclusion under the exponential tilt, directly from a second
exponential moment and a fourth moment for the observable. -/
theorem s15e_tilt_memLp_of_exp_two {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {V Q : Ω → ℝ}
    (hV : AEMeasurable V P)
    (hE2 : Integrable (fun ω => Real.exp (-(2 * V ω))) P)
    (hQ4 : MemLp Q 4 P) :
    MemLp Q 2 (r26t3_tilt P V) := by
  have hE2' : Integrable (fun ω => Real.exp (-2 * V ω)) P := by
    convert hE2 using 1
    funext ω
    congr 1
    ring
  have hE := s21g2_s15a_int1 (P := P) hV
    (r := (2 : ℝ)) (by norm_num) hE2'
  exact s15e_tilt_memLp_two P hV hE
    (s15e_exp_memLp_two P hV hE2) hQ4

/-- The centered quadratic observable remains in L2 of the tilted probability
measure. This is the analytic integrability part of the S15e target. -/
theorem s15e_tilt_centered_memLp_two {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {V Q : Ω → ℝ}
    (hV : AEMeasurable V P)
    (hE2 : Integrable (fun ω => Real.exp (-(2 * V ω))) P)
    (hQ4 : MemLp Q 4 P) :
    let Pt := r26t3_tilt P V
    ∃ hPt : IsProbabilityMeasure Pt,
      letI := hPt
      MemLp (fun ω => Q ω - ∫ ω', Q ω' ∂Pt) 2 Pt := by
  have hE2' : Integrable (fun ω => Real.exp (-2 * V ω)) P := by
    convert hE2 using 1
    funext ω
    congr 1
    ring
  have hE := s21g2_s15a_int1 (P := P) hV (r := (2 : ℝ))
    (by norm_num) hE2'
  haveI : IsProbabilityMeasure (r26t3_tilt P V) :=
    r26t3_tilt_isProb P hV hE
  dsimp
  refine ⟨inferInstance, ?_⟩
  exact (s15e_tilt_memLp_of_exp_two P hV hE2 hQ4).sub
    (memLp_const (∫ ω', Q ω' ∂(r26t3_tilt P V)))

/-- A scalar variable in the second Gaussian chaos has a fourth moment,
using the existing exact Gaussian fourth-moment estimate. -/
theorem s15e_inQ2_memLp_four {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} {hξ : HRS.IsStdGaussianSeq P ξ}
    {Q : Ω → ℝ} (hQ : HRS.MC.E213U13.InQ2 hξ Q) :
    MemLp Q 4 P := by
  have h4 := (s21l_inQ2_four hQ).1
  apply (integrable_norm_rpow_iff hQ.1.aestronglyMeasurable
    (by norm_num) (by norm_num)).1
  convert h4 using 1
  funext ω
  rw [show ((4 : ℝ≥0∞).toReal) = ((4 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, Real.norm_eq_abs]
  calc
    |Q ω| ^ 4 = (|Q ω| ^ 2) ^ 2 := by ring
    _ = ((Q ω) ^ 2) ^ 2 := by rw [sq_abs]
    _ = (Q ω) ^ 4 := by ring

/-- A quadratic Gaussian-chaos observable is square integrable after
any exponential tilt with an integrable squared density. -/
theorem s15e_inQ2_tilt_memLp_two {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} {hξ : HRS.IsStdGaussianSeq P ξ}
    {V Q : Ω → ℝ}
    (hV : AEMeasurable V P)
    (hE2 : Integrable (fun ω => Real.exp (-(2 * V ω))) P)
    (hQ : HRS.MC.E213U13.InQ2 hξ Q) :
    MemLp Q 2 (r26t3_tilt P V) :=
  s15e_tilt_memLp_of_exp_two P hV hE2 (s15e_inQ2_memLp_four hQ)

/-- Direct centered L2 integrability of a second-chaos observable under
a square-integrable exponential density. -/
theorem s15e_inQ2_tilt_centered_memLp_two {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} {hξ : HRS.IsStdGaussianSeq P ξ}
    {V Q : Ω → ℝ}
    (hV : AEMeasurable V P)
    (hE2 : Integrable (fun ω => Real.exp (-(2 * V ω))) P)
    (hQ : HRS.MC.E213U13.InQ2 hξ Q) :
    let Pt := r26t3_tilt P V
    ∃ hPt : IsProbabilityMeasure Pt,
      letI := hPt
      MemLp (fun ω => Q ω - ∫ ω', Q ω' ∂Pt) 2 Pt :=
  s15e_tilt_centered_memLp_two P hV hE2 (s15e_inQ2_memLp_four hQ)

end HRS.MS.R26T3
