import HRS.MS.Fp81S21GaussianWickPackage
import HRS.MS.Fp81S21RSValue5

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S21E
variable {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
attribute [local instance] fp81s21_initialMeasure_isProbability

/-- The two supplied conditioning identities turn the Gaussian pairing formula
into the signed physical window correction. -/
theorem fp81s21_gaussian_contraction_of_conditioning
    (Q : fp81s21_Physical35 p R) (a : ℝ) (ha : 0 ≤ a)
    (Φ : Window p → ℝ) (hΦ : Φ ∈ CbUnitBall (Window p) 5)
    {ED EJ : Type*} [NormedAddCommGroup ED] [NormedSpace ℝ ED] [CompleteSpace ED]
    [NormedAddCommGroup EJ] [NormedSpace ℝ EJ] [CompleteSpace EJ]
    {Ad : Q.src.G0.Ω → ℝ → ED →L[ℝ] ℝ} {Fd : Q.src.G0.Ω → ℝ → ED}
    {Aj : Q.src.G0.Ω → ℝ → EJ →L[ℝ] ℝ} {Fj : Q.src.G0.Ω → ℝ → EJ}
    (WG : fp81s21_WindowRS Q.src.G0.P (a + p.T) Ad Fd Aj Fj)
    (hD36 : Integrable (WG.drift.value 0 (a + p.T)) Q.src.G0.P ∧
      Integrable (fun ω => fderiv ℝ Φ (r26t3_Zpath Q.src.G0 a ω)
        (fp81s21_physical35_D Q.tofp81s21_Gaussian35Selection Q.OD a ω)) Q.src.G0.P ∧
      (-(∫ ω, WG.drift.value 0 (a + p.T) ω ∂Q.src.G0.P) =
       -(∫ ω, fderiv ℝ Φ (r26t3_Zpath Q.src.G0 a ω)
        (fp81s21_physical35_D Q.tofp81s21_Gaussian35Selection Q.OD a ω) ∂Q.src.G0.P)))
    (hJ36 : Integrable (WG.covariance.value 0 (a + p.T)) Q.src.G0.P ∧
      Integrable (fun ω => (fp81s21_physical35_J Q.tofp81s21_Gaussian35Selection Q.OJ a ω :
        TensorDual (Window p) 2) (iteratedFDeriv ℝ 2 Φ (r26t3_Zpath Q.src.G0 a ω))) Q.src.G0.P ∧
      ((1 / 2 : ℝ) * (∫ ω, WG.covariance.value 0 (a + p.T) ω ∂Q.src.G0.P) =
       (1 / 2 : ℝ) * (∫ ω, (fp81s21_physical35_J Q.tofp81s21_Gaussian35Selection Q.OJ a ω :
        TensorDual (Window p) 2) (iteratedFDeriv ℝ 2 Φ (r26t3_Zpath Q.src.G0 a ω)) ∂Q.src.G0.P))) :
    (1 / 6 : ℝ) * (∫ ω, (s21eKappa Q.src.G0.P (initialKappa R a)
        (fp81s21_physical35_D Q.tofp81s21_Gaussian35Selection Q.OD a)
        (r26t3_Zpath Q.src.G0 a)
        (fun ω => (fp81s21_physical35_J Q.tofp81s21_Gaussian35Selection Q.OJ a ω :
          TensorDual (Window p) 2))) (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath Q.src.G0 a ω)) ∂Q.src.G0.P) =
      (1 / 6 : ℝ) * (∫ ω, initialKappa R a
        (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath Q.src.G0 a ω)) ∂Q.src.G0.P) +
        fp81s21_WindowRS_corr WG 0 (a + p.T) := by
  have hΦ3 : MemCb 3 Φ := ⟨hΦ.1.of_le (by norm_num),
    fun j hj => hΦ.2.1 j (hj.trans (by norm_num))⟩
  have hc := Q.chaos a ha
  have hm := Q.moments a ha
  have hi := Q.integrabilities a ha
  have hpair := s21e_pairing_identity Q.src.G0.P
    (fp81s21_gaussian_source_measurableXi Q.src) Q.source.1
    (r26t3_Zpath Q.src.G0 a)
    (fp81s21_physical35_D Q.tofp81s21_Gaussian35Selection Q.OD a)
    (fp81s21_physical35_J Q.tofp81s21_Gaussian35Selection Q.OJ a)
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 Φ hΦ3
    hm.2.2.2.2.1.aestronglyMeasurable hm.1.aestronglyMeasurable
    (continuous_subtype_val.comp_aestronglyMeasurable hm.2.2.1.aestronglyMeasurable)
    hi.1 hi.2.2.1 hi.2.1 hi.2.2.2 (initialKappa R a)
  rw [fp81s21_WindowRS_corr, hD36.2.2, hJ36.2.2]
  linarith

#print axioms fp81s21_gaussian_contraction_of_conditioning
end HRS.Fp81.S21
end
