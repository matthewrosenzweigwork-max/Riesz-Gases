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

/-- Rewrite a supplied Gaussian contraction through a compatible O1 tensor. -/
theorem fp81s21_gaussian_contraction_O1
    (Q : fp81s21_Physical35 p R)
    (O1 : fp81s21_O1_gaussian_wick p.d p.s p.a p.β p.γ p.T R.ρ)
    (a : ℝ) (ha : 0 ≤ a) (Φ : Window p → ℝ)
    {ED EJ : Type*} [NormedAddCommGroup ED] [NormedSpace ℝ ED] [CompleteSpace ED]
    [NormedAddCommGroup EJ] [NormedSpace ℝ EJ] [CompleteSpace EJ]
    {Ad : Q.src.G0.Ω → ℝ → ED →L[ℝ] ℝ} {Fd : Q.src.G0.Ω → ℝ → ED}
    {Aj : Q.src.G0.Ω → ℝ → EJ →L[ℝ] ℝ} {Fj : Q.src.G0.Ω → ℝ → EJ}
    (WG : fp81s21_WindowRS Q.src.G0.P (a + p.T) Ad Fd Aj Fj)
    (hκ : (fp81s21_O1_kappa O1 a : TensorDual (Window p) 3) =
      s21eKappa Q.src.G0.P (initialKappa R a)
        (fp81s21_physical35_D Q.tofp81s21_Gaussian35Selection Q.OD a)
        (r26t3_Zpath Q.src.G0 a)
        (fun ω => (fp81s21_physical35_J Q.tofp81s21_Gaussian35Selection Q.OJ a ω :
          TensorDual (Window p) 2)))
    (hC : (1 / 6 : ℝ) * (∫ ω, (s21eKappa Q.src.G0.P (initialKappa R a)
        (fp81s21_physical35_D Q.tofp81s21_Gaussian35Selection Q.OD a)
        (r26t3_Zpath Q.src.G0 a)
        (fun ω => (fp81s21_physical35_J Q.tofp81s21_Gaussian35Selection Q.OJ a ω :
          TensorDual (Window p) 2))) (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath Q.src.G0 a ω)) ∂Q.src.G0.P) =
      (1 / 6 : ℝ) * (∫ ω, initialKappa R a
        (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath Q.src.G0 a ω)) ∂Q.src.G0.P) +
        fp81s21_WindowRS_corr WG 0 (a + p.T)) :
    (1 / 6 : ℝ) * (∫ ω, (fp81s21_O1_kappa O1 a : TensorDual (Window p) 3)
      (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath Q.src.G0 a ω)) ∂Q.src.G0.P) =
    (1 / 6 : ℝ) * (∫ ω, initialKappa R a
      (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath Q.src.G0 a ω)) ∂Q.src.G0.P) +
      fp81s21_WindowRS_corr WG 0 (a + p.T) := by
  rw [hκ]
  exact hC


/-- Specialization to the O1 constructed from the supplied physical data. -/
theorem fp81s21_gaussian_contraction_O1_of_physical35
    (Q : fp81s21_Physical35 p R)
    (Kresponse : ℝ) (hresp : fp81s21_Response9 R Kresponse)
    (hwick : fp81s21_WickAll Q)
    (hbound : ∀ a : ℝ, 0 ≤ a →
      ‖initialKappa R a‖ + 3 * fp81s21_ID Q a + 3 * fp81s21_IJ Q a ≤
        Kresponse ^ 3 + 3 * (Q.MD ^ (1 / 3 : ℝ) * Q.MZ ^ (1 / 2 : ℝ) +
          Q.MJ ^ (1 / 2 : ℝ) * Q.MZ ^ (1 / 4 : ℝ)))
    (a : ℝ) (ha : 0 ≤ a) (Φ : Window p → ℝ)
    {ED EJ : Type*} [NormedAddCommGroup ED] [NormedSpace ℝ ED] [CompleteSpace ED]
    [NormedAddCommGroup EJ] [NormedSpace ℝ EJ] [CompleteSpace EJ]
    {Ad : Q.src.G0.Ω → ℝ → ED →L[ℝ] ℝ} {Fd : Q.src.G0.Ω → ℝ → ED}
    {Aj : Q.src.G0.Ω → ℝ → EJ →L[ℝ] ℝ} {Fj : Q.src.G0.Ω → ℝ → EJ}
    (WG : fp81s21_WindowRS Q.src.G0.P (a + p.T) Ad Fd Aj Fj)
    (hC : (1 / 6 : ℝ) * (∫ ω, (s21eKappa Q.src.G0.P (initialKappa R a)
        (fp81s21_physical35_D Q.tofp81s21_Gaussian35Selection Q.OD a)
        (r26t3_Zpath Q.src.G0 a)
        (fun ω => (fp81s21_physical35_J Q.tofp81s21_Gaussian35Selection Q.OJ a ω :
          TensorDual (Window p) 2))) (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath Q.src.G0 a ω)) ∂Q.src.G0.P) =
      (1 / 6 : ℝ) * (∫ ω, initialKappa R a
        (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath Q.src.G0 a ω)) ∂Q.src.G0.P) +
        fp81s21_WindowRS_corr WG 0 (a + p.T)) :
    (1 / 6 : ℝ) * (∫ ω, (fp81s21_O1_kappa (fp81s21_gaussianO1_of_physical35 Q Kresponse hresp hwick hbound) a : TensorDual (Window p) 3)
      (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath Q.src.G0 a ω)) ∂Q.src.G0.P) =
    (1 / 6 : ℝ) * (∫ ω, initialKappa R a
      (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath Q.src.G0 a ω)) ∂Q.src.G0.P) +
      fp81s21_WindowRS_corr WG 0 (a + p.T) := by
  exact fp81s21_gaussian_contraction_O1 Q _ a ha Φ WG
    (fp81s21_gaussianO1_kappa_eq Q Kresponse hresp hwick hbound a ha) hC

#print axioms fp81s21_gaussian_contraction_O1
#print axioms fp81s21_gaussian_contraction_O1_of_physical35
end HRS.Fp81.S21
end
