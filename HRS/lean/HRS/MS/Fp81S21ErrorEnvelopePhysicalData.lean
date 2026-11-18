import HRS.MS.Fp81S21GaussianPacket36
import HRS.MS.Fp81S21GaussianContractionPhysical

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S21E
attribute [local instance] fp81s21_initialMeasure_isProbability

local instance (p : Parameters) : CompleteSpace (projTensor (Window p) 2) :=
  HRS.Fp81.V01.fp81v01_projTensorComplete (Window p) 2

/-- The conditioning clauses for a retained Gaussian record imply the
contraction required by the physical supplied-data interface. -/
theorem fp81s21_errorEnvelope_packet36_contract
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (Q : fp81s21_Physical35 p R) (future : (H : ℝ) → ℝ →
      Measure (OscPath p.d (wholeSpaceIndex p.d) H))
    (a : ℝ) (ha : 0 ≤ a) (Φ : Window p → ℝ)
    (hΦ : Φ ∈ CbUnitBall (Window p) 5)
    (W : fp81s21_GRS Q future a ha Φ)
    (hD : fp81s21_D36 W) (hJ : fp81s21_J36 W) :
    (1 / 6 : ℝ) * (∫ ω, (s21eKappa Q.src.G0.P (initialKappa R a)
      (fp81s21_physical35_D Q.tofp81s21_Gaussian35Selection Q.OD a)
      (r26t3_Zpath Q.src.G0 a)
      (fun ω => (fp81s21_physical35_J Q.tofp81s21_Gaussian35Selection Q.OJ a ω :
        TensorDual (Window p) 2)))
      (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath Q.src.G0 a ω)) ∂Q.src.G0.P) =
    (1 / 6 : ℝ) * (∫ ω, initialKappa R a
      (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath Q.src.G0 a ω)) ∂Q.src.G0.P) +
      fp81s21_WindowRS_corr W.WG 0 (a + p.T) := by
  exact fp81s21_gaussian_contraction_of_conditioning Q a ha Φ hΦ W.WG hD hJ

#print axioms fp81s21_errorEnvelope_packet36_contract
end HRS.Fp81.S21
end
