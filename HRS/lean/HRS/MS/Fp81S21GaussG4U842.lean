import HRS.MS.Fp81S21GaussG4U812
import HRS.MS.Fp81S21GaussG4U83
import HRS.MS.Fp81S21GaussG4U832
import HRS.MS.Fp81S21GaussG4U84
import HRS.MS.Fp81S21GaussG4U72

/-! The centered initial Gaussian increment is controlled by its reference variance. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S111X2

theorem fp81s21_g4_initial_increment_le_centered
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    {Mg : ℝ}
    {K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0)}
    (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg)
    {f : Euc p.d → ℝ}
    (hf : IsOscTest (wholeSpaceIndex p.d : ℝ) f)
    {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) :
    ‖fp81s21_initialGaussianFeature p R hK w f -
      fp81s21_initialGaussianFeature p R hK v f‖^2 ≤
        p.C₁ * fp81s21_g4_initialValue R f v w := by
  let ν : Measure (Euc p.d) := HRS.Whole.withDensityReal R.ρβ
  let D : Euc p.d → ℝ := fun x => r26t3_U R 0 w f x - r26t3_U R 0 v f x
  letI : IsProbabilityMeasure ν :=
    HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  have hw : 0 ≤ w := hv.trans hvw
  have huW := fp81s21_U_osc_test_classical p R hf hw
  have huV := fp81s21_U_osc_test_classical p R hf hv
  obtain ⟨B0W, _, _, hB0W, _, _, hBW⟩ := HRS.MS.S111X1.classical_bounds huW
  obtain ⟨B0V, _, _, hB0V, _, _, hBV⟩ := HRS.MS.S111X1.classical_bounds huV
  have hWν : MemLp (r26t3_U R 0 w f) 2 ν := by
    exact (MemLp.of_bound
      (huW.c2 0 ⟨le_rfl, hw⟩).continuous.aestronglyMeasurable B0W
      (Eventually.of_forall fun x => (hBW 0 ⟨le_rfl, hw⟩ x).1)).mono_exponent le_top
  have hVν : MemLp (r26t3_U R 0 v f) 2 ν := by
    exact (MemLp.of_bound
      (huV.c2 0 ⟨le_rfl, hv⟩).continuous.aestronglyMeasurable B0V
      (Eventually.of_forall fun x => (hBV 0 ⟨le_rfl, hv⟩ x).1)).mono_exponent le_top
  obtain ⟨hC₁, hcomparison⟩ :=
    fp81s21_g4_density_comparison p R hδ hδhalf
  have hμν : r26t3_mu R 0 ≤ ENNReal.ofReal p.C₁ • ν := by
    simpa [fp81s21_g4_mu, ν] using (hcomparison 0 le_rfl).2
  have hWμ : MemLp (propagatorW (r26t3_coeff R) 0 w f) 2 (r26t3_mu R 0) := by
    simpa [r26t3_U] using
      (hWν.of_measure_le_smul ENNReal.ofReal_ne_top hμν)
  have hVμ : MemLp (propagatorW (r26t3_coeff R) 0 v f) 2 (r26t3_mu R 0) := by
    simpa [r26t3_U] using
      (hVν.of_measure_le_smul ENNReal.ofReal_ne_top hμν)
  have hDν : MemLp D 2 ν := by
    convert hWν.sub hVν using 1
  have hDμ : MemLp D 2 (r26t3_mu R 0) := by
    convert hWμ.sub hVμ using 1
    funext x
    rfl
  have hresponse := fp81s21_g4_initial_increment_centered_response_bound
    p R hK hWμ hVμ
  have hresponse' :
      ‖fp81s21_initialGaussianFeature p R hK w f -
        fp81s21_initialGaussianFeature p R hK v f‖ ^ 2 ≤
        s111x2_centeredSquare (r26t3_mu R 0) D := by
    convert hresponse using 1
    have hDfun :
        (fun x => propagatorW (r26t3_coeff R) 0 w f x -
          propagatorW (r26t3_coeff R) 0 v f x) = D := by
      funext x
      simp [D, r26t3_U]
    simpa only [hDfun]
  have hvariance := fp81s21_g4_centered_variance_domination
    (K := p.C₁) hC₁.le hμν hDμ hDν
  have hvalue : s111x2_centeredSquare ν D =
      fp81s21_g4_initialValue R f v w := by
    simp [s111x2_centeredSquare, fp81s21_g4_initialValue, D, ν]
  calc
    _ ≤ s111x2_centeredSquare (r26t3_mu R 0) D := hresponse'
    _ ≤ p.C₁ * s111x2_centeredSquare ν D := hvariance
    _ = p.C₁ * fp81s21_g4_initialValue R f v w := by rw [hvalue]

#print axioms fp81s21_g4_initial_increment_le_centered

end HRS.Fp81.S21
