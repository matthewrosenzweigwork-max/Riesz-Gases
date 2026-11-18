import HRS.MS.Fp81S21CovRS2
import HRS.MS.R2InterpAux24

/-! Uniform norm and variation bounds for the covariance integrand. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R2Interp

/-- Restricting a bilinear form to projective tensors has operator norm at most
the norm of the form. -/
theorem fp81s21_covariance_pairingCLM_norm_le
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (Q : B [×2]→L[ℝ] ℝ) :
    ‖fp81s21_covariance_pairingCLM Q‖ ≤ ‖Q‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Q) fun x => ?_
  change ‖(x : TensorDual B 2) Q‖ ≤ ‖Q‖ * ‖x‖
  calc
    ‖(x : TensorDual B 2) Q‖ ≤ ‖(x : TensorDual B 2)‖ * ‖Q‖ :=
      (x : TensorDual B 2).le_opNorm Q
    _ = ‖Q‖ * ‖x‖ := by
      rw [mul_comm]
      rfl

/-- The projected heat Hessian, paired on projective tensors, is bounded by
the original test norm uniformly in the heat time and evaluation point. -/
theorem fp81s21_projected_heat_covariance_pairing_norm_le
    {d : ℕ} {m H : ℝ}
    (γ : ℝ → Measure (OscPath d m H))
    (hγ : ∀ τ, IsProbabilityMeasure (γ τ))
    (P : OscPath d m H →L[ℝ] OscPath d m H) (hP : ‖P‖ ≤ 1)
    (Ψ : OscPath d m H → ℝ) (hΨ : MemCb 5 Ψ)
    (τ : ℝ) (y : OscPath d m H) :
    ‖fp81s21_covariance_pairingCLM
      (iteratedFDeriv ℝ 2
        (r2HeatFn γ (fun w => Ψ (P w)) τ) y)‖ ≤ cbNorm 5 Ψ := by
  exact (fp81s21_covariance_pairingCLM_norm_le _).trans
    (s102_deriv_norm_le γ hγ P hP hΨ τ y)

/-- On every admissible subinterval the exact covariance RS supremum-times-
variation majorant is bounded by the full-horizon variation times the test
norm, with no dependence on the projection level. -/
theorem fp81s21_projected_heat_covariance_variation_majorant_le
    {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {m H : ℝ}
    (γ : ℝ → Measure (OscPath d m H))
    (hγ : ∀ τ, IsProbabilityMeasure (γ τ))
    (P : OscPath d m H →L[ℝ] OscPath d m H) (hP : ‖P‖ ≤ 1)
    (Ψ : OscPath d m H → ℝ) (hΨ : MemCb 5 Ψ)
    (Y : Ω → ℝ → OscPath d m H)
    (F : Ω → ℝ → projTensor (OscPath d m H) 2)
    (ω : Ω) (V : ℝ)
    (hBV : BoundedVariationOn (F ω) (Icc 0 H))
    (hV : (eVariationOn (F ω) (Icc 0 H)).toReal ≤ V)
    {q r : ℝ} (hq : 0 ≤ q) (hqr : q ≤ r) (hr : r ≤ H) :
    fp81s21_rs_bv_variation_majorant
      (fun ω τ => fp81s21_covariance_pairingCLM
        (iteratedFDeriv ℝ 2
          (r2HeatFn γ (fun w => Ψ (P w)) τ) (Y ω τ))) F q r ω ≤
      cbNorm 5 Ψ * V := by
  letI : Nonempty (Icc q r) := ⟨⟨q, le_rfl, hqr⟩⟩
  have hs : Icc q r ⊆ Icc (0 : ℝ) H := Icc_subset_Icc hq hr
  have hv : (eVariationOn (F ω) (Icc q r)).toReal ≤ V :=
    (ENNReal.toReal_mono hBV (eVariationOn.mono (F ω) hs)).trans hV
  have hsup : (⨆ τ : Icc q r,
      ‖fp81s21_covariance_pairingCLM
        (iteratedFDeriv ℝ 2
          (r2HeatFn γ (fun w => Ψ (P w)) τ) (Y ω τ))‖) ≤ cbNorm 5 Ψ := by
    apply ciSup_le
    intro τ
    exact fp81s21_projected_heat_covariance_pairing_norm_le γ hγ P hP Ψ hΨ τ (Y ω τ)
  unfold fp81s21_rs_bv_variation_majorant
  calc
    _ ≤ cbNorm 5 Ψ * (eVariationOn (F ω) (Icc q r)).toReal :=
      mul_le_mul_of_nonneg_right hsup ENNReal.toReal_nonneg
    _ ≤ cbNorm 5 Ψ * V :=
      mul_le_mul_of_nonneg_left hv
        (HRS.MC.Sec7.S7PIL.S7PIL_cbNorm_nonneg hΨ 0)

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_covariance_pairingCLM_norm_le
#print axioms HRS.Fp81.S21.fp81s21_projected_heat_covariance_pairing_norm_le
#print axioms HRS.Fp81.S21.fp81s21_projected_heat_covariance_variation_majorant_le
end
