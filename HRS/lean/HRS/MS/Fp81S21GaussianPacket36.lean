import HRS.MS.Fp81S21GaussianConditioningPhysicalD3
import HRS.MS.Fp81S21GaussianConditioningPhysicalJ3
import HRS.MS.Fp81S21GaussianWindowRS2

/-! Assemble the three uniform-radius producers using the same retained record. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

local instance fp81s21_packet36_complete (p : Parameters) :
    CompleteSpace (projTensor (Window p) 2) :=
  HRS.Fp81.V01.fp81v01_projTensorComplete (Window p) 2

/-- One radius and one GRS record carry both physical conditioning identities. -/
theorem fp81s21_gaussian_packet36 (p : Parameters) :
    fp81s21_Rad p (fun _ R => ∀ Q : fp81s21_Physical35 p R,
      ∀ future, fp81s21_moving_heat_full_clause p R future →
      ∀ (a : ℝ) (ha : 0 ≤ a) (Φ : Window p → ℝ), Φ ∈ CbUnitBall (Window p) 5 →
      ∃ C : fp81s21_GRS Q future a ha Φ, fp81s21_D36 C ∧ fp81s21_J36 C) := by
  obtain ⟨rR, hrR, hRhalf, hR⟩ := fp81s21_gaussian_window_rs p
  obtain ⟨rD, hrD, hDhalf, hD⟩ := fp81s21_gaussian_conditioning_physical_D p
  obtain ⟨rJ, hrJ, hJhalf, hJ⟩ := fp81s21_gaussian_conditioning_physical_J p
  refine ⟨min rR (min rD rJ), lt_min hrR (lt_min hrD hrJ),
    le_trans (min_le_left _ _) hRhalf, ?_⟩
  intro δ hδ hδle R Q future hf a ha Φ hΦ
  have hδR : δ ≤ rR := le_trans hδle (min_le_left _ _)
  have hδD : δ ≤ rD := le_trans hδle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδJ : δ ≤ rJ := le_trans hδle (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨C⟩ := hR δ hδ hδR R Q future hf a ha Φ hΦ
  exact ⟨C, hD δ hδ hδD R Q future hf a ha Φ hΦ C,
    hJ δ hδ hδJ R Q future hf a ha Φ hΦ C⟩

/-- The two clauses unfold to the premises consumed by the contraction theorem,
with its window RS argument instantiated by the same record's `WG`. -/
theorem fp81s21_gaussian_packet36_WG (p : Parameters) :
    fp81s21_Rad p (fun _ R => ∀ Q : fp81s21_Physical35 p R,
      ∀ future, fp81s21_moving_heat_full_clause p R future →
      ∀ (a : ℝ) (ha : 0 ≤ a) (Φ : Window p → ℝ), Φ ∈ CbUnitBall (Window p) 5 →
      ∃ C : fp81s21_GRS Q future a ha Φ,
        (Integrable (C.WG.drift.value 0 (a + p.T)) Q.src.G0.P ∧
         Integrable (fun ω => fderiv ℝ Φ (r26t3_Zpath Q.src.G0 a ω)
           (fp81s21_physical35_D Q.tofp81s21_Gaussian35Selection Q.OD a ω)) Q.src.G0.P ∧
         (-(∫ ω, C.WG.drift.value 0 (a + p.T) ω ∂Q.src.G0.P) =
          -(∫ ω, fderiv ℝ Φ (r26t3_Zpath Q.src.G0 a ω)
            (fp81s21_physical35_D Q.tofp81s21_Gaussian35Selection Q.OD a ω) ∂Q.src.G0.P))) ∧
        (Integrable (C.WG.covariance.value 0 (a + p.T)) Q.src.G0.P ∧
         Integrable (fun ω => (fp81s21_physical35_J Q.tofp81s21_Gaussian35Selection Q.OJ a ω :
           TensorDual (Window p) 2) (iteratedFDeriv ℝ 2 Φ (r26t3_Zpath Q.src.G0 a ω))) Q.src.G0.P ∧
         ((1 / 2 : ℝ) * (∫ ω, C.WG.covariance.value 0 (a + p.T) ω ∂Q.src.G0.P) =
          (1 / 2 : ℝ) * (∫ ω, (fp81s21_physical35_J Q.tofp81s21_Gaussian35Selection Q.OJ a ω :
            TensorDual (Window p) 2) (iteratedFDeriv ℝ 2 Φ (r26t3_Zpath Q.src.G0 a ω)) ∂Q.src.G0.P)))) := by
  exact fp81s21_gaussian_packet36 p

#print axioms fp81s21_gaussian_packet36
#print axioms fp81s21_gaussian_packet36_WG
end HRS.Fp81.S21
end
