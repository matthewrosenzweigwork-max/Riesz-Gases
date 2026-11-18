import HRS.MS.Fp81S21MovingInterpolation
import HRS.MS.Fp81S21InitialWindow
import HRS.MS.Fp81S21RSValue5

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

section
variable {Ω₁ Ω₂ E₁ J₁ E₂ J₂ : Type*}
variable [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
variable [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [CompleteSpace E₁]
variable [NormedAddCommGroup J₁] [NormedSpace ℝ J₁] [CompleteSpace J₁]
variable [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂]
variable [NormedAddCommGroup J₂] [NormedSpace ℝ J₂] [CompleteSpace J₂]
variable {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂} {H : ℝ}
variable {Ad₁ : Ω₁ → ℝ → E₁ →L[ℝ] ℝ} {Fd₁ : Ω₁ → ℝ → E₁}
variable {Aj₁ : Ω₁ → ℝ → J₁ →L[ℝ] ℝ} {Fj₁ : Ω₁ → ℝ → J₁}
variable {Ad₂ : Ω₂ → ℝ → E₂ →L[ℝ] ℝ} {Fd₂ : Ω₂ → ℝ → E₂}
variable {Aj₂ : Ω₂ → ℝ → J₂ →L[ℝ] ℝ} {Fj₂ : Ω₂ → ℝ → J₂}

/-- Split the two supplied correction records at the same cutoff. -/
theorem fp81s21_error_corr_split
    (WN : fp81s21_WindowRS μ₁ H Ad₁ Fd₁ Aj₁ Fj₁)
    (WG : fp81s21_WindowRS μ₂ H Ad₂ Fd₂ Aj₂ Fj₂)
    (a L : ℝ) (ha : 0 ≤ a) (hL : 0 ≤ L) (haH : a ≤ H) :
    |fp81s21_WindowRS_corr WN 0 H - fp81s21_WindowRS_corr WG 0 H| ≤
      |fp81s21_WindowRS_corr WN 0 (max (a - L) 0)| +
      |fp81s21_WindowRS_corr WG 0 (max (a - L) 0)| +
      |fp81s21_WindowRS_corr WN (max (a - L) 0) H -
        fp81s21_WindowRS_corr WG (max (a - L) 0) H| := by
  have hb0 : 0 ≤ max (a - L) 0 := le_max_right _ _
  have hbH : max (a - L) 0 ≤ H := (max_le (by linarith) ha).trans haH
  rw [fp81s21_WindowRS_corr_add WN le_rfl hb0 hbH le_rfl,
    fp81s21_WindowRS_corr_add WG le_rfl hb0 hbH le_rfl]
  calc
    |(fp81s21_WindowRS_corr WN 0 (max (a - L) 0) +
        fp81s21_WindowRS_corr WN (max (a - L) 0) H) -
       (fp81s21_WindowRS_corr WG 0 (max (a - L) 0) +
        fp81s21_WindowRS_corr WG (max (a - L) 0) H)| =
      |(fp81s21_WindowRS_corr WN 0 (max (a - L) 0) -
        fp81s21_WindowRS_corr WG 0 (max (a - L) 0)) +
        (fp81s21_WindowRS_corr WN (max (a - L) 0) H -
        fp81s21_WindowRS_corr WG (max (a - L) 0) H)| := by congr 1 <;> ring
    _ ≤ |fp81s21_WindowRS_corr WN 0 (max (a - L) 0) -
          fp81s21_WindowRS_corr WG 0 (max (a - L) 0)| +
        |fp81s21_WindowRS_corr WN (max (a - L) 0) H -
          fp81s21_WindowRS_corr WG (max (a - L) 0) H| := abs_add_le _ _
    _ ≤ _ := by
      have h := abs_sub (fp81s21_WindowRS_corr WN 0 (max (a - L) 0))
        (fp81s21_WindowRS_corr WG 0 (max (a - L) 0))
      linarith

/-- The packet-20 interpolation and supplied Gaussian contraction identify the error. -/
theorem fp81s21_error_physical
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d) H))
    (N : ℕ) (A : Particle R N) (G : GaussianRealization R)
    (a : ℝ) (ha : 0 ≤ a) (Φ : Window p → ℝ)
    (κ : ℝ → projTensor (Window p) 3)
    (WN : fp81s21_WindowRS μ₁ (a + p.T) Ad₁ Fd₁ Aj₁ Fj₁)
    (WG : fp81s21_WindowRS μ₂ (a + p.T) Ad₂ Fd₂ Aj₂ Fj₂)
    (hI : Real.sqrt N *
      ((∫ ω, Φ (r26t3_zetapath A a ω) ∂A.P) -
        ∫ X, initialHeat future a ha Φ 0 (initialWindow R N a X) ∂(r26t3_Q R N)) =
          fp81s21_WindowRS_corr WN 0 (a + p.T))
    (hC : (1 / 6 : ℝ) * ∫ ω, (κ a : TensorDual (Window p) 3)
      (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath G a ω)) ∂G.P =
      (1 / 6 : ℝ) * ∫ ω, initialKappa R a
        (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath G a ω)) ∂G.P +
      fp81s21_WindowRS_corr WG 0 (a + p.T)) :
    r26t3_error κ A G a Φ =
      |initialRemainder R future N G a ha Φ +
        fp81s21_WindowRS_corr WN 0 (a + p.T) -
        fp81s21_WindowRS_corr WG 0 (a + p.T)| := by
  unfold r26t3_error initialRemainder
  congr 1
  linarith [hI, hC]

/-- Combine the residual identity with the same-record remote/recent split. -/
theorem fp81s21_error_physical_bound
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d) H))
    (N : ℕ) (A : Particle R N) (G : GaussianRealization R)
    (a : ℝ) (ha : 0 ≤ a) (Φ : Window p → ℝ)
    (κ : ℝ → projTensor (Window p) 3)
    (WN : fp81s21_WindowRS μ₁ (a + p.T) Ad₁ Fd₁ Aj₁ Fj₁)
    (WG : fp81s21_WindowRS μ₂ (a + p.T) Ad₂ Fd₂ Aj₂ Fj₂)
    (hI : Real.sqrt N *
      ((∫ ω, Φ (r26t3_zetapath A a ω) ∂A.P) -
        ∫ X, initialHeat future a ha Φ 0 (initialWindow R N a X) ∂(r26t3_Q R N)) =
          fp81s21_WindowRS_corr WN 0 (a + p.T))
    (hC : (1 / 6 : ℝ) * ∫ ω, (κ a : TensorDual (Window p) 3)
      (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath G a ω)) ∂G.P =
      (1 / 6 : ℝ) * ∫ ω, initialKappa R a
        (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath G a ω)) ∂G.P +
      fp81s21_WindowRS_corr WG 0 (a + p.T))
    (L : ℝ) (hL : 0 ≤ L) :
    r26t3_error κ A G a Φ ≤ |initialRemainder R future N G a ha Φ| +
      (|fp81s21_WindowRS_corr WN 0 (max (a - L) 0)| +
       |fp81s21_WindowRS_corr WG 0 (max (a - L) 0)| +
       |fp81s21_WindowRS_corr WN (max (a - L) 0) (a + p.T) -
        fp81s21_WindowRS_corr WG (max (a - L) 0) (a + p.T)|) := by
  rw [fp81s21_error_physical p R future N A G a ha Φ κ WN WG hI hC]
  have hs := fp81s21_error_corr_split WN WG a L ha hL (by linarith [p.hT])
  calc
    |initialRemainder R future N G a ha Φ + fp81s21_WindowRS_corr WN 0 (a + p.T) -
       fp81s21_WindowRS_corr WG 0 (a + p.T)| =
      |initialRemainder R future N G a ha Φ +
        (fp81s21_WindowRS_corr WN 0 (a + p.T) -
         fp81s21_WindowRS_corr WG 0 (a + p.T))| := by congr 1 <;> ring
    _ ≤ _ := by
      have ht := abs_add_le (initialRemainder R future N G a ha Φ)
        (fp81s21_WindowRS_corr WN 0 (a + p.T) -
         fp81s21_WindowRS_corr WG 0 (a + p.T))
      linarith

end
#print axioms fp81s21_error_corr_split
#print axioms fp81s21_error_physical
#print axioms fp81s21_error_physical_bound
end HRS.Fp81.S21
end
