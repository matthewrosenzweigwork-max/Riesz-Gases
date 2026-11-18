import HRS.MS.Fp81S21GaussG4U1
import HRS.MS.WhoAux5

/-! A time-uniform weighted convolution estimate with an L² input cost. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.Who HRS.MS.Ul

/-- The density factor makes the convolution bounded on the weighted L²
space. The bounded-jet assumption ensures classical convolution identities;
the numerical bound depends only on the weighted L² cost. -/
theorem fp81s21_g4_density_convolution_cost (p : Parameters) {δ : ℝ}
    (R : Trajectory p δ) (k : Fin p.d) {P : ℝ}
    (hP : 0 ≤ P) (hPd : (p.d : ℝ) / 2 < P)
    (n : ℕ) (hnP : (p.d : ℝ) / 2 < (n : ℝ) - P)
    (hnd : (p.d : ℝ) < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℝ, 0 ≤ q →
      ∀ φ : Euc p.d → ℝ, CbCls 1 φ →
        wSq P (fun x => ‖(convGradConvW (rieszKernelGrad p.d p.s)
          (fun y => R.ρ q y * φ y) x) k‖) ≤
            ENNReal.ofReal C * Nsq 0 P φ := by
  have hd : 1 ≤ p.d := le_trans (by decide) p.hd
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hk := ult_ker_kap p.hs0 hsd k
  obtain ⟨A, hA, hρ⟩ := fp81s21_g4_density_decay p R n
  obtain ⟨C, hC, hcost⟩ := who_Kprod hd hP hPd hk
    (fp81s21_g4_kernel_exponent p) 0 hnP hnd hA
  refine ⟨C, hC, ?_⟩
  intro q hq φ hφ
  obtain ⟨hφc, B, hB⟩ := hφ
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by omega) 0)
  have hdec : U2Dec 1 (n : ℝ) (A * B * 2 ^ 1)
      (fun y => R.ρ q y * φ y) := who_u2dec_mul (hρ q hq) hφc hB
  have heq : (fun x => (convGradConvW (rieszKernelGrad p.d p.s)
      (fun y => R.ρ q y * φ y) x) k) =
      ultK (u2_kap p.d p.s k) (fun y => R.ρ q y * φ y) := by
    funext x
    exact (ult_conv_comp hd p.hs0 hsd hnd (by positivity) hdec x).2 k
  rw [show (fun x => ‖(convGradConvW (rieszKernelGrad p.d p.s)
      (fun y => R.ρ q y * φ y) x) k‖) =
      (fun x => ‖ultK (u2_kap p.d p.s k) (fun y => R.ρ q y * φ y) x‖) by
        funext x
        exact congrArg norm (congrFun heq x)]
  simpa using (hcost (hρ q hq) ⟨hφc, B, hB⟩ (i := 0) (by omega))

#print axioms HRS.Fp81.S21.fp81s21_g4_density_convolution_cost
end HRS.Fp81.S21
