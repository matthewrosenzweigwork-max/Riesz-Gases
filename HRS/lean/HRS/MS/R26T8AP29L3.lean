import HRS.MS.R26T8AP29L2

/-!
# S8.2 T8A P29 (linearity, part 3): `Psi` is linear on `TestBound` data and annihilates constants
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 12800000 in
theorem r26t8a_p29_Psi_linear (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) (C20 M20 : ℝ) (hfp : r26t8a_P20spec d a beta chi C20 M20)
    (hC20 : 0 ≤ C20) (MU : ℝ) (hMU : 0 < MU) (hK : M20 < MU)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (f g : Euc d → ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : TestBound (testOrder d) A f) (hg : TestBound (testOrder d) B g) (c : ℝ) :
    r26t8a_p29_Psi (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi (s85_Ulim a beta rho MU) (f + c • g) =
      r26t8a_p29_Psi (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi (s85_Ulim a beta rho MU) f +
        c • r26t8a_p29_Psi (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi (s85_Ulim a beta rho MU) g := by
  obtain ⟨hz, hrem, -⟩ := r26t8a_parametrix_linear d hd a beta ha hbeta chi hchi rho hrho f g A B hA hB hf hg c
  obtain ⟨Q1, R1, -, hR1, -, hcan1, -, -, hc1, hb1, -⟩ := hfp rho hrho f A hA hf
  obtain ⟨Q2, R2, -, hR2, -, hcan2, -, -, hc2, hb2, -⟩ := hfp rho hrho g B hB hg
  have h1 : r26t8a_p29_RemHyp d rho M20 (C20 * A) R1 := ⟨hc1, hb1, hcan1⟩
  have h2 : r26t8a_p29_RemHyp d rho M20 (C20 * B) R2 := ⟨hc2, hb2, hcan2⟩
  have hl := r26t8a_p29_psi_lin hd a beta M20 MU ha hbeta hMU hK rho hrho R1 R2 (C20 * A) (C20 * B)
    (mul_nonneg hC20 hA) (mul_nonneg hC20 hB) h1 h2 c
  funext x y
  unfold r26t8a_p29_Psi
  have e1 := congrFun (congrFun hz x) y
  have e2 := congrFun (congrFun hl x) y
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1 e2 ⊢
  rw [hrem, e1, ← hR1, ← hR2, e2]
  ring

theorem r26t8a_p29_Psi_const (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) (MU K : ℝ) (hMU : 0 < MU) (hK : K < MU)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (b : ℝ) :
    r26t8a_p29_Psi (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi (s85_Ulim a beta rho MU) (fun _ => b) =
      fun _ _ => 0 := by
  have hf : TestBound (testOrder d) 0 (fun _ : Euc d => b) := by
    refine ⟨contDiff_const, fun j hj1 _ x => ?_⟩
    rw [iteratedFDeriv_const_of_ne (𝕜 := ℝ) (E := Euc d) (by omega) b]
    simp
  obtain ⟨-, -, hc⟩ := r26t8a_parametrix_linear d hd a beta ha hbeta chi hchi rho hrho (fun _ => b) (fun _ => b) 0 0
    le_rfl le_rfl hf hf 0
  obtain ⟨hz, hr⟩ := hc b
  have hz0 := r26t8a_p29_psi_zero hd a beta K MU ha hbeta hMU hK rho hrho
  funext x y
  unfold r26t8a_p29_Psi
  have h1 : r26t8a_remainder (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi (fun _ => b) =
      fun _ _ => (0 : ℝ) := by rw [hr]; rfl
  rw [h1, hz]
  have := congrFun (congrFun hz0 x) y
  simp only [Pi.zero_apply] at this ⊢
  rw [this]; simp

end HRS.MS.R26T8A

end
