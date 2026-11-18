import HRS.MS.SA16Y11Nl1
import HRS.MS.SA16Y6COp1
import HRS.MS.SA16Y6CSm1

/-!
# S.A.16 (SA16Y11) Nl1c: critical copy of `Nl1` (`s = d-1`, Calderon-Zygmund order-one operator)

`sa16y11c_Gop_diff`: as `sa16y11_Gop_diff` with `sa16y6c_G_smooth` / `sa16y6c_isoop_add/smul` (hypothesis `s = d-1`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Nl1c
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

set_option maxHeartbeats 3200000 in
theorem sa16y11c_Gop_diff (d m : ℕ) (hd : 1 ≤ d) (s p MB : ℝ) [Fact (2 ≤ p)] (hs0 : 0 ≤ s)
    (hs1 : s = (d : ℝ) - 1) (hfar : (d : ℝ) < p * (s + 1)) (Wd : ℝ) (hWd : 0 ≤ Wd) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Matrix (Fin d) (Fin d) ℝ, (∀ i j, |M i j| ≤ MB) →
      ∀ a1 a2 : Euc d → ℝ, sa16q_SB a1 → sa16q_SB a2 → sa16y5_Dec (m + 3) Wd a1 → sa16y5_Dec (m + 3) Wd a2 →
      ∀ δ : ℝ, 0 ≤ δ → sa16y5_Dec (m + 2) δ (fun y => a1 y - a2 y) →
      ∀ y : WmpSpace d (m + 1 + 1) p,
        ‖sa16r_iota d m p ((sa16y5_Gop d m p s M a1 - sa16y5_Gop d m p s M a2) y)‖ ≤ C * δ * ‖y‖ := by
  obtain ⟨C0, hC0, hG0⟩ := sa16y6c_G_smooth d m hd s p MB 1 hs0 hs1 hfar zero_le_one
  obtain ⟨C1, hC1, hG1⟩ := sa16y6c_G_smooth d (m + 1) hd s p MB Wd hs0 hs1 hfar hWd
  refine ⟨C0, hC0, fun M hM a1 a2 hS1 hS2 hD1 hD2 δ hδ hDd y => ?_⟩
  obtain ⟨T1, -, hT1⟩ := hG1 M hM a1 hS1 (fun κ hκ x => hD1 κ (by omega) x)
  obtain ⟨T2, -, hT2⟩ := hG1 M hM a2 hS2 (fun κ hκ x => hD2 κ (by omega) x)
  have hT1' : SA16IsoOp d (m + 1) p s M a1 T1 := hT1
  have hT2' : SA16IsoOp d (m + 1) p s M a2 T2 := hT2
  rw [sa16y5_Gop_eq hT1', sa16y5_Gop_eq hT2']
  rcases hδ.eq_or_lt with h0 | hpos
  · -- δ = 0: the densities coincide
    have heq : a1 = a2 := by
      funext x
      have := hDd 0 (by omega) x
      rw [← h0, zero_mul, norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
      have : a1 x - a2 x = 0 := abs_nonpos_iff.1 this
      linarith
    subst heq
    have : T1 = T2 := by rw [← sa16y5_Gop_eq hT1', ← sa16y5_Gop_eq hT2']
    subst this
    simp [← h0]
  · -- δ > 0
    set a : Euc d → ℝ := fun x => a1 x - a2 x with ha
    have hSBa : sa16q_SB a := sa16q_SB_sub hS1 hS2
    set at' : Euc d → ℝ := fun x => δ⁻¹ * a x with hat
    have hSBt : sa16q_SB at' := sa16y11_SB_smul _ hSBa
    have hDt : sa16y5_Dec (m + 2) 1 at' := by
      have := sa16y11_Dec_smul (hSBa.1) hDd δ⁻¹
      rwa [abs_of_pos (inv_pos.2 hpos), inv_mul_cancel₀ hpos.ne'] at this
    obtain ⟨Tt, hTtn, hTt⟩ := hG0 M hM at' hSBt (fun κ hκ x => by simpa using hDt κ hκ x)
    have hTt' : SA16IsoOp d m p s M at' Tt := hTt
    have hG1 : sa16y4_Good a1 := sa16q_SB_C1 hS1
    have hG2 : sa16y4_Good a2 := sa16q_SB_C1 hS2
    have hGt : sa16y4_Good at' := sa16q_SB_C1 hSBt
    have hdiff1 : SA16IsoOp d (m + 1) p s M a (T1 - T2) := by
      have h := sa16y6c_isoop_add hd hs0 hs1 M hG1 (sa16y4_good_smul (-1) hG2) hT1'
        (sa16y6c_isoop_smul hd hs0 hs1 M (-1) hG2 hT2')
      have e1 : (fun y => a1 y + (-1 : ℝ) * a2 y) = a := by funext y; simp only [ha]; ring
      have e2 : T1 + (-1 : ℝ) • T2 = T1 - T2 := ContinuousLinearMap.ext fun z => by
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply]
        rw [sub_eq_add_neg]; congr 1; exact neg_one_smul ℝ (T2 z)
      rw [e1, e2] at h; exact h
    have hdiff0 : SA16IsoOp d m p s M a (δ • Tt) := by
      have h := sa16y6c_isoop_smul hd hs0 hs1 M δ hGt hTt'
      have e : (fun y => δ * at' y) = a := by funext y; simp only [hat]; field_simp
      rw [e] at h; exact h
    have hcomp : (sa16r_iota d m p).comp (T1 - T2) = (δ • Tt).comp (sa16r_iota d (m + 1) p) := by
      refine sa16so_clm_ext fun φ => ?_
      refine sa16r_wrep_inj d m p _ _ ?_
      simp only [ContinuousLinearMap.comp_apply]
      rw [sa16r_iota_Jcc (m + 1) φ]
      filter_upwards [sa16r_iota_wrep (p := p) m ((T1 - T2) (sa16r_Jcc d (m + 1 + 1) p φ)), hdiff1 φ, hdiff0 φ]
        with x e1 e2 e3
      rw [e1, e2, e3]
    have hy := congrArg (fun L => L y) hcomp
    simp only [ContinuousLinearMap.comp_apply] at hy
    rw [hy]
    have h1 : ‖δ • Tt‖ ≤ δ * C0 := by
      refine (ContinuousLinearMap.opNorm_smul_le δ Tt).trans ?_
      rw [Real.norm_eq_abs, abs_of_pos hpos]
      exact mul_le_mul_of_nonneg_left hTtn hpos.le
    have h2 : ‖sa16r_iota d (m + 1) p y‖ ≤ ‖y‖ :=
      ((sa16r_iota d (m + 1) p).le_opNorm y).trans (by
        have := sa16y4_iota_norm (d := d) (p := p) (m + 1)
        nlinarith [norm_nonneg y])
    calc ‖(δ • Tt) (sa16r_iota d (m + 1) p y)‖ ≤ ‖δ • Tt‖ * ‖sa16r_iota d (m + 1) p y‖ :=
          (δ • Tt).le_opNorm _
      _ ≤ (δ * C0) * ‖y‖ := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = C0 * δ * ‖y‖ := by ring

end Nl1c

end HRS.Whole.AppendixA.Phase2SA16R

end
