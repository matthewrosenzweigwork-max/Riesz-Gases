import HRS.MS.R2S11Aux22
import HRS.MS.MovThermAux1

/-!
# S11G: `S11KappaBound` from the stationary case of `r2_tensor_relaxation`

`S11KappaBound` does not involve `γ`.  Given the conclusion (b) of the tensor relaxation for the stationary
preparation `γ = β` at `u = 0` (diameter `≤ C` of the set of admissible stationary tensors) and the pointwise uniqueness of
the thermal density (`mv0_rho_eq`), the stationary tensor is bounded by the norm of one anchor plus `C`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S11G

open HRS.Whole
open HRS (Euc)

theorem s11g_kappaBound_of_stationary_relaxation {d : ℕ} (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s)
    (hs : s < (d : ℝ) / 2) (a β γ : ℝ) (ha : 0 < a) (hβ : 0 < β) (T : ℝ) (hT : 0 < T) (lam : ℝ)
    (hlam : 0 < lam)
    (h11β : type_of% (r2_tensor_relaxation hd s hs0 hs a β β ha hβ hβ.le (fun _ => hβ) T hT lam hlam)) :
    HRS.MS.R2S11.S11KappaBound d s a β γ T lam := by
  classical
  obtain ⟨c, hc, C, hC⟩ := h11β
  have hsd : s < (d : ℝ) := by
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  by_cases hex : ∃ ρ0 : Euc d → ℝ, IsThermalEquilibrium d s a β ρ0 ∧
      IsR2Poincare (HRS.Whole.withDensityReal ρ0) lam ∧
      ∃ κ0 : projTensor (R2X d T) 3, IsR2PathCubic d s a β β ρ0 T 0 κ0
  · obtain ⟨ρ0, hρ0, hP0, κ0, h0⟩ := hex
    refine ⟨‖κ0‖ + C, fun ρβ hρ hP κβ h2 => ?_⟩
    have hρeq : ρβ = ρ0 := by
      rw [HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ, HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ0]
    subst hρeq
    have h3 := (hC ρβ hρ hP).2 0 le_rfl κ0 κβ h0 h2
    simp only [mul_zero, Real.exp_zero, mul_one] at h3
    have h4 := norm_sub_le κ0 (κ0 - κβ)
    rw [sub_sub_cancel] at h4
    linarith
  · refine ⟨0, fun ρβ hρ hP κβ h2 => ?_⟩
    exact absurd ⟨ρβ, hρ, hP, κβ, h2⟩ hex

end HRS.MS.S11G
