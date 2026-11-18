import HRS.MS.SpecAux40
import HRS.MS.MovOpAux7

/-!
# S8P: the `L²(dx)` profile `w_φ = W_φ - c √ρ = √ρ e_φ` of an eigenfunction is Schwartz (S8.7, packet b6)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_w_schwartz`: for Schwartz `φ`, `w = ν φ + √ρ (g * (√ρ φ)) - c √ρ` is a
Schwartz function (`g * (√ρ φ)` has temperate growth, `movc3a_Tg_tg`).  `s8p_therm_B`: the thermal data give `MovcTherm` with a bounded
`B` (`∂_i log ρ = -(βq) x_i + B_i`).
-/

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovDec HRS.MS.MovLin HRS.MS.MovC1 HRS.MS.Mov0

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

theorem s8p_therm_B (H : Mov2dTh d s β q ρ) :
    ∃ B : Euc d → Euc d, MovcTherm d ρ (β * q) B ∧ ∃ MB : ℝ, ∀ x, ‖B x‖ ≤ MB := by
  obtain ⟨B, -, hR, -⟩ := mv0_gapref H.hd H.hs0 H.hsd H.hq H.hβ H.hρ
  exact ⟨B, ⟨mul_pos H.hβ H.hq, hR⟩, mov0_B_bdd hR⟩

theorem s8p_w_schwartz (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R)
    (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x)) (φ : 𝓢R) (c : ℝ) :
    ∃ S : 𝓢R, (⇑S : Euc d → ℝ) = fun x => mov2eW d s β ρ φ x - c * Real.sqrt (ρ x) := by
  have hd1 : 1 ≤ d := by have := H.hd; omega
  obtain ⟨B, hT, -⟩ := s8p_therm_B H
  have hh : MovcG (fun y => Real.sqrt (ρ y) * φ y) := movc1_schwartz_G_mul hT.psi φ
  have htg := movc3a_Tg_tg hd1 H.hs0 H.hsd hh
  have hU : (fun x => HRS.Whole.convFun (rieszKernel d s) (fun y => Real.sqrt (ρ y) * φ y) x) =
      HRS.MS.MovForce.movb2_T (rieszKernel d s) (fun y => Real.sqrt (ρ y) * φ y) := by
    funext x; exact HRS.MS.MovForce.mv1_convFun_eq _ _ x
  refine ⟨β⁻¹ • φ + SchwartzMap.smulLeftCLM ℝ (HRS.MS.MovForce.movb2_T (rieszKernel d s) (fun y => Real.sqrt (ρ y) * φ y)) ψ0 -
    c • ψ0, ?_⟩
  funext x
  rw [SchwartzMap.sub_apply, SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply htg, hψ0]
  have := congrFun hU x
  simp only [mov2eW, smul_eq_mul]
  rw [← this]
  ring

end HRS.MS.Spec
