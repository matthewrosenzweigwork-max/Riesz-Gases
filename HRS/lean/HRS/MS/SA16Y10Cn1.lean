import HRS.MS.SA16Y10Sr1
import HRS.MS.SA16QApp2
import HRS.MS.SA16QFin2

/-!
# S.A.16 (SA16Y10) Cn1: from `coeffNormE` to the weighted derivative decay used by the difference-operator lemmas

`sa16y10_decay_of_coeffNormE`: `coeffNormE d s m g ≤ ofReal δ` gives, for `κ ≤ m+2`,
`‖D^κ g(x)‖ ≤ (d^{m+2} 2^{d+3} δ) (1+|x|)^{-(d+3)}`.
-/

set_option autoImplicit false

noncomputable section
open scoped ContDiff
open Filter MeasureTheory

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

variable {d : ℕ}

theorem sa16y10_decay_of_coeffNormE (hd : 1 ≤ d) {s : ℝ} {m : ℕ} {g : Euc d → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : coeffNormE d s m g ≤ ENNReal.ofReal δ) :
    ∀ κ ≤ m + 2, ∀ x, ‖iteratedFDeriv ℝ κ g x‖ ≤
      ((d : ℝ) ^ (m + 2) * 2 ^ (d + 3) * δ) * (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ)) := by
  intro κ hκ x
  have hws : weightedSupE (m + 2) ((d : ℝ) + 3) g ≤ ENNReal.ofReal δ :=
    le_trans (by unfold coeffNormE; exact le_add_right le_add_self) h
  have hpd : ∀ r : Fin κ → Fin d, ∀ y, |partialDeriv r g y| * (1 + ‖y‖) ^ (d + 3) ≤ 2 ^ (d + 3) * δ := by
    intro r y
    have h1 : ENNReal.ofReal (jbracket y ^ ((d : ℝ) + 3) * |partialDeriv r g y|) ≤
        weightedSupE (m + 2) ((d : ℝ) + 3) g := by
      unfold weightedSupE derivSupE
      exact le_iSup_of_le ⟨κ, by omega⟩ (le_iSup_of_le r (le_iSup_of_le y le_rfl))
    have h2 : jbracket y ^ ((d : ℝ) + 3) * |partialDeriv r g y| ≤ δ :=
      (ENNReal.ofReal_le_ofReal_iff hδ).1 (h1.trans hws)
    have h3 : jbracket y ^ ((d : ℝ) + 3) = jbracket y ^ (d + 3) := by
      rw [← Real.rpow_natCast]; push_cast; rfl
    rw [h3] at h2
    have h4 : (1 + ‖y‖) ^ (d + 3) ≤ 2 ^ (d + 3) * jbracket y ^ (d + 3) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) (sa16q_jb_le y) _
    calc |partialDeriv r g y| * (1 + ‖y‖) ^ (d + 3)
        ≤ |partialDeriv r g y| * (2 ^ (d + 3) * jbracket y ^ (d + 3)) := by gcongr
      _ = 2 ^ (d + 3) * (jbracket y ^ (d + 3) * |partialDeriv r g y|) := by ring
      _ ≤ 2 ^ (d + 3) * δ := by gcongr
  have h1 := sa16q_weight_conv (a := g) (κ := κ) (Λ2 := 2 ^ (d + 3) * δ) (fun r y => hpd r y) x
  refine h1.trans ?_
  have hω : 0 ≤ (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ)) := Real.rpow_nonneg (by positivity) _
  have hpw : (d : ℝ) ^ κ ≤ (d : ℝ) ^ (m + 2) := pow_le_pow_right₀ (by exact_mod_cast hd) hκ
  have hc : 0 ≤ 2 ^ (d + 3) * δ := by positivity
  calc (d : ℝ) ^ κ * (2 ^ (d + 3) * δ) * (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ))
      ≤ (d : ℝ) ^ (m + 2) * (2 ^ (d + 3) * δ) * (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpw hc) hω
    _ = _ := by ring

end HRS.Whole.AppendixA.Phase2SA16R

end
