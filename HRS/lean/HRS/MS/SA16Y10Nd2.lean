import HRS.MS.SA16Y10Nd1
import HRS.MS.SA16QFin6
import HRS.MP.RdInit

/-!
# S.A.16 (SA16Y10) Nd2: `sa16y10_node_diff_sub`
-/

set_option autoImplicit false

noncomputable section
open scoped ContDiff
open Filter

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA MeasureTheory Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

variable {d : ℕ}

/-- weight of the mollification of a function with weighted derivative decay -/
lemma sa16y10_mol_weight (hd : 1 ≤ d) (N : ℕ) {g : Euc d → ℝ} {m : ℕ} (hg : ContDiff ℝ ((m + 2 : ℕ) : WithTop ℕ∞) g) {δ : ℝ}
    (hdec : ∀ κ ≤ m + 2, ∀ x, ‖iteratedFDeriv ℝ κ g x‖ ≤ δ * (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ))) :
    ∀ κ ≤ m + 2, ∀ x, ‖iteratedFDeriv ℝ κ (sa16q_mol N g) x‖ ≤
      ((d : ℝ) ^ (m + 2) * 2 ^ (d + 3) * δ) * (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ)) := by
  intro κ hκ x
  have hgκ : ContDiff ℝ κ g := hg.of_le (by exact_mod_cast hκ)
  have hδ : 0 ≤ δ := by
    have := hdec 0 (Nat.zero_le _) 0
    have h2 : 0 ≤ ‖iteratedFDeriv ℝ 0 g 0‖ := norm_nonneg _
    have h3 : 0 < (1 + ‖(0 : Euc d)‖) ^ (-((d + 3 : ℕ) : ℝ)) := Real.rpow_pos_of_pos (by simp) _
    nlinarith
  have hw : ∀ r : Fin κ → Fin d, ∀ y, |partialDeriv r g y| * (1 + ‖y‖) ^ (d + 3) ≤ δ := by
    intro r y
    have h1 := (HRS.MP.RdInit.mri_abs_partialDeriv_le r g y).trans (hdec κ hκ y)
    have hpos : 0 < (1 + ‖y‖) ^ (d + 3) := by positivity
    have hω : (1 + ‖y‖) ^ (-((d + 3 : ℕ) : ℝ)) = ((1 + ‖y‖) ^ (d + 3))⁻¹ := by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
    rw [hω] at h1
    calc |partialDeriv r g y| * (1 + ‖y‖) ^ (d + 3) ≤ δ * ((1 + ‖y‖) ^ (d + 3))⁻¹ * (1 + ‖y‖) ^ (d + 3) :=
          mul_le_mul_of_nonneg_right h1 hpos.le
      _ = δ := by field_simp
  have h1 := sa16q_weight_conv (a := sa16q_mol N g) (κ := κ) (Λ2 := 2 ^ (d + 3) * δ)
    (fun r y => sa16q_mol_pd_weight N hgκ (Λ1 := δ) hw r y) x
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
