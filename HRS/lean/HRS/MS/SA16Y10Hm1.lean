import HRS.MS.SA16Y10Sm1

/-!
# S.A.16 (SA16Y10) Hm1: homogeneity: a bound at weight `1` gives a bound linear in the weight `δ`
-/

set_option autoImplicit false

noncomputable section
open scoped ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

theorem sa16y10_lin_abstract {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (κ0 : ℕ) (Dw : ℝ) (rep : (E →L[ℝ] F) → (Euc d → ℝ) → Prop) (P : (Euc d → ℝ) → Prop)
    (hPcd : ∀ a, P a → ContDiff ℝ ∞ a) (hPsmul : ∀ a (c : ℝ), P a → P (fun y => c * a y))
    (hrep : ∀ T a (c : ℝ), rep T a → rep (c • T) (fun y => c * a y)) (C : ℝ)
    (H : ∀ a, P a → (∀ κ ≤ κ0, ∀ x, ‖iteratedFDeriv ℝ κ a x‖ ≤ 1 * (1 + ‖x‖) ^ Dw) →
      ∃ T : E →L[ℝ] F, ‖T‖ ≤ C ∧ rep T a) :
    ∀ a, P a → ∀ δ : ℝ, 0 ≤ δ → (∀ κ ≤ κ0, ∀ x, ‖iteratedFDeriv ℝ κ a x‖ ≤ δ * (1 + ‖x‖) ^ Dw) →
      ∃ T : E →L[ℝ] F, ‖T‖ ≤ C * δ ∧ rep T a := by
  intro a ha δ hδ hdec
  rcases hδ.eq_or_lt with h0 | hpos
  · subst h0
    have hz0 : ∀ y, a y = 0 := by
      intro y
      have h2 : |a y| ≤ 0 := by
        have := hdec 0 (Nat.zero_le _) y
        rw [norm_iteratedFDeriv_zero] at this
        simpa using this
      exact abs_nonpos_iff.1 h2
    have haz : a = fun _ => (0 : ℝ) := funext hz0
    obtain ⟨T0, -, hT0⟩ := H a ha (fun κ hκ x => by
      rw [haz]
      simp
      positivity)
    refine ⟨(0 : ℝ) • T0, by simp, ?_⟩
    have := hrep T0 a 0 hT0
    have e : (fun y => (0 : ℝ) * a y) = a := by rw [haz]; funext y; simp
    rw [e] at this
    exact this
  · have hδ' : δ⁻¹ ≠ 0 := inv_ne_zero hpos.ne'
    have hs := hPsmul a δ⁻¹ ha
    obtain ⟨T0, hT0n, hT0⟩ := H _ hs (fun κ hκ x => by
      have hc : ContDiffAt ℝ κ (fun y => a y) x := ((hPcd a ha).of_le (by exact_mod_cast le_top)).contDiffAt
      have e := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := δ⁻¹) (f := a) (x := x) (i := κ) hc
      have e' : iteratedFDeriv ℝ κ (fun y => δ⁻¹ * a y) x = δ⁻¹ • iteratedFDeriv ℝ κ a x := e
      rw [e', norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hpos.le)]
      calc δ⁻¹ * ‖iteratedFDeriv ℝ κ a x‖ ≤ δ⁻¹ * (δ * (1 + ‖x‖) ^ Dw) :=
            mul_le_mul_of_nonneg_left (hdec κ hκ x) (inv_nonneg.2 hpos.le)
        _ = 1 * (1 + ‖x‖) ^ Dw := by field_simp)
    refine ⟨δ • T0, ?_, ?_⟩
    · calc ‖δ • T0‖ = δ * ‖T0‖ := by rw [norm_smul, Real.norm_of_nonneg hpos.le]
        _ ≤ δ * C := mul_le_mul_of_nonneg_left hT0n hpos.le
        _ = C * δ := mul_comm _ _
    · have := hrep T0 _ δ hT0
      have e : (fun y => δ * (δ⁻¹ * a y)) = a := by
        funext y; field_simp
      rw [e] at this
      exact this

end HRS.Whole.AppendixA.Phase2SA16R

end
