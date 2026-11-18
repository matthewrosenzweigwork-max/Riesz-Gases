import HRS.MS.SA12X3N1G

/-!
# S.A.12 N1/N2 (SA12X3), part H: K1 (uniform bound) and K2 (convergence) for `γ_L ⋆ Q`, `∫ Q = 0`
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

theorem sa12x3n_conv_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (R : ℝ) (hR : 1 ≤ R) :
    ∃ L₁ Kc : ℝ, 1 ≤ L₁ ∧ 0 ≤ Kc ∧ ∀ L : ℝ, L₁ ≤ L → ∀ γ : Euc d → ℝ, IsPeriodicRieszKernel d s L γ →
      ∀ Q : Euc d → ℝ, Continuous Q → tsupport Q ⊆ closedBall 0 R → ∫ u, Q u = 0 → ∀ B : ℝ, (∀ u, |Q u| ≤ B) →
        ∀ x : Euc d, |HRS.Whole.convFun γ Q x| ≤ Kc * B := by
  obtain ⟨C0, hC0, hfar⟩ := sa12x3n_conv_far hd s hs0 hsd
  obtain ⟨δ, q, hδ, hq, hnear⟩ := sa12x3n_conv_near hd s hs0 hsd
  obtain ⟨Mq, Lq, hMq, hLq, hE⟩ := sa12x3n_E_bounds hq δ
  set V : ℝ := (volume (closedBall (0 : Euc d) R)).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  set Ig : ℝ := ∫ w in closedBall (0 : Euc d) (3 * R), |rieszKernel d s w| with hIg
  have hIg0 : 0 ≤ Ig := setIntegral_nonneg measurableSet_closedBall fun w _ => abs_nonneg _
  refine ⟨max (4 * R) (4 * R / δ), C0 * R * V + Ig + Mq * V, le_max_of_le_left (by linarith),
    by positivity, fun L hL γ hγ Q hQ hQs hQ0 B hB x => ?_⟩
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hL4 : 4 * R ≤ L := (le_max_left _ _).trans hL
  have hLδ : 4 * R ≤ δ * L := by
    have h1 : 4 * R / δ ≤ L := (le_max_right _ _).trans hL
    rw [div_le_iff₀ hδ] at h1
    linarith
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hLs : L ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  have hLs0 : 0 ≤ L ^ (-s) := (Real.rpow_pos_of_pos hL0 _).le
  obtain ⟨k, hk⟩ := sa12x3n_reduce hL0 x
  set x' : Euc d := x - L • latticePt k with hx'
  have hxx : HRS.Whole.convFun γ Q x = HRS.Whole.convFun γ Q x' := by
    have := sa12x3n_conv_periodic hγ.periodic Q x' k
    rw [show x' + L • latticePt k = x by rw [hx']; abel] at this
    exact this
  rw [hxx]
  by_cases hfarx : 2 * R ≤ ‖x'‖
  · have := hfar R hR L hL4 γ hγ Q hQ hQs hQ0 B hB x' hk hfarx
    refine this.trans ?_
    nlinarith [mul_nonneg (mul_nonneg hC0 (by linarith : (0 : ℝ) ≤ R)) hV0,
      mul_nonneg hIg0 hB0, mul_nonneg (mul_nonneg hMq hV0) hB0]
  · push Not at hfarx
    have hnear' : ‖x'‖ + R < δ * L := by linarith
    rw [hnear L hL1 γ hγ R Q hQ hQs hQ0 x' hnear']
    have h1 := sa12x3n_g_bound hs0 hsd (R := R) (ρ := 3 * R) hQs hB (x := x') (by linarith)
    have h2 := (hE L hL0 R (by linarith) Q hQ hQs hQ0 B hB x' hnear').1
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hLs0]
    have h3 : L ^ (-s) * |∫ w, q (L⁻¹ • w) * Q (x' - w)| ≤ Mq * (B * V) := by
      calc _ ≤ 1 * |∫ w, q (L⁻¹ • w) * Q (x' - w)| := mul_le_mul_of_nonneg_right hLs (abs_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact h2
    nlinarith [mul_nonneg hIg0 hB0, mul_nonneg (mul_nonneg hC0 (by linarith : (0 : ℝ) ≤ R)) hV0,
      mul_nonneg hMq hV0]

theorem sa12x3n_conv_conv (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (R : ℝ) (hR : 1 ≤ R) (R2 : ℝ) :
    ∃ L₁ Kq : ℝ, 1 ≤ L₁ ∧ 0 ≤ Kq ∧ ∀ L : ℝ, L₁ ≤ L → ∀ γ : Euc d → ℝ, IsPeriodicRieszKernel d s L γ →
      ∀ Q : Euc d → ℝ, Continuous Q → tsupport Q ⊆ closedBall 0 R → ∫ u, Q u = 0 → ∀ B : ℝ, (∀ u, |Q u| ≤ B) →
        ∀ x : Euc d, ‖x‖ ≤ R2 →
          |HRS.Whole.convFun γ Q x - HRS.Whole.convFun (rieszKernel d s) Q x| ≤ Kq * B / L := by
  obtain ⟨δ, q, hδ, hq, hnear⟩ := sa12x3n_conv_near hd s hs0 hsd
  obtain ⟨Mq, Lq, hMq, hLq, hE⟩ := sa12x3n_E_bounds hq δ
  set V : ℝ := (volume (closedBall (0 : Euc d) R)).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  refine ⟨max 1 ((|R2| + R) / δ + 1), Lq * R * V, le_max_left _ _, by positivity,
    fun L hL γ hγ Q hQ hQs hQ0 B hB x hx => ?_⟩
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hL0 : 0 < L := by linarith
  have hLδ : ‖x‖ + R < δ * L := by
    have h1 : (|R2| + R) / δ + 1 ≤ L := (le_max_right _ _).trans hL
    have h2 : (|R2| + R) / δ < L := by linarith
    rw [div_lt_iff₀ hδ] at h2
    nlinarith [le_abs_self R2]
  have hLs : L ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  have hLs0 : 0 ≤ L ^ (-s) := (Real.rpow_pos_of_pos hL0 _).le
  rw [hnear L hL1 γ hγ R Q hQ hQs hQ0 x hLδ, add_sub_cancel_left]
  have h2 := (hE L hL0 R (by linarith) Q hQ hQs hQ0 B hB x hLδ).2
  rw [abs_mul, abs_of_nonneg hLs0]
  calc L ^ (-s) * |∫ w, q (L⁻¹ • w) * Q (x - w)| ≤ 1 * |∫ w, q (L⁻¹ • w) * Q (x - w)| :=
        mul_le_mul_of_nonneg_right hLs (abs_nonneg _)
    _ ≤ Lq * (R / L) * (B * V) := by rw [one_mul]; exact h2
    _ = Lq * R * V * B / L := by field_simp

end HRS.MH.AdjointRd.Phase2SA12Construction
