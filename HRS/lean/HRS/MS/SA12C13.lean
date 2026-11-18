import HRS.MS.SA12C12

/-!
# S.A.12(c), packet E7.03 (part 2): far jets of `γ_L` and `g` on the centred cube

For `z` in the closed cube `|z_i| ≤ L/2`, `z ≠ 0`, `1 ≤ n ≤ m+2`:
`‖D^nγ_L(z)‖ + ‖D^n g(z)‖ ≤ C₁ (|z|^{-s-n} + L^{-s-n})`  (`periodic_kernel_cube`, `ker1_E_bound`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12c_far_deriv_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) :
    ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ L : ℝ, 1 ≤ L → ∀ γ : Euc d → ℝ, IsPeriodicRieszKernel d s L γ →
      ∀ n : ℕ, 1 ≤ n → n ≤ m + 2 → ∀ z : Euc d, z ≠ 0 → (∀ i, |z i| ≤ L / 2) →
        ‖iteratedFDeriv ℝ n γ z‖ + ‖iteratedFDeriv ℝ n (rieszKernel d s) z‖ ≤
          C1 * (‖z‖ ^ (-s - n) + L ^ (-s - n)) := by
  obtain ⟨Cc, hCc0, hCc⟩ := periodic_kernel_cube hd s hs0 hsd m
  have hker0 : ∀ n : ℕ, ∃ Cn : ℝ, 0 ≤ Cn ∧ (1 ≤ n → ∀ ξ : Euc d, ξ ≠ 0 →
      ‖iteratedFDeriv ℝ n (rieszKernel d s) ξ‖ ≤ Cn * ‖ξ‖ ^ (-s - n)) := by
    intro n
    by_cases hn : 1 ≤ n
    · obtain ⟨C, hC0, hC⟩ := HRS.MS.Ker1.ker1_E_bound (d := d) hs0 n (by
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        linarith)
      exact ⟨C, hC0, fun _ ξ hξ => hC ξ hξ⟩
    · exact ⟨0, le_rfl, fun h1 => absurd h1 hn⟩
  choose Ck hCk0 hCk using hker0
  set Cg : ℝ := ∑ n ∈ Finset.range (m + 3), Ck n with hCg
  have hCg0 : 0 ≤ Cg := Finset.sum_nonneg fun n _ => hCk0 n
  refine ⟨Cc + Cg, add_nonneg hCc0 hCg0, fun L hL γ hγ n hn1 hn2 z hz0 hz => ?_⟩
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have hns : 0 < (n : ℝ) + s := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    linarith
  have h1 := hCc L hL γ hγ n hn2 hns z hz0 hz
  have hite : (if 0 < s then L ^ (-s - n) else 0) + (if s = 0 then L ^ (-(n : ℝ)) else 0) ≤ L ^ (-s - n) := by
    rcases hs0.eq_or_lt with h | h
    · subst h; simp
    · have : ¬ s = 0 := h.ne'
      simp [h, this]
  have hCkn : Ck n ≤ Cg := Finset.single_le_sum (f := Ck) (fun _ _ => hCk0 _)
    (Finset.mem_range.2 (by omega))
  have h2 := hCk n hn1 z hz0
  have ha : 0 ≤ ‖z‖ ^ (-s - n) := Real.rpow_nonneg (norm_nonneg _) _
  have hb : 0 ≤ L ^ (-s - n) := Real.rpow_nonneg hL0.le _
  have h3 : ‖iteratedFDeriv ℝ n γ z‖ ≤ Cc * (‖z‖ ^ (-s - n) + L ^ (-s - n)) := by
    refine h1.trans ?_
    have : ‖z‖ ^ (-s - n) + (if 0 < s then L ^ (-s - n) else 0) + (if s = 0 then L ^ (-(n : ℝ)) else 0) ≤
        ‖z‖ ^ (-s - n) + L ^ (-s - n) := by linarith
    exact mul_le_mul_of_nonneg_left this hCc0
  have h4 : ‖iteratedFDeriv ℝ n (rieszKernel d s) z‖ ≤ Cg * (‖z‖ ^ (-s - n) + L ^ (-s - n)) :=
    h2.trans (by nlinarith [mul_le_mul_of_nonneg_right hCkn ha, mul_nonneg hCg0 hb])
  nlinarith [h3, h4]

end HRS.MH.AdjointRd.Phase2SA12C
