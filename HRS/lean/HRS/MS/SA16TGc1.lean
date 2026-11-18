import HRS.MS.SA16TMo2

/-!
# S.A.16 (SA16T) Gc1: `χ_R (ρ_n ⋆ G)` for an arbitrary cutoff radius `R ≥ 1`, and its decay constant

`sa16t_bcR_small` generalizes `sa16t_bc_small` (cutoff radius `R` free).  `sa16t_nu_decay`: `ν = χ_R (ρ_n ⋆ G)` satisfies
`‖D^j ν‖ ≤ Cn (1+2R)^{d+3} A (1+|y|)^{-(d+3)}` when `|G| ≤ A` on the ball of radius `2R+1`.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16P

section Gc1
variable {d : ℕ}

theorem sa16t_bcR_small (d k n : ℕ) :
    ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ R : ℝ, 1 ≤ R → ∀ G : Euc d → ℝ, Continuous G → ∀ A : ℝ, (∀ y, ‖y‖ ≤ 2 * R + 1 → |G y| ≤ A) →
      ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (fun y => sa16j_chi d R y * sa16j_conv (sa16y_rho d n) G y) x‖ ≤ Cn * A := by
  obtain ⟨Bχ, hB0, hBχ⟩ := sa16j_cut_bound d k
  refine ⟨2 ^ k * (max 1 Bχ * sa16t_Crho d n k), by have := sa16t_Crho_nonneg d n k; positivity,
    fun R hR1 G hG A hA j hjk x => ?_⟩
  have hR0 : 0 < R := by linarith
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 (by simp; linarith))
  have hhs : ContDiff ℝ ∞ (sa16j_conv (sa16y_rho d n) G) := sa16y_mollify_smooth n hG
  have hχs := sa16j_chi_contDiff d (R)
  have hKu0 : 0 ≤ max 1 Bχ * sa16t_Crho d n k * A := by
    have := sa16t_Crho_nonneg d n k; positivity
  by_cases hx : 2 * R < ‖x‖
  · rw [sa16t_vanish hR0 _ hx j, norm_zero]
    have := sa16t_Crho_nonneg d n k; positivity
  · push Not at hx
    have hL' := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (hχs.of_le (by exact_mod_cast le_top))
      (hhs.of_le (by exact_mod_cast le_top)) x (n := j) (N := (j : ℕ∞ω)) le_rfl
    refine hL'.trans ?_
    have hterm : ∀ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (sa16j_chi d R) x‖ *
        ‖iteratedFDeriv ℝ (j - i) (sa16j_conv (sa16y_rho d n) G) x‖ ≤
        (j.choose i : ℝ) * (max 1 Bχ * sa16t_Crho d n k * A) := by
      intro i hi
      have hi' : i ≤ j := by have := Finset.mem_range.1 hi; omega
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      have h1 := hBχ R hR1 i (hi'.trans hjk) x
      have h2 := sa16t_mollify_small hG n k (A := A) x (fun z hz => hA _ (by
        calc ‖x - z‖ ≤ ‖x‖ + ‖z‖ := norm_sub_le _ _
          _ ≤ 2 * R + 1 := by linarith)) (j := j - i) (by omega)
      calc ‖iteratedFDeriv ℝ i (sa16j_chi d R) x‖ *
            ‖iteratedFDeriv ℝ (j - i) (sa16j_conv (sa16y_rho d n) G) x‖
          ≤ max 1 Bχ * (sa16t_Crho d n k * A) :=
            mul_le_mul (h1.trans (le_max_right _ _)) h2 (norm_nonneg _) (by positivity)
        _ = _ := by ring
    calc ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (sa16j_chi d R) x‖ *
          ‖iteratedFDeriv ℝ (j - i) (sa16j_conv (sa16y_rho d n) G) x‖
        ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (max 1 Bχ * sa16t_Crho d n k * A) :=
          Finset.sum_le_sum hterm
      _ = 2 ^ j * (max 1 Bχ * sa16t_Crho d n k * A) := by
          rw [← Finset.sum_mul]
          have : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) = 2 ^ j := by
            exact_mod_cast Nat.sum_range_choose j
          rw [this]
      _ ≤ 2 ^ k * (max 1 Bχ * sa16t_Crho d n k) * A := by
          rw [mul_assoc (2 ^ k)]
          calc 2 ^ j * (max 1 Bχ * sa16t_Crho d n k * A) ≤ 2 ^ k * (max 1 Bχ * sa16t_Crho d n k * A) :=
                mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hjk) hKu0
            _ = _ := by ring


theorem sa16t_nu_decay (d k n : ℕ) :
    ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ R : ℝ, 1 ≤ R → ∀ G : Euc d → ℝ, Continuous G → ∀ A : ℝ, 0 ≤ A →
      (∀ y, ‖y‖ ≤ 2 * R + 1 → |G y| ≤ A) → ∀ j ≤ k, ∀ x,
      ‖iteratedFDeriv ℝ j (fun y => sa16j_chi d R y * sa16j_conv (sa16y_rho d n) G y) x‖ ≤
        (Cn * (1 + 2 * R) ^ ((d : ℝ) + 3) * A) * sa16p_w d x := by
  obtain ⟨Cn, hCn0, hCn⟩ := sa16t_bcR_small d k n
  refine ⟨Cn, hCn0, fun R hR G hG A hA0 hA j hj x => ?_⟩
  have hR0 : 0 < R := by linarith
  by_cases hx : 2 * R < ‖x‖
  · rw [sa16t_vanish hR0 _ hx j, norm_zero]
    have := sa16p_w_pos (d := d) x
    positivity
  · push Not at hx
    refine (hCn R hR G hG A hA j hj x).trans ?_
    have hw : 1 ≤ (1 + 2 * R) ^ ((d : ℝ) + 3) * sa16p_w d x := by
      unfold sa16p_w
      have h1 : (1 + ‖x‖) ^ (-((d : ℝ) + 3)) ≥ (1 + 2 * R) ^ (-((d : ℝ) + 3)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith)
      calc (1 : ℝ) = (1 + 2 * R) ^ ((d : ℝ) + 3) * (1 + 2 * R) ^ (-((d : ℝ) + 3)) := by
            rw [← Real.rpow_add (by positivity)]; simp
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
    have hCA : 0 ≤ Cn * A := mul_nonneg hCn0 hA0
    calc Cn * A ≤ Cn * A * ((1 + 2 * R) ^ ((d : ℝ) + 3) * sa16p_w d x) := le_mul_of_one_le_right hCA hw
      _ = _ := by ring

end Gc1

end HRS.Whole.AppendixA.Phase2SA16R
