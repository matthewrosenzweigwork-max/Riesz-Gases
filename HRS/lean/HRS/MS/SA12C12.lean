import HRS.MS.SA12C11
import HRS.MS.Ker1Aux6
import HRS.MS.SA12BuildC19

/-!
# S.A.12(c), packet E7.03 (part 1): jets of `γ_L - g` near the origin

For `0 < |z| < δ L` and `n ≥ 1`: `D^nγ_L(z) - D^n g(z) = L^{-s-n} D^n q(z/L)` (derivatives of the smooth remainder
of `periodic_kernel_local`; the additive constant is killed since `n ≥ 1`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12c_kernel_local_deriv (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ (δ : ℝ) (q : Euc d → ℝ), 0 < δ ∧ δ ≤ 1 / 2 ∧ ContDiff ℝ ∞ q ∧ ∀ L : ℝ, 1 ≤ L →
      ∀ γ : Euc d → ℝ, IsPeriodicRieszKernel d s L γ →
        (∃ c0 : ℝ, ∀ z : Euc d, z ≠ 0 → ‖z‖ < δ * L →
          γ z = rieszKernel d s z + (c0 + L ^ (-s) * q (L⁻¹ • z))) ∧
        ∀ n : ℕ, 1 ≤ n → ∀ z : Euc d, z ≠ 0 →
        ‖z‖ < δ * L →
          iteratedFDeriv ℝ n γ z - iteratedFDeriv ℝ n (rieszKernel d s) z =
            (L ^ (-s) * (L⁻¹) ^ n) • iteratedFDeriv ℝ n q (L⁻¹ • z) := by
  obtain ⟨q, δ0, hδ0, hq, hloc⟩ := HRS.MS.Ker1.ker1_decomp hd hs0 hsd
  refine ⟨min δ0 (1 / 2), q, lt_min hδ0 (by norm_num), min_le_right _ _, hq, fun L hL γ hγ => ?_⟩
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  refine ⟨⟨if s = 0 then Real.log L else 0, fun z hz0 hz => ?_⟩, fun n hn z hz0 hz => ?_⟩
  · have hz1 : ‖z‖ < δ0 * L := lt_of_lt_of_le hz (mul_le_mul_of_nonneg_right (min_le_left _ _) hL0.le)
    have hz2 : ‖z‖ ≤ L / 2 := by
      have : min δ0 (1 / 2) * L ≤ 1 / 2 * L := mul_le_mul_of_nonneg_right (min_le_right _ _) hL0.le
      linarith
    have hoff := HRS.MS.Ker1.ker1_offLattice_of_half hL0 hz0 hz2
    have h1 : γ z = HRS.MS.Ker1.ker1_gam d s L z := HRS.MS.Ker1.ker1_eq_gam hd hs0 hsd hL0 hγ z hoff
    have h2 := (HRS.MS.Ker1.ker1_gam_eventually hd hloc hL0 hz0 hz1).self_of_nhds
    rw [h1, h2]; ring
  · have hz1 : ‖z‖ < δ0 * L := lt_of_lt_of_le hz (mul_le_mul_of_nonneg_right (min_le_left _ _) hL0.le)
    have hz2 : ‖z‖ ≤ L / 2 := by
      have : min δ0 (1 / 2) * L ≤ 1 / 2 * L := mul_le_mul_of_nonneg_right (min_le_right _ _) hL0.le
      linarith
    have hoff := HRS.MS.Ker1.ker1_offLattice_of_half hL0 hz0 hz2
    have hev := HRS.MS.Ker1.ker1_eventually_eq_gam hd hs0 hsd hL0 hγ hoff
    rw [(hev.iteratedFDeriv ℝ n).eq_of_nhds]
    exact HRS.MS.Ker1.ker1_gam_sub_E hd hq hloc hL0 hz0 hz1 (Or.inl (by omega))

/-- Uniform bound of the derivatives of `q` on the ball of radius `1/2`, up to order `N`. -/
theorem sa12c_q_bound {q : Euc d → ℝ} (hq : ContDiff ℝ ∞ q) (N : ℕ) :
    ∃ Cq : ℝ, 0 ≤ Cq ∧ ∀ n ≤ N, ∀ w : Euc d, ‖w‖ ≤ 1 / 2 → ‖iteratedFDeriv ℝ n q w‖ ≤ Cq := by
  have h1 : ∀ n : ℕ, ∃ C : ℝ, ∀ w : Euc d, ‖w‖ ≤ 1 / 2 → ‖iteratedFDeriv ℝ n q w‖ ≤ C := by
    intro n
    have hc : Continuous (iteratedFDeriv ℝ n q) := hq.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Euc d) (1 / 2)).exists_bound_of_continuousOn hc.continuousOn
    exact ⟨C, fun w hw => hC w (by simpa using hw)⟩
  choose C hC using h1
  refine ⟨∑ n ∈ Finset.range (N + 1), |C n|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun n hn w hw => ?_⟩
  refine (hC n w hw).trans ?_
  refine (le_abs_self _).trans ?_
  exact Finset.single_le_sum (f := fun n => |C n|) (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hn))

end HRS.MH.AdjointRd.Phase2SA12C
