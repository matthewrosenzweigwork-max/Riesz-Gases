import HRS.MS.SA12X3N1B

/-!
# S.A.12 N1/N2 (SA12X3), part C: a mean value bound for the periodic kernel away from the lattice
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

theorem sa12x3n_far_diff (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ R : ℝ, 1 ≤ R → ∀ L : ℝ, 4 * R ≤ L → ∀ γ : Euc d → ℝ, IsPeriodicRieszKernel d s L γ →
      ∀ x : Euc d, (∀ i, |x i| ≤ L / 2) → 2 * R ≤ ‖x‖ → ∀ u : Euc d, ‖u‖ ≤ R →
        |γ (x - u) - γ x| ≤ C0 * ‖u‖ := by
  obtain ⟨C, hC0, hcube⟩ := periodic_kernel_cube hd s hs0 hsd 0
  refine ⟨3 * C, by positivity, fun R hR L hL γ hγ x hx hxn u hu => ?_⟩
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have key : ∀ w ∈ closedBall x R, DifferentiableAt ℝ γ w ∧ ‖fderiv ℝ γ w‖ ≤ 3 * C := by
    intro w hw
    have hwR : ‖x - w‖ ≤ R := by
      rw [mem_closedBall, dist_eq_norm, norm_sub_rev] at hw; exact hw
    obtain ⟨k, hk⟩ := sa12x3n_reduce hL0 w
    have hw1 : w = x - (x - w) := by abel
    have hnorm : R ≤ ‖w - L • latticePt k‖ := by
      have := sa12x3n_reduce_norm hR hL hx hxn hwR (k := k) (by rw [← hw1]; exact hk)
      rwa [← hw1] at this
    have hw'0 : w - L • latticePt k ≠ 0 := by
      intro h; rw [h, norm_zero] at hnorm; linarith
    have hoff : ∀ z : Fin d → ℤ, w ≠ L • latticePt z := by
      intro z hz
      apply hw'0
      have : w - L • latticePt k = L • latticePt (z - k) := by
        rw [hz]; ext i; simp [latticePt, mul_sub]
      rw [this]
      have hzk : z - k = 0 := by
        funext i
        have h1 := hk i
        rw [hz] at h1
        have e : (L • latticePt z - L • latticePt k) i = L * ((z i : ℝ) - k i) := by
          simp [latticePt, mul_sub]
        rw [e, abs_mul, abs_of_pos hL0] at h1
        have h2 : |((z i : ℝ) - k i)| ≤ 1 / 2 := by nlinarith
        have h3 : |z i - k i| < 1 := by
          have : |((z i - k i : ℤ) : ℝ)| < 1 := by push_cast; linarith
          exact_mod_cast this
        have : z i - k i = 0 := Int.abs_lt_one_iff.1 h3
        simpa using this
      rw [hzk]; ext i; simp [latticePt]
    refine ⟨((hγ.smooth.contDiffAt ((HRS.MS.Ker1.ker1_isOpen_offLattice hL0).mem_nhds hoff)).differentiableAt
      (by simp)), ?_⟩
    have hper := sa12v_iter_periodic L (u := γ) hγ.periodic 1 (w - L • latticePt k) k
    have hw2 : w - L • latticePt k + L • latticePt k = w := by abel
    rw [hw2] at hper
    rw [← norm_iteratedFDeriv_one, hper]
    have hc := hcube L hL1 γ hγ 1 (by norm_num) (by push_cast; linarith) (w - L • latticePt k) hw'0 hk
    refine hc.trans ?_
    have hn1 : (1 : ℝ) ≤ ‖w - L • latticePt k‖ := hR.trans hnorm
    have e1 : ‖w - L • latticePt k‖ ^ (-s - ((1 : ℕ) : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hn1 (by push_cast; linarith)
    have e2 : (if 0 < s then L ^ (-s - ((1 : ℕ) : ℝ)) else 0) ≤ 1 := by
      split_ifs
      · exact Real.rpow_le_one_of_one_le_of_nonpos hL1 (by push_cast; linarith)
      · norm_num
    have e3 : (if s = 0 then L ^ (-((1 : ℕ) : ℝ)) else 0) ≤ 1 := by
      split_ifs
      · exact Real.rpow_le_one_of_one_le_of_nonpos hL1 (by push_cast; linarith)
      · norm_num
    nlinarith
  have hconv : Convex ℝ (closedBall x R) := convex_closedBall x R
  have hxm : x ∈ closedBall x R := mem_closedBall_self (by linarith)
  have hym : x - u ∈ closedBall x R := by
    rw [mem_closedBall, dist_eq_norm]; simpa using hu
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (fun w hw => (key w hw).1) (fun w hw => (key w hw).2)
    hconv hxm hym
  rw [Real.norm_eq_abs] at this
  simpa using this

end HRS.MH.AdjointRd.Phase2SA12Construction
