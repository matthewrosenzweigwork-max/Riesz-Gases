import HRS.MS.S82RN19

/-!
# S8.2 R02: `pointwise_pin_comparison` (frozen statement of the Pro skeleton `S82.R02`)
Part 1 (sup norm of the reference marginal density): `S82RN19` (cavity equation + absorption).
Part 2 (pointwise comparison after at most two pins/removals): `S82RN14`, via the dual
position-weighted Lipschitz transfer `S82RM1..S82RM23` and the analytic bridge `S82RN1..S82RN13`.
-/

set_option autoImplicit false
noncomputable section

namespace HRS.MS.Phase2S82
open HRS HRS.Whole

/-- Pointwise comparison after at most two pins/removals. No lower bound on `rho` is required. -/
theorem pointwise_pin_comparison (d : ℕ) (hd : 2 ≤ d)
    (a beta C0 : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (q : Euc d → ℝ) (hq : ShortRangePole d q) :
    ∃ C : ℝ, 0 < C ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ h : ℕ → Euc d → ℝ,
      WeakReferenceSetup d a beta rho q h C0 → PinComparison beta rho q h C := by
  obtain ⟨C1, hC1, h1⟩ := HRS.MS.S82R.s82r_part1 hd a beta C0 ha hbeta q hq
  obtain ⟨C2, hC2, h2⟩ := HRS.MS.S82R.s82r_part2 hd a beta C0 ha hbeta q hq
  refine ⟨max C1 C2, lt_max_of_lt_left hC1, fun rho hrho h hW => ⟨?_, ?_⟩⟩
  · intro N hN
    refine (h1 rho hrho h hW N hN).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _)
      (HRS.MS.S82P2.s82p2_deltaN_nonneg (by omega))
  · intro N hN p n hp hnp hrem pins i
    filter_upwards [h2 rho hrho h hW N hN p n hp hnp hrem pins i] with z hz
    refine hz.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (le_min zero_le_one ?_))
    have : 0 ≤ ∑ j, q (z - pins j) := Finset.sum_nonneg fun j _ => hq.nonneg _
    positivity

end HRS.MS.Phase2S82

end
