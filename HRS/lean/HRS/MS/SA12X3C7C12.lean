import HRS.MS.SA12X3C7C11

/-!
# S.A.12 C7 (SA12X3), part C12 (7C): the cell masses of a function with bounded jets are uniformly bounded
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MH.AdjointRd

variable {d : ℕ}

theorem sa12x3_mass_bdd {Ψ : ℝ → Euc d → Euc d} {τ : ℝ} {Lp : ℝ} (hL : ∀ x y, ‖Ψ τ x - Ψ τ y‖ ≤ Lp * ‖x - y‖)
    (hLp : 0 ≤ Lp) (hΨ : Continuous (Ψ τ)) {m : ℕ} {F : Euc d → ℝ} (hF : BddJets m F) :
    ∃ Mbar : ℝ, ∀ z : Fin d → ℤ, cellMass m Ψ τ z F ≤ Mbar := by
  have hB : ∀ j : ℕ, ∀ idx : Fin j → Fin d, ∃ B : ℝ, 0 ≤ B ∧ (j ≤ m → ∀ x, |partialDeriv idx F x| ≤ B) := by
    intro j idx
    by_cases hj : j ≤ m
    · obtain ⟨B, hB⟩ := hF.2 j hj idx
      exact ⟨max B 0, le_max_right _ _, fun _ x => (hB x).trans (le_max_left _ _)⟩
    · exact ⟨0, le_rfl, fun h => absurd h hj⟩
  choose B hB0 hBb using hB
  set V0 : ℝ := (volume (closedBall (0 : Euc d) (Lp * Real.sqrt d))).toReal with hV0
  refine ⟨∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d, B j idx ^ 2 * V0, ?_⟩
  intro z
  unfold cellMass
  refine Finset.sum_le_sum fun j hj => ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.1 hj)
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun idx _ => ?_) (Nat.cast_nonneg _)
  have hcpt : IsCompact (flowCell Ψ τ z) := sa12x3_flowCell_compact hΨ z
  have hvol : (volume (flowCell Ψ τ z)).toReal ≤ V0 :=
    ENNReal.toReal_mono (measure_closedBall_lt_top).ne (sa12x3_flowCell_vol hL hLp z)
  have hpdc : Continuous (fun x => partialDeriv idx F x ^ 2) :=
    ((sa12z3_pd_contDiff_inf hF.1 idx).continuous).pow 2
  calc ∫ x in flowCell Ψ τ z, partialDeriv idx F x ^ 2 ≤ ∫ x in flowCell Ψ τ z, B j idx ^ 2 := by
        refine setIntegral_mono_on (hpdc.continuousOn.integrableOn_compact hcpt)
          (integrableOn_const hcpt.measure_lt_top.ne) hcpt.isClosed.measurableSet fun x _ => ?_
        have := hBb j idx hjm x
        nlinarith [abs_nonneg (partialDeriv idx F x), sq_abs (partialDeriv idx F x), hB0 j idx]
    _ = B j idx ^ 2 * (volume (flowCell Ψ τ z)).toReal := by
        rw [setIntegral_const]; simp [Measure.real, mul_comm]
    _ ≤ B j idx ^ 2 * V0 := mul_le_mul_of_nonneg_left hvol (sq_nonneg _)

end HRS.MH.AdjointRd.Phase2SA12Near
