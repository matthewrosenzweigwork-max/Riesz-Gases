import HRS.MS.AdjRdNorms
import HRS.MS.UniqM1Fin

/-!
# S.A.12 P1: a finite uloc norm gives a measurable, locally `L²` function
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Assembly

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqM1

-- BEGIN SA12.P1
theorem uloc_local_l2 {d : ℕ} (hd : 1 ≤ d) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ)
    (m : ℕ) (u : Euc d → ℝ) (hu : ulocNormE m χ u<⊤) :
    AEStronglyMeasurable u volume ∧
      ∀ R : ℝ, 0<R → MemLp u 2 (volume.restrict (Metric.ball 0 R)) := by
  have h0 : ulocNormE 0 χ u < ⊤ :=
    lt_of_le_of_lt (HRS.MS.SA12BD.sa12_uloc_mono d m 0 (Nat.zero_le m) χ u) hu
  set B : ℝ := (ulocNormE 0 χ u).toReal with hB
  have hle : ulocNormE 0 χ u ≤ ENNReal.ofReal B := by
    rw [hB, ENNReal.ofReal_toReal h0.ne]
  have hfm := locMass_of_ulocNormE hχ ENNReal.toReal_nonneg hle
  refine ⟨hfm.1, fun R hR => ?_⟩
  obtain ⟨N, hN⟩ := exists_ball_sq_bound d R
  have hmeas : AEStronglyMeasurable u (volume.restrict (Metric.ball (0 : Euc d) R)) := hfm.1.restrict
  rw [memLp_iff]
  have hsq : eLpNorm u 2 (volume.restrict (Metric.ball (0 : Euc d) R)) ^ 2 < ⊤ := by
    rw [sq_eLpNorm_two hmeas]
    exact (hN B u hfm 0).trans_lt (ENNReal.mul_lt_top (ENNReal.natCast_lt_top N) ENNReal.ofReal_lt_top)
  by_contra hcon
  rw [not_lt, top_le_iff] at hcon
  rw [hcon] at hsq
  simp at hsq
-- END SA12.P1

end HRS.MH.AdjointRd.Phase2SA12Assembly
