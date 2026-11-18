import HRS.MS.Fp81S21PredMap2

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical Set
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.R2Interp HRS.MS.CovMeas
  HRS.MS.FixEq

/-- A weighted-continuous physical functional agrees with the chart action
on every normalized propagated oscillator test, with the orbit bound. -/
theorem fp81s21_chartAction_propagated_test
    {d r : ℕ} {Pw : ℝ} {C : WholeCoeff d} {m T : ℝ}
    {c : MultiIndex d → ℝ} (hP : (d : ℝ) < 2 * Pw)
    (hD : S101Data C m T r c) (E : r26t6_WeightedChart d r Pw)
    (z : r26t6_Coeff) (Q : (Euc d → ℝ) → ℝ) (hQ : S102Z r Pw Q)
    (hagree : ∀ f, IsR2Test f → fp81s21_chartAction E z f = Q f)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T) {t : ℝ} (ht : t ∈ Icc u T)
    (α : MultiIndex d) :
    fp81s21_chartAction E z (propagatorW C u t (oscTestFun m α)) =
        Q (propagatorW C u t (oscTestFun m α)) ∧
      |Q (propagatorW C u t (oscTestFun m α))| ≤
        ‖z‖ * (s57pC d r Pw * c α) := by
  obtain ⟨htest, hnorm⟩ := s102_orbit_test hP hD hu ht α
  have heq := fp81s21_chartAction_eq_of_compact_agreement hP E z Q hQ hagree _ htest
  refine ⟨heq, ?_⟩
  rw [← heq]
  exact (fp81s21_chartAction_weighted_bound E z _ htest).trans
    (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))

#print axioms HRS.Fp81.S21.fp81s21_chartAction_propagated_test

end HRS.Fp81.S21
