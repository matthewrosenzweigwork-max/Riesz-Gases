import HRS.MS.Fp81S21InitialFR

open MeasureTheory
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3

/-- The centered quadratic limit associated with the actual initial response
coefficients. The factor `1 / 2` is part of the definition. -/
def fp81s21_initial_Blimit {p : Parameters} {δ : ℝ}
    (R : Trajectory p δ) (φ : ℕ → Euc p.d → ℝ)
    (G : Measure SeqL2) (ψ : SeqL2 → ℝ)
    (h : Euc p.d → Euc p.d → ℝ) : ℝ :=
  (1 / 2) * ∑' l, ∑' q,
    fp81s21_initial_Qk R φ h l q *
      ∫ z, S99.pd (S99.pd ψ l) q z ∂G

/-- Coordinate-generic three-term comparison for the actual-law quadratic
statistic. The hypotheses separately record the finite-cover error, the
finite-rank rate, and the response-coefficient error. -/
theorem fp81s21_initial_Bkernel_three_term
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (φ : ℕ → Euc p.d → ℝ) (N : ℕ)
    (h D : Euc p.d → Euc p.d → ℝ) (G : Measure SeqL2)
    (ψ : SeqL2 → ℝ) (εA εB εC : ℝ)
    (hA : |fp81s21_initial_Bterm R φ N h ψ -
        fp81s21_initial_Bterm R φ N D ψ| ≤ εA)
    (hB : |fp81s21_initial_Bterm R φ N D ψ -
        fp81s21_initial_Blimit R φ G ψ D| ≤ εB)
    (hC : |fp81s21_initial_Blimit R φ G ψ D -
        fp81s21_initial_Blimit R φ G ψ h| ≤ εC) :
    |fp81s21_initial_Bterm R φ N h ψ -
      fp81s21_initial_Blimit R φ G ψ h| ≤ εA + εB + εC := by
  have hdecomp :
      fp81s21_initial_Bterm R φ N h ψ -
          fp81s21_initial_Blimit R φ G ψ h =
        (fp81s21_initial_Bterm R φ N h ψ -
            fp81s21_initial_Bterm R φ N D ψ) +
          (fp81s21_initial_Bterm R φ N D ψ -
            fp81s21_initial_Blimit R φ G ψ D) +
          (fp81s21_initial_Blimit R φ G ψ D -
            fp81s21_initial_Blimit R φ G ψ h) := by ring
  rw [hdecomp]
  calc
    |(fp81s21_initial_Bterm R φ N h ψ -
          fp81s21_initial_Bterm R φ N D ψ) +
        (fp81s21_initial_Bterm R φ N D ψ -
          fp81s21_initial_Blimit R φ G ψ D) +
        (fp81s21_initial_Blimit R φ G ψ D -
          fp81s21_initial_Blimit R φ G ψ h)|
        ≤ |(fp81s21_initial_Bterm R φ N h ψ -
            fp81s21_initial_Bterm R φ N D ψ) +
            (fp81s21_initial_Bterm R φ N D ψ -
              fp81s21_initial_Blimit R φ G ψ D)| +
              |fp81s21_initial_Blimit R φ G ψ D -
                fp81s21_initial_Blimit R φ G ψ h| := abs_add_le _ _
    _ ≤ |fp81s21_initial_Bterm R φ N h ψ -
          fp81s21_initial_Bterm R φ N D ψ| +
        |fp81s21_initial_Bterm R φ N D ψ -
          fp81s21_initial_Blimit R φ G ψ D| +
        |fp81s21_initial_Blimit R φ G ψ D -
          fp81s21_initial_Blimit R φ G ψ h| := by
        gcongr
        exact abs_add_le _ _
    _ ≤ εA + εB + εC := by linarith

#print axioms fp81s21_initial_Bkernel_three_term

end HRS.Fp81.S21

end
