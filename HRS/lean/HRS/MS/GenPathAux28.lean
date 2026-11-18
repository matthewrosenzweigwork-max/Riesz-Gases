import HRS.MS.GenPathAux27

/-!
# S5.6 packet P6c: the mild identity at a fixed time and Hermite coordinate
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.GenPath

open HRS.Whole HRS.MP.RdRem

variable {d : ℕ}

theorem s56_coord_ofMeasureDiff {m : ℝ} (hm : (d : ℝ) < m) (μ ν : Measure (Euc d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (α : MultiIndex d) :
    OscDual.coord (OscDual.ofMeasureDiff m μ ν) α =
      ∫ x, oscTestFun m α x ∂μ - ∫ x, oscTestFun m α x ∂ν := by
  rw [OscDual.coord_eq_mul, OscDual.hermiteCoeff_ofMeasureDiff hm]
  unfold HRS.Whole.measureHermiteCoeff oscTestFun
  rw [integral_const_mul, integral_const_mul]
  ring

theorem s56_sqrt_q (b : WholeBounds d) (S : WholeSetup b) {N : ℕ} (hN : 1 ≤ N) :
    Real.sqrt (2 * S.q N / N) = S.σ N * (Real.sqrt (2 * S.invβ N) / N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hσ : 0 ≤ S.σ N := by
    unfold WholeSetup.σ sigmaScale
    have := S.hκ N
    have := (S.hinvβ N).1
    split_ifs
    · exact (S.hκ N).le
    · exact le_min (S.hκ N).le (Real.sqrt_nonneg _)
  unfold WholeSetup.q qScale
  by_cases h0 : S.invβ N = 0
  · simp [h0]
  · simp only [h0, if_false]
    have hinv : 0 ≤ S.invβ N := (S.hinvβ N).1
    have : 2 * (S.σ N ^ 2 * S.invβ N / N) / N = (S.σ N / N) ^ 2 * (2 * S.invβ N) := by
      field_simp
    show Real.sqrt (2 * (S.σ N ^ 2 * S.invβ N / N) / N) = _
    rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    ring

end HRS.MS.GenPath
