import HRS.MS.Fp81S21WickB24

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open HRS (Euc)
open HRS.Whole

namespace HRS.Fp81.S21

/-- Symmetrizing coefficients leaves the half-Wick polynomial unchanged. -/
theorem fp81s21_wickB3_polynomial_symmCoeff
    {d m : ℕ} {μ : Measure (Euc d)} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P)
    (u : Fin m → Euc d → ℝ) (hu : ∀ i, MemLp (u i) 2 μ)
    (c : Fin m → Fin m → ℝ) :
    fp81s21_wickG_finite_rank_polynomial L u hu
        (fp81s21_wickB23_symmCoeff c) =
      fp81s21_wickG_finite_rank_polynomial L u hu c := by
  classical
  funext ω
  let Q : Fin m → Fin m → ℝ := fun i j =>
    (L ((hu i).toLp (u i))) ω * (L ((hu j).toLp (u j))) ω -
      ∫ ω', (L ((hu i).toLp (u i))) ω' * (L ((hu j).toLp (u j))) ω' ∂P
  have hQ : ∀ i j, Q i j = Q j i := by
    intro i j
    dsimp [Q]
    congr 1
    · exact mul_comm _ _
    · exact integral_congr_ae (ae_of_all _ fun ω' => mul_comm _ _)
  have htranspose : (∑ i, ∑ j, c j i * Q i j) =
      ∑ i, ∑ j, c i j * Q i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by rw [hQ j i]
  change (1 / 2 : ℝ) * (∑ i, ∑ j, ((c i j + c j i) / 2) * Q i j) =
    (1 / 2 : ℝ) * (∑ i, ∑ j, c i j * Q i j)
  have hsum : (∑ i, ∑ j, ((c i j + c j i) / 2) * Q i j) =
      (1 / 2 : ℝ) * ((∑ i, ∑ j, c i j * Q i j) +
        (∑ i, ∑ j, c j i * Q i j)) := by
    rw [mul_add]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum, htranspose]
  ring

#print axioms fp81s21_wickB3_polynomial_symmCoeff

end HRS.Fp81.S21
end
