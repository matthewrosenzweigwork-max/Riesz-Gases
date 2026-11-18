import HRS.MS.Fp81S21WindowSup23

/-!
# S2.1(iii), packet 9d: centered parameterized pair-energy measurability

This adapter turns the explicit moving pair-energy formula into measurability
of the compiled `pairEnergy`, then centers it under a sigma-finite particle
law. It leaves the orbit, density, and particle-path measurability inputs
explicit for the later specialization to the two-time quadratic field.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory

namespace HRS.Fp81.S21

open HRS.Whole
open scoped BigOperators

/-- A moving pair energy is measurable for any parameter space when its
reference density and kernel are jointly measurable. This is the compiled
`pairEnergy` statement, obtained from its explicit finite-sum formula. -/
theorem fp81s21_param_pairEnergy_joint_meas
    {S : Type} [MeasurableSpace S] {d N : ℕ}
    {ρ : S → Euc d → ℝ} {k : S → Euc d → Euc d → ℝ}
    (hρ : Measurable (fun q : S × Euc d => ρ q.1 q.2))
    (hρ0 : ∀ a x, 0 ≤ ρ a x)
    (hk : Measurable fun q : S × Euc d × Euc d => k q.1 q.2.1 q.2.2) :
    Measurable (fun q : S × EucConfig d N =>
      HRS.Whole.pairEnergy (k q.1) q.2
        (HRS.Whole.withDensityReal (ρ q.1))) := by
  rw [fp81s21_param_pairEnergy_eq_formula]
  exact fp81s21_param_pairEnergy_formula_joint_meas hρ hρ0 hk

#print axioms fp81s21_param_pairEnergy_joint_meas

end HRS.Fp81.S21

end
