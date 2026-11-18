import HRS.MS.Fp81S21WindowSup15

/-!
# S2.1(iii), packet 9d: pair-energy normalization

The source definitions are `HRS.Whole.pairEnergy` (the ordered off-diagonal
sum with coefficients `1/(2N²)`, `-1/N`, and `1/2`) and
`HRS.MS.S53.s53_Dk` (the `centeredPairFunctional` of the commutator kernel).
Thus the pair-energy observable is one half of `s53_Dk`; both background
integrals are included in this identity.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open HRS HRS.Whole HRS.Whole.AppendixA

namespace HRS.Fp81.S21

/-- The quadratic pair energy for the commutator kernel is one half of the
S5.3 centered pair functional. -/
theorem fp81s21_pairEnergy_eq_half_s53_Dk
    {d N : ℕ} (s : ℝ) (ρ : Euc d → ℝ) (f : Euc d → ℝ)
    (X : EucConfig d N) :
    HRS.Whole.pairEnergy
        (HRS.Whole.commutatorKernel d s (fun x => gradient f x)) X
        (HRS.Whole.withDensityReal ρ) =
      (1 / 2 : ℝ) * HRS.MS.S53.s53_Dk s ρ f X := by
  unfold HRS.Whole.pairEnergy HRS.MS.S53.s53_Dk
    HRS.Whole.centeredPairFunctional
  ring

#print axioms fp81s21_pairEnergy_eq_half_s53_Dk

end HRS.Fp81.S21

end
