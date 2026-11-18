import HRS.MS.Fp81S21GaussG4U1
import HRS.MS.Fp81S21GaussG4U3

/-! The two G4 cost definitions coincide. -/
set_option autoImplicit false
noncomputable section
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3

theorem fp81s21_g4_cost_eq (d : ℕ) (f : Euc d → ℝ) :
    fp81s21_g4J d f = fp81s21_g4_J d f := rfl

#print axioms fp81s21_g4_cost_eq
end HRS.Fp81.S21
end
