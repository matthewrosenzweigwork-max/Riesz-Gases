import HRS.MS.Fp81S21FutureIndep5
import HRS.MS.Fp81S21PropagatorOsc
import HRS.MS.S111X2Aux21

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.R26T3

/-- Composition of the moving adjoint propagator on an oscillator datum. The
intermediate datum is the actual propagated test, not an oscillator assumption. -/
theorem fp81s21_moving_propagator_comp
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {v r t : ℝ} (hv : 0 ≤ v) (hvr : v ≤ r) (hrt : r ≤ t)
    {φ : Euc p.d → ℝ} (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ) :
    propagatorW (r26t3_coeff R) v r (propagatorW (r26t3_coeff R) r t φ) =
      propagatorW (r26t3_coeff R) v t φ := by
  have hr : 0 ≤ r := hv.trans hvr
  have ht : 0 ≤ t := hr.trans hrt
  have hcl := fp81s21_U_osc_test_classical p R hφ ht
  have hrestrict := HRS.MS.S111X2.s111x2_cls_restrict hcl hr hrt
  have hsd : p.s < (p.d : ℝ) := by
    have hdreal : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    nlinarith [p.hs]
  have hu := HRS.MS.S104e.s104e_unique p.hd p.hs0 hsd p.ha p.hβ
    δ p.c₁ p.C₁ R.thermal R.admissible R.resulting t ht ⟨hr, hrt⟩ hrestrict
  simpa only [r26t3_U, r26t3_coeff] using hu v ⟨hv, hvr⟩

#print axioms fp81s21_moving_propagator_comp

end HRS.Fp81.S21
end
