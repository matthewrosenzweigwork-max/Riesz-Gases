import HRS.MS.Fp81S21WindowFeature9
import HRS.MS.FcauTie

/-!
# S2.1 packet 15c: scalar orbit decay conversion

This packages the finite-order conversion from a decaying gradient estimate to
the positive spatial derivatives of a propagated scalar terminal input.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole

variable {d : ℕ}

/-- A C_b bound on the gradient of every classical adjoint yields the same
positive-order scalar derivative bound for its propagated terminal input. -/
theorem fp81s21_scalar_orbit_pos_of_gradient_decay
    {C : WholeCoeff d} {T v X : ℝ} {ψ : Euc d → ℝ} {K k : ℕ}
    (hex : ∃ f, IsClassicalAdjointW C T ψ f)
    (hv : v ∈ Icc (0 : ℝ) T)
    (hdecay : ∀ f : ℝ → Euc d → ℝ,
      IsClassicalAdjointW C T ψ f →
        ContDiff ℝ (K : WithTop ℕ∞) (fun x => gradient (f v) x) ∧
        cbNormVecE K (fun x => gradient (f v) x) ≤ ENNReal.ofReal X)
    (hX : 0 ≤ X) (hk : 1 ≤ k) (hkK : k ≤ K + 1) :
    ∀ x, ‖iteratedFDeriv ℝ k (propagatorW C v T ψ) x‖ ≤ X := by
  let fcan : ℝ → Euc d → ℝ := fun r => propagatorW C r T ψ
  have hcan : IsClassicalAdjointW C T ψ fcan := by
    simpa [fcan] using HRS.MS.Fcau.propagatorW_isClassical hex
  have hregular : ContDiff ℝ 1 (propagatorW C v T ψ) := by
    have h := hcan.c2 v hv
    exact h.of_le (by norm_num)
  have hgrad : ContDiff ℝ (K : WithTop ℕ∞)
      (fun x => gradient (propagatorW C v T ψ) x) := by
    simpa [fcan] using (hdecay fcan hcan).1
  have hbound : cbNormVecE K
      (fun x => gradient (propagatorW C v T ψ) x) ≤ ENNReal.ofReal X := by
    simpa [fcan] using (hdecay fcan hcan).2
  exact (fp81s21_scalar_pos_deriv_of_gradient_cb hregular hgrad hbound hX hk hkK).2

#print axioms fp81s21_scalar_orbit_pos_of_gradient_decay

end HRS.Fp81.S21

end
