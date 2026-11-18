import HRS.MS.Fp81S21WindowFeature8
import HRS.MS.R2WinOrbAux1
import HRS.MS.R2WinErrAux15

/-!
# S2.1 packet 15c: scalar bounds used by the moving window estimate

This file records the scalar extraction from the C_b envelope of an
oscillator terminal test.  Moving-orbit gradient bounds are converted by the
finite-order bridge in `Fp81S21WindowFeature7`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.R2WinOrb HRS.MS.R2WinErr

variable {d : ℕ}

/-- Each pointwise iterated derivative is bounded by the scalar `C_b` norm. -/
theorem fp81s21_scalar_cbNorm_pointwise
    {K : ℕ} {g : Euc d → ℝ} {B : ℝ} (hg : MemCb K g)
    (hcb : cbNorm K g ≤  B) :
    ∀ j ≤ K, ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ B := by
  intro j hj x
  have hbd := hg.2 j hj
  have h1 : ‖iteratedFDeriv ℝ j g x‖ ≤ ⨆ y, ‖iteratedFDeriv ℝ j g y‖ :=
    le_ciSup hbd x
  calc
    _ ≤ ⨆ y, ‖iteratedFDeriv ℝ j g y‖ := h1
    _ ≤ cbNorm K g := by
      unfold HRS.cbNorm
      exact Finset.single_le_sum
        (f := fun i => ⨆ y, ‖iteratedFDeriv ℝ i g y‖)
        (fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _)
        (Finset.mem_range.2 (by omega))
    _ ≤ B := hcb

/-- The standard oscillator tests admit a summable scalar derivative
envelope through every order used by the window feature. -/
theorem fp81s21_window_test_pos_envelope (hd : 1 ≤ d) :
    ∃ Kφ : ℝ, 0 ≤ Kφ ∧
      ∀ α : MultiIndex d, ∀ j ≤ 4 * d + 42, ∀ x,
        ‖iteratedFDeriv ℝ j
          (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α) x‖ ≤
            Kφ * s104_b d α := by
  obtain ⟨Kφ, hKφ, htest⟩ := s103_phi_cb hd
  refine ⟨Kφ, hKφ, ?_⟩
  intro α j hj x
  have hpoint := fp81s21_scalar_cbNorm_pointwise (htest α).1 (htest α).2 j hj x
  simpa [s103_b, s104_b, wholeSpaceIndex] using hpoint

#print axioms fp81s21_scalar_cbNorm_pointwise
#print axioms fp81s21_window_test_pos_envelope

end HRS.Fp81.S21

end
