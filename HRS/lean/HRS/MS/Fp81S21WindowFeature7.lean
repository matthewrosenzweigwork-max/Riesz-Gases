import HRS.MS.Fp81S21WindowFeature6
import HRS.MS.R26T8AF13b
import HRS.MS.R2WinErrAux11

/-!
# S2.1 packet 15c: scalar derivative bounds from moving gradient orbits

The orbit theorem controls all derivatives of the gradient.  This finite-order
conversion gives the corresponding positive-order bounds for the scalar orbit.
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

/-- A finite-order gradient bound controls positive scalar derivatives, and
the gradient regularity upgrades the scalar function by one order. -/
theorem fp81s21_scalar_pos_deriv_of_gradient_cb
    {g : Euc d → ℝ} {K k : ℕ} {X : ℝ}
    (hg : ContDiff ℝ 1 g)
    (hgrad : ContDiff ℝ (K : WithTop ℕ∞) (fun x => gradient g x))
    (hcb : cbNormVecE K (fun x => gradient g x) ≤ ENNReal.ofReal X)
    (hX : 0 ≤ X) (hk : 1 ≤ k) (hkK : k ≤ K + 1) :
    ContDiff ℝ ((K + 1 : ℕ) : WithTop ℕ∞) g ∧
      ∀ x, ‖iteratedFDeriv ℝ k g x‖ ≤ X := by
  let L : Euc d →L[ℝ] StrongDual ℝ (Euc d) :=
    (InnerProductSpace.toDual ℝ (Euc d)).toContinuousLinearEquiv.toContinuousLinearMap
  have hfd : ContDiff ℝ (K : WithTop ℕ∞) (fderiv ℝ g) := by
    have he : (fderiv ℝ g) = L ∘ (fun x => gradient g x) := by
      funext x
      simp [L, gradient]
    rw [he]
    exact L.contDiff.comp hgrad
  have hdiff : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hder : ∀ x, HasFDerivAt g (fderiv ℝ g x) x := by
    intro x
    exact (hdiff x).hasFDerivAt
  have hreg : ContDiff ℝ ((K + 1 : ℕ) : WithTop ℕ∞) g :=
    contDiff_succ_iff_hasFDerivAt.2 ⟨fderiv ℝ g, hfd, hder⟩
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hnK : n ≤ K := by omega
  have hgradnorm : ∀ x, ‖iteratedFDeriv ℝ n (fun y => gradient g y) x‖ ≤ X := by
    intro x
    exact HRS.MS.R2WinErr.s104_cbNormVecE_le hX hcb n hnK x
  have hL : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    simp [L]
  have he : (fderiv ℝ g) = L ∘ (fun x => gradient g x) := by
    funext x
    simp [L, gradient]
  refine ⟨hreg, fun x => ?_⟩
  rw [← norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := g) (x := x) (n := n), he]
  rw [ContinuousLinearMap.iteratedFDeriv_comp_left L hgrad.contDiffAt
    (i := n) (by exact_mod_cast hnK)]
  calc
    ‖L.compContinuousMultilinearMap (iteratedFDeriv ℝ n (fun y => gradient g y) x)‖
        ≤ ‖L‖ * ‖iteratedFDeriv ℝ n (fun y => gradient g y) x‖ :=
          ContinuousLinearMap.norm_compContinuousMultilinearMap_le L _
    _ ≤ 1 * X := mul_le_mul hL (hgradnorm x) (norm_nonneg _) (by norm_num)
    _ = X := one_mul _

#print axioms fp81s21_scalar_pos_deriv_of_gradient_cb

end HRS.Fp81.S21

end
