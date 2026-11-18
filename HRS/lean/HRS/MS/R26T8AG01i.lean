import HRS.MS.R26T8AG01h
import HRS.MS.R26T8AG01f

/-!
# S8.2 observed-time layer, packet T8A.G01 (helper i): factor-level derivative bounds for the graph cutoff

With `m = n + 1`, the spatial factor `s_i X = 1 - ψ(m⁻² ‖X i‖²)` and the pair factor `f_ij X = ψ(m² ‖X i - X j‖²)`
have derivative bounds uniform in `n` (spatial) and in terms of `1/‖X i - X j‖` (pair, off the collision set).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

/-- uniform spatial factor bounds -/
theorem r26t8a_g01i_spatial {d N : ℕ} {K1 K2 : ℝ}
    (hK1 : ∀ t : ℝ, |deriv r26t8a_g01a_psi t| ≤ K1) (hK2 : ∀ t : ℝ, |deriv (deriv r26t8a_g01a_psi) t| ≤ K2)
    (hK1n : 0 ≤ K1) (hK2n : 0 ≤ K2) (n : ℕ) (i : Fin N) (X : EucConfig d N) :
    ‖iteratedFDeriv ℝ 1 (fun y : EucConfig d N => 1 - r26t8a_g01a_psi (((n : ℝ) + 1)⁻¹ ^ 2 * ‖y i‖ ^ 2)) X‖
        ≤ 8 * K1 * ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i‖ ∧
      ‖iteratedFDeriv ℝ 2 (fun y : EucConfig d N => 1 - r26t8a_g01a_psi (((n : ℝ) + 1)⁻¹ ^ 2 * ‖y i‖ ^ 2)) X‖
        ≤ (8 * K1 + 64 * K2) * ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i‖ ^ 2 := by
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hm : 1 ≤ (n : ℝ) + 1 := by linarith
  exact r26t8a_g01f_spatial r26t8a_g01a_psi r26t8a_g01a_contDiff
    (fun t ht => r26t8a_g01a_deriv_zero ht)
    hK1 hK2 hK1n hK2n hm (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i) X

/-- off the collision set, the pair factor is controlled by the inverse distance -/
theorem r26t8a_g01i_pair {d N : ℕ} {K1 K2 : ℝ}
    (hK1 : ∀ t : ℝ, |deriv r26t8a_g01a_psi t| ≤ K1) (hK2 : ∀ t : ℝ, |deriv (deriv r26t8a_g01a_psi) t| ≤ K2)
    (hK1n : 0 ≤ K1) (hK2n : 0 ≤ K2) (n : ℕ) (i j : Fin N) (X : EucConfig d N) :
    ‖iteratedFDeriv ℝ 1 (fun y : EucConfig d N => r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖y i - y j‖ ^ 2)) X‖
        ≤ 8 * K1 * ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i -
            ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) j‖ / ‖X i - X j‖ ∧
      ‖iteratedFDeriv ℝ 2 (fun y : EucConfig d N => r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖y i - y j‖ ^ 2)) X‖
        ≤ (8 * K1 + 64 * K2) * ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i -
            ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) j‖ ^ 2 / ‖X i - X j‖ ^ 2 := by
  have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  exact r26t8a_g01e_pair r26t8a_g01a_psi r26t8a_g01a_contDiff (fun t ht => r26t8a_g01a_deriv_zero ht)
    hK1 hK2 hK1n hK2n (m := (n : ℝ) + 1)
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i -
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) j) X

end HRS.MS.R26T8A

end
