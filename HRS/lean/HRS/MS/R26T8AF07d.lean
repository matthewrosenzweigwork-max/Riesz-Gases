import HRS.MS.R26T8AF07c

/-!
# S8.2 observed-time layer, packet T8A.F07 (helper 07d): Sobolev bound of the Laplacian of a `SobSmooth` function

`sobolevNormE r (Δ u) ≤ d · sobolevNormE (r+2) u`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

theorem r26t8a_f07d_lap_sob {u : Euc d → ℝ} (hu : r26t8a_SobSmooth u) (r : ℝ) :
    sobolevNormE r (fun x => Laplacian.laplacian u x) ≤ (d : ℝ≥0∞) * sobolevNormE (r + 2) u := by
  have e : (fun x => Laplacian.laplacian u x) =
      fun x => ∑ i : Fin d, r26t8a_l3_D i (r26t8a_l3_D i u) x :=
    funext fun x => r26t8a_f07c_lap u hu.1 x
  rw [e]
  refine le_trans (r26t8a_f05c_sob_sum r Finset.univ fun i x => r26t8a_l3_D i (r26t8a_l3_D i u) x) ?_
  have hterm : ∀ i : Fin d, sobolevNormE r (r26t8a_l3_D i (r26t8a_l3_D i u)) ≤ sobolevNormE (r + 2) u := by
    intro i
    have h1 := r26t8a_l2 (r26t8a_l3_sob_D u hu i) i r
    have h2 := r26t8a_l2 hu i (r + 1)
    rw [show r + 1 + 1 = r + 2 by ring] at h2
    exact h1.trans h2
  calc ∑ i : Fin d, sobolevNormE r (fun x => r26t8a_l3_D i (r26t8a_l3_D i u) x)
      ≤ ∑ _i : Fin d, sobolevNormE (r + 2) u := Finset.sum_le_sum fun i _ => hterm i
    _ = (d : ℝ≥0∞) * sobolevNormE (r + 2) u := by
        simp [nsmul_eq_mul]

end HRS.MS.R26T8A

end
