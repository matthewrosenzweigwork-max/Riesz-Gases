import HRS.MS.SA12X2R36N
import HRS.MS.SA12X2R34

/-!
# S.A.12 R36 (SA12X2), part O: density approximation `a_n = φ_n ⋆ a` of a `C^(m+1)` density

For `a ∈ C^(m+1)_c` with bounded jets, `b_n = φ_n ⋆ a` is smooth, supported in `B̄(0,R+1)`, has uniformly
bounded tuple partials of order `≤ m+1`, and its tuple partials converge pointwise to those of `a`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12

open HRS HRS.Whole

variable {d : ℕ}

theorem sa12x2_mol_contDiff_conv {a : Euc d → ℝ} (ha : Continuous a) (n : ℕ) :
    ContDiff ℝ ∞ (fun x => ∫ y, sa12x2_mol (d := d) n (x - y) * a y) := by
  have h := (sa12x2_mol_hasCompactSupport (d := d) n).contDiff_convolution_left
    (ContinuousLinearMap.mul ℝ ℝ) (μ := (volume : Measure (Euc d))) (sa12x2_mol_contDiff (d := d) n)
    (ha.locallyIntegrable (μ := (volume : Measure (Euc d))))
  convert h using 1
  funext x
  rw [sa12x2_conv_flip, convolution_def]
  simp

theorem sa12x2_mol_tendsto {g : Euc d → ℝ} (hg : Continuous g) (x : Euc d) :
    Tendsto (fun n : ℕ => ∫ y, sa12x2_mol (d := d) n (x - y) * g y) atTop (𝓝 (g x)) := by
  have hT := ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume)
    (φ := fun n : ℕ => sa12x2_bump (d := d) n) (l := atTop) sa12x2_mol_tendsto_radius hg x
  refine Tendsto.congr (fun n => ?_) hT
  rw [sa12x2_conv_flip, convolution_def]
  simp [sa12x2_mol]

/-- A single evaluation of a tuple partial is bounded by the iterated derivative norm. -/
theorem sa12x2_pd_le_norm {j : ℕ} (f : Euc d → ℝ) (idx : Fin j → Fin d) (x : Euc d) :
    |partialDeriv idx f x| ≤ ‖iteratedFDeriv ℝ j f x‖ := by
  have h1 := (iteratedFDeriv ℝ j f x).le_opNorm (fun l => EuclideanSpace.single (idx l) (1 : ℝ))
  have h2 : ∏ l, ‖(EuclideanSpace.single (idx l) (1 : ℝ) : Euc d)‖ = 1 := by
    simp [PiLp.norm_single]
  rw [h2, mul_one] at h1
  rw [← Real.norm_eq_abs]
  exact h1

end HRS.MH.AdjointRd.Phase2SA12
