import HRS.MS.SA12X2R36M

/-!
# S.A.12 R36 (SA12X2), part N: mollifier facts for the density approximation

Normed bumps `φ_n` (radius `1/(n+1)`, integral one, nonnegative, smooth, compactly supported) and the
mollified functions `x ↦ ∫ φ_n(x-y) g(y) dy`: uniform bound, smoothness, pointwise convergence.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12

variable {d : ℕ}

/-- The mollifier bump of radius `1/(n+1)`. -/
def sa12x2_bump (n : ℕ) : ContDiffBump (0 : Euc d) :=
  ⟨1 / ((n : ℝ) + 1) / 2, 1 / ((n : ℝ) + 1), by positivity, by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith⟩

/-- The normed mollifier `φ_n`. -/
def sa12x2_mol (n : ℕ) : Euc d → ℝ := (sa12x2_bump (d := d) n).normed volume

theorem sa12x2_mol_nonneg (n : ℕ) (x : Euc d) : 0 ≤ sa12x2_mol (d := d) n x :=
  (sa12x2_bump (d := d) n).nonneg_normed x

theorem sa12x2_mol_integral (n : ℕ) : ∫ x, sa12x2_mol (d := d) n x = 1 :=
  (sa12x2_bump (d := d) n).integral_normed

theorem sa12x2_mol_contDiff (n : ℕ) : ContDiff ℝ ∞ (sa12x2_mol (d := d) n) := by
  unfold sa12x2_mol
  exact (sa12x2_bump (d := d) n).contDiff.div_const _

theorem sa12x2_mol_hasCompactSupport (n : ℕ) : HasCompactSupport (sa12x2_mol (d := d) n) := by
  unfold sa12x2_mol
  have h := (sa12x2_bump (d := d) n).hasCompactSupport
  unfold ContDiffBump.normed
  simp only [div_eq_mul_inv]
  exact h.mul_right

theorem sa12x2_mol_tendsto_radius :
    Tendsto (fun n : ℕ => (sa12x2_bump (d := d) n).rOut) atTop (𝓝 0) := by
  have : (fun n : ℕ => (sa12x2_bump (d := d) n).rOut) = fun n : ℕ => 1 / ((n : ℝ) + 1) := rfl
  rw [this]
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- Convolution form with the kernel first, `∫ φ(x-y) g(y) dy = ∫ φ(t) g(x-t) dt`. -/
theorem sa12x2_conv_flip (φ g : Euc d → ℝ) (x : Euc d) :
    ∫ y, φ (x - y) * g y = ∫ t, φ t * g (x - t) := by
  have h := integral_sub_left_eq_self (μ := volume) (fun y => φ (x - y) * g y) x
  simp only [sub_sub_cancel] at h
  exact h.symm

/-- A bound for a mollified function. -/
theorem sa12x2_mol_bound {φ g : Euc d → ℝ} (hφ0 : ∀ t, 0 ≤ φ t) (hφ1 : ∫ t, φ t = 1)
    (hφi : Integrable φ) (hφc : HasCompactSupport φ)
    (hg : Continuous g) (B : ℝ) (hgB : ∀ y, |g y| ≤ B) (x : Euc d) :
    |∫ y, φ (x - y) * g y| ≤ B := by
  have hI : Integrable (fun y => φ (x - y)) := by
    have := hφi.comp_sub_left x
    exact this
  have hBnd : ∀ᵐ y ∂(volume : Measure (Euc d)), ‖φ (x - y) * g y‖ ≤ B * φ (x - y) := by
    refine Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hφ0 _)]
    calc φ (x - y) * |g y| ≤ φ (x - y) * B := mul_le_mul_of_nonneg_left (hgB y) (hφ0 _)
      _ = B * φ (x - y) := mul_comm _ _
  have hgi : Integrable (fun y => B * φ (x - y)) := hI.const_mul B
  have hint := norm_integral_le_of_norm_le hgi hBnd
  have hval : ∫ y, B * φ (x - y) = B := by
    rw [integral_const_mul, integral_sub_left_eq_self (μ := volume) φ x, hφ1, mul_one]
  rw [hval] at hint
  rwa [Real.norm_eq_abs] at hint

end HRS.MH.AdjointRd.Phase2SA12
