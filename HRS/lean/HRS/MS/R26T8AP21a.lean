import HRS.MS.SuppU2Aux1
import HRS.MS.R26T8AP00

/-!
# S8.2 local Newton layer, packet T8A.P21 (part a): the leading source as `k(z) * Q(X,z)`
For `z != 0`: `midPair (lead f) X z = -(s/2) |z|^(-s-2) * Q(X,z)`, `Q(X,z) = Df(X+z/2) z - Df(X-z/2) z - D^2 f(X)(z,z)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

def r26t8a_Q (f : Euc d → ℝ) (X z : Euc d) : ℝ :=
  fderiv ℝ f (X + (1 / 2 : ℝ) • z) z - fderiv ℝ f (X - (1 / 2 : ℝ) • z) z - fderiv ℝ (fderiv ℝ f) X z z

def r26t8a_kz (d : ℕ) (z : Euc d) : ℝ := -(criticalS d / 2) * ‖z‖ ^ (-criticalS d - 2)

def r26t8a_lead (f : Euc d → ℝ) : Euc d → Euc d → ℝ := fun x y =>
  (1 / 2 : ℝ) * hSource f x y + (criticalS d / 2) * ‖x - y‖ ^ (-criticalS d) *
    (fderiv ℝ (fderiv ℝ f) ((1 / 2 : ℝ) • (x + y))) (‖x - y‖⁻¹ • (x - y)) (‖x - y‖⁻¹ • (x - y))

theorem r26t8a_lead_mid (hd : 1 ≤ d) (f : Euc d → ℝ) (X : Euc d) {z : Euc d} (hz : z ≠ 0) :
    midPair (r26t8a_lead f) X z = r26t8a_kz d z * r26t8a_Q f X z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hs : criticalS d ≠ 0 := by
    unfold criticalS
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  have h1 : (X + (1 / 2 : ℝ) • z) - (X - (1 / 2 : ℝ) • z) = z := by module
  have h2 : (1 / 2 : ℝ) • ((X + (1 / 2 : ℝ) • z) + (X - (1 / 2 : ℝ) • z)) = X := by module
  have hrk := u2_rieszKernelGrad_eq (d := d) (criticalS d) hz
  have hinner : ∀ (a : Euc d) (v : Euc d), inner ℝ (gradient f a) v = fderiv ℝ f a v := fun a v => by
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  have hpow : (‖z‖ ^ 2) ^ (-criticalS d / 2 - 1) = ‖z‖ ^ (-criticalS d - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    congr 1; push_cast; ring
  have hpow2 : ‖z‖ ^ (-criticalS d - 2) = ‖z‖ ^ (-criticalS d) * (‖z‖⁻¹ * ‖z‖⁻¹) := by
    rw [Real.rpow_sub hn, Real.rpow_two]; field_simp
  unfold midPair r26t8a_lead r26t8a_kz r26t8a_Q hSource commutatorKernel
  simp only [h1, h2]
  rw [hrk, u2_sigma, if_neg hs, real_inner_smul_right, inner_sub_left, hinner, hinner, hpow]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hpow2]
  ring

end HRS.MS.R26T8A
