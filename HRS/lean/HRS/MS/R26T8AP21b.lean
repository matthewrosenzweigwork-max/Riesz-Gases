import HRS.MS.R26T8AP21a
import Mathlib.Analysis.Calculus.TaylorIntegral

/-!
# S8.2 local Newton layer, packet T8A.P21 (part b): integral formula for `Q`
`Q(X,z) = (1/16) int_0^1 (1-t)^2 (u_4(t/2) + u_4(-t/2)) dt`, `u_n(tau) = D^n f(X + tau z)(z,...,z)` (symmetric Taylor remainder).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

def r26t8a_u (f : Euc d → ℝ) (X z : Euc d) (n : ℕ) (τ : ℝ) : ℝ :=
  iteratedFDeriv ℝ n f (X + τ • z) (fun _ => z)

theorem r26t8a_u_deriv {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (X z : Euc d) (n : ℕ) (τ : ℝ) :
    deriv (r26t8a_u f X z n) τ = r26t8a_u f X z (n + 1) τ :=
  ContDiffAt.deriv_fderiv_add_smul (hf.contDiffAt.of_le (by exact_mod_cast le_top))

theorem r26t8a_u_iteratedDeriv {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (X z : Euc d) (n : ℕ) :
    ∀ k : ℕ, iteratedDeriv k (r26t8a_u f X z n) = r26t8a_u f X z (n + k)
  | 0 => by simp [iteratedDeriv_zero]
  | k + 1 => by
    rw [iteratedDeriv_succ, r26t8a_u_iteratedDeriv hf X z n k]
    funext τ
    rw [r26t8a_u_deriv hf, add_assoc]

theorem r26t8a_u_contDiff {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (X z : Euc d) (n : ℕ) :
    ContDiff ℝ ∞ (r26t8a_u f X z n) := by
  unfold r26t8a_u
  have h1 : ContDiff ℝ ∞ (iteratedFDeriv ℝ n f) := hf.iteratedFDeriv_right (m := ∞) (by simp)
  have h2 : ContDiff ℝ ∞ (fun τ : ℝ => iteratedFDeriv ℝ n f (X + τ • z)) :=
    h1.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Euc d) ℝ (fun _ => z)).contDiff).comp h2

theorem r26t8a_u_one {f : Euc d → ℝ} (X z : Euc d) (τ : ℝ) :
    r26t8a_u f X z 1 τ = fderiv ℝ f (X + τ • z) z := by
  simp [r26t8a_u, iteratedFDeriv_one_apply]

theorem r26t8a_u_two_zero {f : Euc d → ℝ} (X z : Euc d) :
    r26t8a_u f X z 2 0 = fderiv ℝ (fderiv ℝ f) X z z := by
  simp [r26t8a_u, iteratedFDeriv_two_apply]

theorem r26t8a_taylor_half {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (X z : Euc d) (y : ℝ) :
    r26t8a_u f X z 1 y = r26t8a_u f X z 1 0 + y * r26t8a_u f X z 2 0 + (y ^ 2 / 2) * r26t8a_u f X z 3 0 +
      (1 / 2) * y ^ 3 * ∫ t in (0 : ℝ)..1, (1 - t) ^ 2 * r26t8a_u f X z 4 (t * y) := by
  have hψ : ContDiff ℝ ∞ (r26t8a_u f X z 1) := r26t8a_u_contDiff hf X z 1
  have h := map_add_eq_sum_add_integral_iteratedFDeriv (f := r26t8a_u f X z 1) (x := 0) (y := y) (n := 2)
    (fun t _ => (hψ.contDiffAt).of_le (by norm_cast))
  have hk : ∀ k : ℕ, ∀ x : ℝ, iteratedFDeriv ℝ k (r26t8a_u f X z 1) x (fun _ => y) =
      y ^ k * r26t8a_u f X z (1 + k) x := fun k x => by
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, r26t8a_u_iteratedDeriv hf]
    simp [smul_eq_mul]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, hk] at h
  rw [zero_add] at h
  simp only [Nat.factorial, Nat.cast_one, inv_one, smul_eq_mul, one_mul, pow_zero] at h
  have hI : (∫ t in (0 : ℝ)..1, (1 - t) ^ 2 * (y ^ (2 + 1) * r26t8a_u f X z (1 + (2 + 1)) (0 + t * y))) =
      y ^ 3 * ∫ t in (0 : ℝ)..1, (1 - t) ^ 2 * r26t8a_u f X z 4 (t * y) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    simp only [zero_add]
    norm_num
    ring
  rw [hI] at h
  norm_num at h
  linarith

theorem r26t8a_Q_integral {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (X z : Euc d) :
    r26t8a_Q f X z = (1 / 16 : ℝ) * ∫ t in (0 : ℝ)..1,
      (1 - t) ^ 2 * (r26t8a_u f X z 4 (t / 2) + r26t8a_u f X z 4 (-t / 2)) := by
  have hc : Continuous (r26t8a_u f X z 4) := (r26t8a_u_contDiff hf X z 4).continuous
  have hi1 : IntervalIntegrable (fun t : ℝ => (1 - t) ^ 2 * r26t8a_u f X z 4 (t * (1 / 2))) MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous fun t : ℝ => (1 - t) ^ 2 * r26t8a_u f X z 4 (t * (1 / 2))).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun t : ℝ => (1 - t) ^ 2 * r26t8a_u f X z 4 (t * (-1 / 2))) MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous fun t : ℝ => (1 - t) ^ 2 * r26t8a_u f X z 4 (t * (-1 / 2))).intervalIntegrable _ _
  have h1 := r26t8a_taylor_half hf X z (1 / 2)
  have h2 := r26t8a_taylor_half hf X z (-1 / 2)
  have e1 : (X - (1 / 2 : ℝ) • z) = X + (-1 / 2 : ℝ) • z := by module
  have e2 : r26t8a_Q f X z = r26t8a_u f X z 1 (1 / 2) - r26t8a_u f X z 1 (-1 / 2) - r26t8a_u f X z 2 0 := by
    unfold r26t8a_Q
    rw [r26t8a_u_one, r26t8a_u_one, r26t8a_u_two_zero, e1]
  have e3 : (∫ t in (0 : ℝ)..1, (1 - t) ^ 2 * (r26t8a_u f X z 4 (t / 2) + r26t8a_u f X z 4 (-t / 2))) =
      (∫ t in (0 : ℝ)..1, (1 - t) ^ 2 * r26t8a_u f X z 4 (t * (1 / 2))) +
        ∫ t in (0 : ℝ)..1, (1 - t) ^ 2 * r26t8a_u f X z 4 (t * (-1 / 2)) := by
    rw [← intervalIntegral.integral_add hi1 hi2]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    have a1 : t / 2 = t * (1 / 2) := by ring
    have a2 : -t / 2 = t * (-1 / 2) := by ring
    simp only [a1, a2]; ring
  rw [e2, e3, h1, h2]
  ring

end HRS.MS.R26T8A
