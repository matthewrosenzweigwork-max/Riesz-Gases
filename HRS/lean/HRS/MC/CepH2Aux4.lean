import HRS.MC.CepH2Aux3
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# CEPH2, helper 4: the Gaussian on `Ch N`

`h2_g v` is the centred Gaussian density with variance `v` per coordinate.  Integral `1`, second moment `N v`,
gradient and Hessian, and polynomially weighted bounds by `exp(-‖w‖²/(4v))`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ}

/-- The Gaussian density of variance `v` per coordinate. -/
def h2_g (v : ℝ) (w : Ch N) : ℝ :=
  (2 * Real.pi * v) ^ (-(N : ℝ) / 2) * Real.exp (-(1 / (2 * v)) * ‖w‖ ^ 2)

theorem h2_g_pos {v : ℝ} (hv : 0 < v) (w : Ch N) : 0 < h2_g v w := by
  unfold h2_g
  have : 0 < 2 * Real.pi * v := by positivity
  positivity

theorem h2_g_nonneg {v : ℝ} (hv : 0 < v) (w : Ch N) : 0 ≤ h2_g v w := (h2_g_pos hv w).le

theorem h2_continuous_g (v : ℝ) : Continuous (h2_g (N := N) v) := by
  unfold h2_g; fun_prop

theorem h2_gauss_integral {b : ℝ} (hb : 0 < b) :
    ∫ w : Ch N, Real.exp (-b * ‖w‖ ^ 2) = (Real.pi / b) ^ ((N : ℝ) / 2) := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb]
  simp [finrank_euclideanSpace_fin]

theorem h2_integrable_gauss {b : ℝ} (hb : 0 < b) : Integrable (fun w : Ch N => Real.exp (-b * ‖w‖ ^ 2)) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [h2_gauss_integral hb]
  have : 0 < Real.pi / b := by positivity
  exact (Real.rpow_pos_of_pos this _).ne'

theorem h2_g_integral {v : ℝ} (hv : 0 < v) : ∫ w : Ch N, h2_g v w = 1 := by
  unfold h2_g
  rw [integral_const_mul, h2_gauss_integral (by positivity : 0 < 1 / (2 * v))]
  have h1 : Real.pi / (1 / (2 * v)) = 2 * Real.pi * v := by field_simp
  rw [h1, ← Real.rpow_add (by positivity)]
  have : -(N : ℝ) / 2 + (N : ℝ) / 2 = 0 := by ring
  rw [this, Real.rpow_zero]

theorem h2_integrable_g {v : ℝ} (hv : 0 < v) : Integrable (h2_g (N := N) v) := by
  unfold h2_g
  exact (h2_integrable_gauss (by positivity : 0 < 1 / (2 * v))).const_mul _

/-- `r² e^{-b r²} ≤ (2/b) e^{-(b/2) r²}`. -/
theorem h2_sq_exp_le {b : ℝ} (hb : 0 < b) (r : ℝ) :
    r ^ 2 * Real.exp (-b * r ^ 2) ≤ (2 / b) * Real.exp (-(b / 2) * r ^ 2) := by
  have h1 : (b / 2) * r ^ 2 ≤ Real.exp ((b / 2) * r ^ 2) := by
    have := Real.add_one_le_exp ((b / 2) * r ^ 2); linarith
  have h2 : Real.exp (-b * r ^ 2) = Real.exp (-(b / 2) * r ^ 2) * Real.exp (-(b / 2) * r ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 : Real.exp (-(b / 2) * r ^ 2) * Real.exp ((b / 2) * r ^ 2) = 1 := by
    rw [← Real.exp_add]; simp
  have h4 : 0 < Real.exp (-(b / 2) * r ^ 2) := Real.exp_pos _
  calc r ^ 2 * Real.exp (-b * r ^ 2)
      = (2 / b) * (((b / 2) * r ^ 2) * Real.exp (-(b / 2) * r ^ 2)) * Real.exp (-(b / 2) * r ^ 2) := by
        rw [h2]; field_simp
    _ ≤ (2 / b) * (Real.exp ((b / 2) * r ^ 2) * Real.exp (-(b / 2) * r ^ 2)) * Real.exp (-(b / 2) * r ^ 2) := by
        gcongr
    _ = (2 / b) * Real.exp (-(b / 2) * r ^ 2) := by
        rw [mul_comm (Real.exp _) (Real.exp _), h3]; ring

theorem h2_integrable_sq_gauss {b : ℝ} (hb : 0 < b) :
    Integrable (fun w : Ch N => ‖w‖ ^ 2 * Real.exp (-b * ‖w‖ ^ 2)) := by
  refine Integrable.mono' ((h2_integrable_gauss (by positivity : 0 < b / 2)).const_mul (2 / b))
    (by fun_prop) (ae_of_all _ fun w => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact h2_sq_exp_le hb ‖w‖

theorem h2_gauss_second {b : ℝ} (hb : 0 < b) :
    ∫ w : Ch N, ‖w‖ ^ 2 * Real.exp (-b * ‖w‖ ^ 2) = ((N : ℝ) / (2 * b)) * (Real.pi / b) ^ ((N : ℝ) / 2) := by
  set x : ℝ := (N : ℝ) / 2 with hx
  have hint := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (Ch N))) (𝕜 := ℝ)
    (F := fun (b : ℝ) (w : Ch N) => Real.exp (-b * ‖w‖ ^ 2)) (x₀ := b) (s := Set.Ioo (b / 2) (2 * b))
    (bound := fun w => ‖w‖ ^ 2 * Real.exp (-(b / 2) * ‖w‖ ^ 2))
    (F' := fun (b : ℝ) (w : Ch N) => -(‖w‖ ^ 2 * Real.exp (-b * ‖w‖ ^ 2)))
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun b' => by fun_prop) (h2_integrable_gauss hb)
    (by fun_prop) (ae_of_all _ fun w b' hb' => by
      rw [norm_neg, Real.norm_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
      have := hb'.1
      nlinarith [sq_nonneg ‖w‖])
    (h2_integrable_sq_gauss (by positivity : 0 < b / 2))
    (ae_of_all _ fun w b' _ => by
      have h1 : HasDerivAt (fun b' : ℝ => -b' * ‖w‖ ^ 2) (-‖w‖ ^ 2) b' := by
        simpa using (hasDerivAt_id b').neg.mul_const (‖w‖ ^ 2)
      have := h1.exp
      convert this using 1
      ring)
  have hΦ : HasDerivAt (fun b' : ℝ => (Real.pi) ^ x * b' ^ (-x)) ((Real.pi) ^ x * (-x * b ^ (-x - 1))) b := by
    have := Real.hasDerivAt_rpow_const (x := b) (p := -x) (Or.inl hb.ne')
    exact this.const_mul _
  have hev : (fun b' : ℝ => ∫ w : Ch N, Real.exp (-b' * ‖w‖ ^ 2)) =ᶠ[𝓝 b] fun b' => (Real.pi) ^ x * b' ^ (-x) := by
    filter_upwards [Ioi_mem_nhds hb] with b' hb'
    rw [h2_gauss_integral hb', Real.div_rpow Real.pi_pos.le hb'.le, Real.rpow_neg hb'.le]
    ring
  have h2 := hint.2.congr_of_eventuallyEq hev.symm
  have h3 := h2.unique hΦ
  rw [integral_neg] at h3
  have h4 : ∫ w : Ch N, ‖w‖ ^ 2 * Real.exp (-b * ‖w‖ ^ 2) = (Real.pi) ^ x * (x * b ^ (-x - 1)) := by linarith
  rw [h4, Real.div_rpow Real.pi_pos.le hb.le, hx]
  have : b ^ (-x - 1) = b ^ (-x) / b := by rw [Real.rpow_sub hb, Real.rpow_one]
  rw [this, Real.rpow_neg hb.le]
  field_simp
  rw [hx]

theorem h2_g_second {v : ℝ} (hv : 0 < v) : ∫ w : Ch N, ‖w‖ ^ 2 * h2_g v w = N * v := by
  unfold h2_g
  have : ∀ w : Ch N, ‖w‖ ^ 2 * ((2 * Real.pi * v) ^ (-(N : ℝ) / 2) * Real.exp (-(1 / (2 * v)) * ‖w‖ ^ 2))
      = (2 * Real.pi * v) ^ (-(N : ℝ) / 2) * (‖w‖ ^ 2 * Real.exp (-(1 / (2 * v)) * ‖w‖ ^ 2)) := fun w => by ring
  simp_rw [this]
  rw [integral_const_mul, h2_gauss_second (by positivity : 0 < 1 / (2 * v))]
  have h1 : Real.pi / (1 / (2 * v)) = 2 * Real.pi * v := by field_simp
  rw [h1]
  have h2 : (2 * Real.pi * v) ^ (-(N : ℝ) / 2) * ((N : ℝ) / (2 * (1 / (2 * v))) * (2 * Real.pi * v) ^ ((N : ℝ) / 2))
      = ((N : ℝ) / (2 * (1 / (2 * v)))) * ((2 * Real.pi * v) ^ (-(N : ℝ) / 2) * (2 * Real.pi * v) ^ ((N : ℝ) / 2)) := by
    ring
  rw [h2, ← Real.rpow_add (by positivity)]
  have : -(N : ℝ) / 2 + (N : ℝ) / 2 = 0 := by ring
  rw [this, Real.rpow_zero]
  field_simp

theorem h2_integrable_sq_g {v : ℝ} (hv : 0 < v) : Integrable (fun w : Ch N => ‖w‖ ^ 2 * h2_g v w) := by
  unfold h2_g
  have : ∀ w : Ch N, ‖w‖ ^ 2 * ((2 * Real.pi * v) ^ (-(N : ℝ) / 2) * Real.exp (-(1 / (2 * v)) * ‖w‖ ^ 2))
      = (2 * Real.pi * v) ^ (-(N : ℝ) / 2) * (‖w‖ ^ 2 * Real.exp (-(1 / (2 * v)) * ‖w‖ ^ 2)) := fun w => by ring
  simp_rw [this]
  exact (h2_integrable_sq_gauss (by positivity : 0 < 1 / (2 * v))).const_mul _

end HRS.MC.CepH2
