import HRS.MC.CepH2Aux9

/-!
# CEPH2, helper 10: logarithmic lower bound of the mollified density
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

theorem h2_cell_norm_sq_le {z : Ch N} (hz : z ∈ cep_cell N) :
    ‖z‖ ^ 2 ≤ 2 * (1 + Real.sqrt N) ^ 2 * ‖h2_perp z‖ ^ 2 + 2 * N := by
  have h := h2_cell_norm_le hz
  have hs : (Real.sqrt N) ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg N)
  have h1 : ‖z‖ ≤ (1 + Real.sqrt N) * ‖h2_perp z‖ + Real.sqrt N := by linarith
  have h2 : ‖z‖ ^ 2 ≤ ((1 + Real.sqrt N) * ‖h2_perp z‖ + Real.sqrt N) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg ((1 + Real.sqrt N) * ‖h2_perp z‖ - Real.sqrt N)]

theorem h2_integrable_norm_sq_of_perp {μ : Measure (Ch N)} [IsFiniteMeasure μ] (hcell : μ (cep_cell N)ᶜ = 0)
    (hmom : Integrable (fun y => ‖h2_perp y‖ ^ 2) μ) : Integrable (fun y : Ch N => ‖y‖ ^ 2) μ := by
  have hb : Integrable (fun y : Ch N => 2 * (1 + Real.sqrt N) ^ 2 * ‖h2_perp y‖ ^ 2 + 2 * N) μ :=
    (hmom.const_mul (2 * (1 + Real.sqrt N) ^ 2)).add (integrable_const (2 * (N : ℝ)))
  refine Integrable.mono' hb (by fun_prop) ?_
  have : ∀ᵐ y ∂μ, y ∈ cep_cell N := mem_ae_iff.2 hcell
  filter_upwards [this] with y hy
  rw [Real.norm_of_nonneg (by positivity)]
  exact h2_cell_norm_sq_le hy

/-- The lower-bound constant. -/
def h2_logA (N : ℕ) (v : ℝ) : ℝ :=
  |Real.log ((2 * Real.pi * v) ^ (-(N : ℝ) / 2))| + 4 * N / v + 2 * (1 + Real.sqrt N) ^ 2 / v

theorem h2_logA_nonneg {v : ℝ} (hv : 0 < v) : 0 ≤ h2_logA N v := by
  unfold h2_logA; positivity

/-- Pointwise lower bound `u ≥ c₀ exp(-(‖x‖² + ∫‖y‖²)/v)`. -/
theorem h2_mu_lower_exp {v : ℝ} (hv : 0 < v) (μ : Measure (Ch N)) [IsProbabilityMeasure μ]
    (hY : Integrable (fun y : Ch N => ‖y‖ ^ 2) μ) (x : Ch N) :
    (2 * Real.pi * v) ^ (-(N : ℝ) / 2) * Real.exp (-(‖x‖ ^ 2 + ∫ y, ‖y‖ ^ 2 ∂μ) / v) ≤ h2_mu v μ x := by
  set c0 : ℝ := (2 * Real.pi * v) ^ (-(N : ℝ) / 2) with hc0
  have hc0pos : 0 < c0 := by
    have : 0 < 2 * Real.pi * v := by positivity
    positivity
  have hsub : Integrable (fun y : Ch N => ‖x - y‖ ^ 2) μ := by
    have hb : Integrable (fun y : Ch N => 2 * ‖y‖ ^ 2 + 2 * ‖x‖ ^ 2) μ :=
      (hY.const_mul 2).add (integrable_const (2 * ‖x‖ ^ 2))
    refine Integrable.mono' hb (by fun_prop) (ae_of_all _ fun y => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
    nlinarith [sq_nonneg (‖x‖ - ‖y‖), norm_nonneg x, norm_nonneg y, norm_nonneg (x - y)]
  -- step 1: u ≥ ∫ g(x - y)
  have hgint : Integrable (fun y => h2_g v (x - y)) μ := by
    refine (integrable_const (c0)).mono' ((h2_continuous_g v).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun y => ?_)
    rw [Real.norm_of_nonneg (h2_g_pos hv _).le]
    unfold h2_g
    have : Real.exp (-(1 / (2 * v)) * ‖x - y‖ ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg ‖x - y‖, (by positivity : 0 < 1 / (2 * v))]
    nlinarith [hc0pos]
  have h1 : ∫ y, h2_g v (x - y) ∂μ ≤ h2_mu v μ x := by
    refine integral_mono hgint (h2_integrable_per_sub hv μ x) fun y => ?_
    show h2_g v (x - y) ≤ h2_per v (x - y)
    unfold h2_per
    have := (h2_summable_g_trans hv (x - y)).le_tsum 0 (fun m _ => (h2_g_pos hv _).le)
    simpa using this
  refine le_trans ?_ h1
  -- step 2: Jensen
  have hf : Integrable (fun y => -(1 / (2 * v)) * ‖x - y‖ ^ 2) μ := hsub.const_mul _
  have hJ := ConvexOn.map_integral_le (μ := μ) (g := Real.exp) (s := Set.univ) convexOn_exp
    Real.continuous_exp.continuousOn isClosed_univ (ae_of_all _ fun _ => Set.mem_univ _) hf
    (by
      refine (integrable_const (1 : ℝ)).mono' (Real.continuous_exp.comp_aestronglyMeasurable hf.1) (ae_of_all _ fun y => ?_)
      rw [Function.comp_apply, Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
      nlinarith [sq_nonneg ‖x - y‖, (by positivity : 0 < 1 / (2 * v))])
  have hg : ∫ y, h2_g v (x - y) ∂μ = c0 * ∫ y, Real.exp (-(1 / (2 * v)) * ‖x - y‖ ^ 2) ∂μ := by
    rw [← integral_const_mul]; rfl
  rw [hg]
  refine mul_le_mul_of_nonneg_left (le_trans ?_ hJ) hc0pos.le
  refine Real.exp_le_exp.2 ?_
  rw [integral_const_mul]
  have h3 : ∫ y, ‖x - y‖ ^ 2 ∂μ ≤ 2 * ‖x‖ ^ 2 + 2 * ∫ y, ‖y‖ ^ 2 ∂μ := by
    have hb : Integrable (fun y : Ch N => 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) μ :=
      (integrable_const (2 * ‖x‖ ^ 2)).add (hY.const_mul 2)
    have := integral_mono hsub hb
      (fun y => by
        show ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2
        nlinarith [sq_nonneg (‖x‖ - ‖y‖), norm_nonneg x, norm_nonneg y, norm_nonneg (x - y), norm_sub_le x y])
    rw [integral_add (integrable_const _) (hY.const_mul 2), integral_const, integral_const_mul] at this
    simpa using this
  have h4 : 0 ≤ 1 / (2 * v) := by positivity
  have h5 : -(‖x‖ ^ 2 + ∫ y, ‖y‖ ^ 2 ∂μ) / v = -(1 / (2 * v)) * (2 * ‖x‖ ^ 2 + 2 * ∫ y, ‖y‖ ^ 2 ∂μ) := by
    field_simp
  rw [h5]
  nlinarith [mul_le_mul_of_nonneg_left h3 h4]

theorem h2_mu_log_lower {v : ℝ} (hv : 0 < v) (μ : Measure (Ch N)) [IsProbabilityMeasure μ]
    (hcell : μ (cep_cell N)ᶜ = 0) (hmom : Integrable (fun y => ‖h2_perp y‖ ^ 2) μ) {x : Ch N} (hx : x ∈ cep_cell N) :
    -Real.log (h2_mu v μ x) ≤ h2_logA N v * (1 + ∫ y, ‖h2_perp y‖ ^ 2 ∂μ + ‖h2_perp x‖ ^ 2) := by
  have hY := h2_integrable_norm_sq_of_perp hcell hmom
  set M2 : ℝ := ∫ y, ‖h2_perp y‖ ^ 2 ∂μ with hM2
  have hM2n : 0 ≤ M2 := integral_nonneg fun y => by positivity
  have hY2 : ∫ y, ‖y‖ ^ 2 ∂μ ≤ 2 * (1 + Real.sqrt N) ^ 2 * M2 + 2 * N := by
    have hae : ∀ᵐ y ∂μ, y ∈ cep_cell N := mem_ae_iff.2 hcell
    have hb : Integrable (fun y : Ch N => 2 * (1 + Real.sqrt N) ^ 2 * ‖h2_perp y‖ ^ 2 + 2 * N) μ :=
      (hmom.const_mul (2 * (1 + Real.sqrt N) ^ 2)).add (integrable_const (2 * (N : ℝ)))
    have := integral_mono_ae hY hb
      (by filter_upwards [hae] with y hy; exact h2_cell_norm_sq_le hy)
    rw [integral_add (hmom.const_mul _) (integrable_const _), integral_const_mul, integral_const] at this
    simpa using this
  have hlow := h2_mu_lower_exp hv μ hY x
  set c0 : ℝ := (2 * Real.pi * v) ^ (-(N : ℝ) / 2) with hc0
  have hc0pos : 0 < c0 := by
    have : 0 < 2 * Real.pi * v := by positivity
    positivity
  have hlog : Real.log c0 + (-(‖x‖ ^ 2 + ∫ y, ‖y‖ ^ 2 ∂μ) / v) ≤ Real.log (h2_mu v μ x) := by
    have := Real.log_le_log (mul_pos hc0pos (Real.exp_pos _)) hlow
    rwa [Real.log_mul hc0pos.ne' (Real.exp_pos _).ne', Real.log_exp] at this
  have hx2 := h2_cell_norm_sq_le hx
  have habs : -Real.log c0 ≤ |Real.log c0| := neg_le_abs _
  have hAeq : h2_logA N v = |Real.log c0| + 4 * N / v + 2 * (1 + Real.sqrt N) ^ 2 / v := rfl
  have hQ : 0 ≤ 2 * (1 + Real.sqrt N) ^ 2 / v := by positivity
  have hN : 0 ≤ 4 * (N : ℝ) / v := by positivity
  have hP : 0 ≤ ‖h2_perp x‖ ^ 2 := by positivity
  -- -log u ≤ -log c0 + (‖x‖² + Y2)/v
  have h6 : -Real.log (h2_mu v μ x) ≤ -Real.log c0 + (‖x‖ ^ 2 + ∫ y, ‖y‖ ^ 2 ∂μ) / v := by
    have : -(‖x‖ ^ 2 + ∫ y, ‖y‖ ^ 2 ∂μ) / v = -((‖x‖ ^ 2 + ∫ y, ‖y‖ ^ 2 ∂μ) / v) := by ring
    linarith
  have h7 : (‖x‖ ^ 2 + ∫ y, ‖y‖ ^ 2 ∂μ) / v ≤
      (2 * (1 + Real.sqrt N) ^ 2 * ‖h2_perp x‖ ^ 2 + 2 * N + (2 * (1 + Real.sqrt N) ^ 2 * M2 + 2 * N)) / v :=
    div_le_div_of_nonneg_right (by linarith) hv.le
  have h8 : (2 * (1 + Real.sqrt N) ^ 2 * ‖h2_perp x‖ ^ 2 + 2 * N + (2 * (1 + Real.sqrt N) ^ 2 * M2 + 2 * N)) / v
      = 4 * N / v + 2 * (1 + Real.sqrt N) ^ 2 / v * (M2 + ‖h2_perp x‖ ^ 2) := by
    field_simp; ring
  rw [hAeq]
  nlinarith [mul_nonneg hQ hM2n, mul_nonneg hQ hP, mul_nonneg (abs_nonneg (Real.log c0)) hM2n,
    mul_nonneg (abs_nonneg (Real.log c0)) hP]

end HRS.MC.CepH2
