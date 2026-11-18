import HRS.MC.CepH2Aux19

/-!
# CEPH2, helper 20: the setting and uniform bounds

`H2Set θ v U K μ T M` collects the hypotheses of the mollified dissipation argument, with all bounds
holding for every `t` (the family is clamped to `[0,T]` before the argument starts).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

structure H2Set (θ v : ℝ) (U : Ch N → ℝ) (K : ℝ≥0) (μ : ℝ → Measure (Ch N)) (T M : ℝ) : Prop where
  hθ : 0 < θ
  hv : 0 < v
  hU : ContDiff ℝ 1 U
  hUper : ∀ z, U (z + cep_diag N) = U z
  hK : LipschitzWith K (gradient U)
  hT : 0 ≤ T
  hprob : ∀ t, IsProbabilityMeasure (μ t)
  hcell : ∀ t, μ t (cep_cell N)ᶜ = 0
  hmom : ∀ t, Integrable (fun y => ‖h2_perp y‖ ^ 2) (μ t)
  hM : ∀ t, ∫ y, ‖h2_perp y‖ ^ 2 ∂(μ t) ≤ M
  hnar : H2Narrow μ
  hfp : ∀ g : Ch N → ℝ, H2Test g → ∀ t ∈ Icc (0 : ℝ) T,
    ∫ z, g z ∂(μ t) = ∫ z, g z ∂(μ 0) + ∫ s in Icc (0 : ℝ) t, ∫ z, h2_gen θ U g z ∂(μ s)

section
variable {θ v : ℝ} {U : Ch N → ℝ} {K : ℝ≥0} {μ : ℝ → Measure (Ch N)} {T M : ℝ}

theorem H2Set.hU1 (S : H2Set θ v U K μ T M) : ContDiff ℝ 1 U := S.hU.of_le (by norm_num)

theorem H2Set.hM0 (S : H2Set θ v U K μ T M) : 0 ≤ M :=
  le_trans (integral_nonneg fun y => by positivity) (S.hM 0)

theorem h2_integrable_grad {U : Ch N → ℝ} (hUper : ∀ z, U (z + cep_diag N) = U z) {K : ℝ≥0}
    (hK : LipschitzWith K (gradient U)) (hU : ContDiff ℝ 1 U) {μ : Measure (Ch N)} [IsFiniteMeasure μ]
    (hmom : Integrable (fun y => ‖h2_perp y‖ ^ 2) μ) :
    Integrable (fun y => ‖gradient U y‖) μ ∧ Integrable (fun y => ‖gradient U y‖ ^ 2) μ := by
  obtain ⟨a, b, ha, hb, hab⟩ := h2_grad_growth hUper hK
  have hgc := h2_continuous_gradient hU
  constructor
  · have hbd : Integrable (fun y => (a + b) + b * ‖h2_perp y‖ ^ 2) μ :=
      (integrable_const _).add (hmom.const_mul b)
    refine Integrable.mono' hbd hgc.norm.aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    nlinarith [hab y, norm_nonneg (h2_perp y), sq_nonneg (‖h2_perp y‖ - 1), mul_nonneg hb (sq_nonneg (‖h2_perp y‖ - 1))]
  · have hbd : Integrable (fun y => 2 * a ^ 2 + 2 * b ^ 2 * ‖h2_perp y‖ ^ 2) μ :=
      (integrable_const _).add (hmom.const_mul (2 * b ^ 2))
    refine Integrable.mono' hbd (hgc.norm.pow 2).aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have h1 := hab y
    have h0 := norm_nonneg (gradient U y)
    nlinarith [sq_nonneg (a - b * ‖h2_perp y‖), mul_nonneg hb (norm_nonneg (h2_perp y))]

theorem H2Set.gradInt (S : H2Set θ v U K μ T M) (t : ℝ) :
    Integrable (fun y => ‖gradient U y‖) (μ t) ∧ Integrable (fun y => ‖gradient U y‖ ^ 2) (μ t) := by
  haveI := S.hprob t
  exact h2_integrable_grad S.hUper S.hK S.hU1 (S.hmom t)

theorem h2_integral_grad_le {U : Ch N → ℝ} (hUper : ∀ z, U (z + cep_diag N) = U z) {K : ℝ≥0}
    (hK : LipschitzWith K (gradient U)) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ ∀ (μ : Measure (Ch N)) [IsProbabilityMeasure μ],
      Integrable (fun y => ‖h2_perp y‖ ^ 2) μ → ∀ (hU : ContDiff ℝ 1 U),
      ∫ y, ‖gradient U y‖ ∂μ ≤ a + b * (1 + ∫ y, ‖h2_perp y‖ ^ 2 ∂μ) := by
  obtain ⟨a, b, ha, hb, hab⟩ := h2_grad_growth hUper hK
  refine ⟨a, b, ha, hb, fun μ _ hmom hU => ?_⟩
  have hG := (h2_integrable_grad hUper hK hU hmom).1
  have hbd : Integrable (fun y => (a + b) + b * ‖h2_perp y‖ ^ 2) μ :=
    (integrable_const _).add (hmom.const_mul b)
  have := integral_mono hG hbd (fun y => by
    nlinarith [hab y, norm_nonneg (h2_perp y), sq_nonneg (‖h2_perp y‖ - 1), mul_nonneg hb (sq_nonneg (‖h2_perp y‖ - 1))])
  rw [integral_add (integrable_const _) (hmom.const_mul b), integral_const_mul, integral_const] at this
  simp at this
  nlinarith [this]

theorem H2Set.bound_A (S : H2Set θ v U K μ T M) : ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ s x, |∫ y, h2_A θ v U x y ∂μ s| ≤ Ca := by
  obtain ⟨B2, hB2, hB⟩ := h2_A_bound S.hv θ U
  obtain ⟨a, b, ha, hb, hg⟩ := h2_integral_grad_le S.hUper S.hK
  refine ⟨B2 * (1 + (a + b * (1 + M))), by have := S.hM0; positivity, fun s x => ?_⟩
  haveI := S.hprob s
  have hG1 := (S.gradInt s).1
  have h1 : ∫ y, ‖gradient U y‖ ∂μ s ≤ a + b * (1 + M) := by
    refine (hg (μ s) (S.hmom s) S.hU1).trans ?_
    nlinarith [S.hM s]
  have hn : |∫ y, h2_A θ v U x y ∂μ s| ≤ ∫ y, |h2_A θ v U x y| ∂μ s := by
    rw [← Real.norm_eq_abs]
    exact (norm_integral_le_integral_norm _).trans (by simp)
  have hint : Integrable (fun y => B2 * (1 + ‖gradient U y‖)) (μ s) := ((integrable_const 1).add hG1).const_mul _
  have h2 : ∫ y, |h2_A θ v U x y| ∂μ s ≤ ∫ y, B2 * (1 + ‖gradient U y‖) ∂μ s := by
    refine integral_mono_of_nonneg (ae_of_all _ fun y => abs_nonneg _) hint (ae_of_all _ fun y => hB x y)
  rw [integral_const_mul, integral_add (integrable_const _) hG1] at h2
  simp at h2
  refine hn.trans (h2.trans ?_)
  exact mul_le_mul_of_nonneg_left (by linarith) hB2

theorem h2_mu_le_uniform {v : ℝ} (hv : 0 < v) : ∃ B : ℝ, 0 ≤ B ∧ ∀ (μ : Measure (Ch N)) [IsProbabilityMeasure μ] (x : Ch N),
    h2_mu v μ x ≤ B := by
  obtain ⟨B, hB0, hB⟩ := h2_per_le (N := N) hv
  refine ⟨B, hB0, fun μ _ x => ?_⟩
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun y => h2_per v (x - y)) (C := B)
    (ae_of_all _ fun y => (hB _).1)
  calc h2_mu v μ x ≤ ‖h2_mu v μ x‖ := Real.le_norm_self _
    _ ≤ B := by simpa [h2_mu] using this

theorem H2Set.log_bound (S : H2Set θ v U K μ T M) :
    ∃ cL : ℝ, 0 ≤ cL ∧ ∀ s x, |Real.log (h2_mu v (μ s) x)| ≤ cL * (1 + ‖h2_perp x‖ ^ 2) := by
  obtain ⟨B, hB0, hB⟩ := h2_mu_le_uniform (N := N) S.hv
  have hA := h2_logA_nonneg (N := N) S.hv
  have hM0 := S.hM0
  refine ⟨|Real.log B| + h2_logA N v * (1 + M), by positivity, fun s x => ?_⟩
  haveI := S.hprob s
  set r := ‖h2_perp x‖ with hr
  have hr2 : 0 ≤ r ^ 2 := by positivity
  have hupper : Real.log (h2_mu v (μ s) x) ≤ |Real.log B| := by
    have := Real.log_le_log (h2_mu_pos S.hv (μ s) x) (hB (μ s) x)
    exact this.trans (le_abs_self _)
  -- lower bound: extend from the cell by periodicity
  have hx' : cep_reduce x ∈ cep_cell N := h2_reduce_mem_cell x
  have hlow := h2_mu_log_lower S.hv (μ s) (S.hcell s) (S.hmom s) hx'
  have e1 : h2_mu v (μ s) (cep_reduce x) = h2_mu v (μ s) x := h2_periodic_reduce (g := h2_mu v (μ s))
    (fun z => h2_mu_periodic v (μ s) z) x
  rw [e1, h2_perp_reduce] at hlow
  have hM2 := S.hM s
  have hlow2 : -Real.log (h2_mu v (μ s) x) ≤ h2_logA N v * (1 + M) * (1 + r ^ 2) := by
    refine hlow.trans ?_
    nlinarith [mul_nonneg hA hr2, mul_nonneg hA (sub_nonneg.2 hM2), mul_nonneg (mul_nonneg hA hM0) hr2]
  have hc : (|Real.log B| + h2_logA N v * (1 + M)) * (1 + r ^ 2) =
      |Real.log B| * (1 + r ^ 2) + h2_logA N v * (1 + M) * (1 + r ^ 2) := by ring
  have hp : 0 ≤ |Real.log B| * (1 + r ^ 2) := by positivity
  rw [abs_le]
  constructor
  · linarith
  · have h1 : 0 ≤ |Real.log B| * r ^ 2 := mul_nonneg (abs_nonneg _) hr2
    have h2 : 0 ≤ h2_logA N v * (1 + M) * (1 + r ^ 2) :=
      mul_nonneg (mul_nonneg hA (by linarith)) (by positivity)
    nlinarith

theorem H2Set.ell_bound (S : H2Set θ v U K μ T M) :
    ∃ cE : ℝ, 0 ≤ cE ∧ ∀ s x, |h2_ell θ v U (μ s) x| ≤ cE * (1 + ‖h2_perp x‖ ^ 2) := by
  obtain ⟨cL, hcL, hL⟩ := S.log_bound
  obtain ⟨a, b, ha, hb, hU⟩ := h2_U_growth S.hU1 S.hUper S.hK
  have hθ := S.hθ
  refine ⟨cL + (a + b) / θ, by positivity, fun s x => ?_⟩
  set r := ‖h2_perp x‖ with hr
  have hr2 : 0 ≤ r ^ 2 := by positivity
  unfold h2_ell
  refine (abs_add_le _ _).trans ?_
  have h1 := hL s x
  have h2 : |(1 / θ) * U x| ≤ (a + b) / θ * (1 + r ^ 2) := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / θ)]
    have h3 : a + b * r ^ 2 ≤ (a + b) * (1 + r ^ 2) := by nlinarith [mul_nonneg ha hr2, mul_nonneg hb hr2]
    calc 1 / θ * |U x| ≤ 1 / θ * (a + b * r ^ 2) := mul_le_mul_of_nonneg_left (hU x) (by positivity)
      _ ≤ 1 / θ * ((a + b) * (1 + r ^ 2)) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (a + b) / θ * (1 + r ^ 2) := by ring
  nlinarith [h1, h2]

end

end HRS.MC.CepH2
