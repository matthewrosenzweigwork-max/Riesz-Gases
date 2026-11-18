import HRS.MC.CepH2Aux14

/-!
# CEPH2, helper 15: the pointwise dissipation inequality for the mollified density

At a point `x`, with `q = d(log u + U/θ)(x)`:
`θ Σ_k q(e_k) ∂_k u + ∫ q(∇U(y)) Ĝ(x-y) dμ(y) ≥ θ(1-δ) u ‖q‖² - C(x)/(4θδ)`,
where `C(x) = ∫ Ĝ(x-y) ‖∇U(y) - ∇U(x)‖² dμ(y)`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ}

/-- Riesz vector of a functional. -/
def h2_dg (q : Ch N →L[ℝ] ℝ) : Ch N := (InnerProductSpace.toDual ℝ (Ch N)).symm q

theorem h2_dg_inner (q : Ch N →L[ℝ] ℝ) (w : Ch N) : inner ℝ (h2_dg q) w = q w :=
  InnerProductSpace.toDual_symm_apply

theorem h2_norm_dg (q : Ch N →L[ℝ] ℝ) : ‖h2_dg q‖ = ‖q‖ := (InnerProductSpace.toDual ℝ (Ch N)).symm.norm_map _

theorem h2_sum_dual (q p : Ch N →L[ℝ] ℝ) : ∑ k, q (h2_e k) * p (h2_e k) = p (h2_dg q) := by
  have h := (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr' (h2_dg q)
  conv_rhs => rw [← h]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, EuclideanSpace.basisFun_apply, real_inner_comm, h2_dg_inner]
  rfl

theorem h2_sum_dual_self (q : Ch N →L[ℝ] ℝ) : ∑ k, q (h2_e k) * q (h2_e k) = ‖q‖ ^ 2 := by
  rw [h2_sum_dual, ← h2_dg_inner q (h2_dg q), real_inner_self_eq_norm_sq, h2_norm_dg]

theorem h2_sum_dual_grad {U : Ch N → ℝ} (q : Ch N →L[ℝ] ℝ) (x : Ch N) :
    ∑ k, q (h2_e k) * fderiv ℝ U x (h2_e k) = q (gradient U x) := by
  rw [h2_sum_dual, h2_fderiv_eq_inner, real_inner_comm, h2_dg_inner]

section
variable [NeZero N]

/-- The commutator functional. -/
def h2_C (v : ℝ) (U : Ch N → ℝ) (μ : Measure (Ch N)) (x : Ch N) : ℝ :=
  ∫ y, h2_per v (x - y) * ‖gradient U y - gradient U x‖ ^ 2 ∂μ

theorem h2_integrable_comm {v : ℝ} (hv : 0 < v) {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U) {μ : Measure (Ch N)}
    [IsFiniteMeasure μ] (hG2 : Integrable (fun y => ‖gradient U y‖ ^ 2) μ) (x : Ch N) :
    Integrable (fun y => h2_per v (x - y) * ‖gradient U y - gradient U x‖ ^ 2) μ := by
  obtain ⟨B, hB0, hB⟩ := h2_per_le (N := N) hv
  have hgc := h2_continuous_gradient hU
  have hb : Integrable (fun y => B * (2 * ‖gradient U y‖ ^ 2 + 2 * ‖gradient U x‖ ^ 2)) μ :=
    ((hG2.const_mul 2).add (integrable_const _)).const_mul B
  refine Integrable.mono' hb ?_ (ae_of_all _ fun y => ?_)
  · exact (((h2_continuous_per hv).comp (continuous_const.sub continuous_id)).mul
      ((hgc.sub continuous_const).norm.pow 2)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (mul_nonneg (h2_per_nonneg hv _) (sq_nonneg _))]
    refine mul_le_mul ((hB _).1.trans' (by rw [Real.norm_eq_abs]; exact le_abs_self _)) ?_ (sq_nonneg _) hB0
    have := norm_sub_le (gradient U y) (gradient U x)
    nlinarith [sq_nonneg (‖gradient U y‖ - ‖gradient U x‖), norm_nonneg (gradient U y - gradient U x),
      norm_nonneg (gradient U y), norm_nonneg (gradient U x)]

theorem h2_integrable_q_grad {v : ℝ} (hv : 0 < v) {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U) {μ : Measure (Ch N)}
    [IsFiniteMeasure μ] (hG1 : Integrable (fun y => ‖gradient U y‖) μ) (q : Ch N →L[ℝ] ℝ) (x : Ch N) :
    Integrable (fun y => q (gradient U y) * h2_per v (x - y)) μ := by
  obtain ⟨B, hB0, hB⟩ := h2_per_le (N := N) hv
  have hgc := h2_continuous_gradient hU
  have hb : Integrable (fun y => ‖q‖ * B * ‖gradient U y‖) μ := hG1.const_mul _
  refine Integrable.mono' hb ?_ (ae_of_all _ fun y => ?_)
  · exact ((q.continuous.comp hgc).mul ((h2_continuous_per hv).comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · rw [norm_mul]
    calc ‖q (gradient U y)‖ * ‖h2_per v (x - y)‖ ≤ (‖q‖ * ‖gradient U y‖) * B :=
          mul_le_mul (q.le_opNorm _) (hB _).1 (norm_nonneg _) (by positivity)
      _ = ‖q‖ * B * ‖gradient U y‖ := by ring

/-- **Pointwise dissipation inequality.** -/
theorem h2_pointwise_diss {v θ δ : ℝ} (hv : 0 < v) (hθ : 0 < θ) (hδ : 0 < δ) {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U)
    {μ : Measure (Ch N)} [IsProbabilityMeasure μ] (hG1 : Integrable (fun y => ‖gradient U y‖) μ)
    (hG2 : Integrable (fun y => ‖gradient U y‖ ^ 2) μ) (x : Ch N) (q : Ch N →L[ℝ] ℝ)
    (hq : h2_mu1 v μ x = h2_mu v μ x • (q - (1 / θ) • fderiv ℝ U x)) :
    θ * (1 - δ) * h2_mu v μ x * ‖q‖ ^ 2 - h2_C v U μ x / (4 * θ * δ) ≤
      θ * ∑ k, q (h2_e k) * h2_mu1 v μ x (h2_e k) + ∫ y, q (gradient U y) * h2_per v (x - y) ∂μ := by
  have hint1 := h2_integrable_q_grad hv hU hG1 q x
  have hint2 := h2_integrable_comm hv hU hG2 x
  have hperint := h2_integrable_per_sub hv μ x
  -- Step 1: the sum term
  have hsum : ∑ k, q (h2_e k) * h2_mu1 v μ x (h2_e k) = h2_mu v μ x * ‖q‖ ^ 2 -
      h2_mu v μ x / θ * q (gradient U x) := by
    have e : ∀ k, q (h2_e k) * h2_mu1 v μ x (h2_e k) = h2_mu v μ x * (q (h2_e k) * q (h2_e k)) -
        h2_mu v μ x / θ * (q (h2_e k) * fderiv ℝ U x (h2_e k)) := by
      intro k
      rw [hq]
      simp only [smul_apply, ContinuousLinearMap.sub_apply, smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl fun k _ => e k, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      h2_sum_dual_self, h2_sum_dual_grad]
  -- Step 2: rewrite u q(∇U x) as an integral
  have hu : h2_mu v μ x * q (gradient U x) = ∫ y, q (gradient U x) * h2_per v (x - y) ∂μ := by
    rw [integral_const_mul]; unfold h2_mu; ring
  -- Step 3: pointwise Young
  have hY : ∀ y, -(θ * δ * ‖q‖ ^ 2 + ‖gradient U y - gradient U x‖ ^ 2 / (4 * θ * δ)) * h2_per v (x - y) ≤
      (q (gradient U y) - q (gradient U x)) * h2_per v (x - y) := by
    intro y
    refine mul_le_mul_of_nonneg_right ?_ (h2_per_nonneg hv _)
    have h1 : |q (gradient U y - gradient U x)| ≤ ‖q‖ * ‖gradient U y - gradient U x‖ := by
      rw [← Real.norm_eq_abs]; exact q.le_opNorm _
    rw [map_sub] at h1
    have h2 : ‖q‖ * ‖gradient U y - gradient U x‖ ≤ θ * δ * ‖q‖ ^ 2 + ‖gradient U y - gradient U x‖ ^ 2 / (4 * θ * δ) := by
      have hpos : 0 < 4 * θ * δ := by positivity
      rw [← sub_nonneg]
      have : θ * δ * ‖q‖ ^ 2 + ‖gradient U y - gradient U x‖ ^ 2 / (4 * θ * δ) - ‖q‖ * ‖gradient U y - gradient U x‖ =
          (2 * θ * δ * ‖q‖ - ‖gradient U y - gradient U x‖) ^ 2 / (4 * θ * δ) := by
        field_simp; ring
      rw [this]; positivity
    linarith [(abs_le.1 h1).1]
  have hI : ∫ y, -(θ * δ * ‖q‖ ^ 2 + ‖gradient U y - gradient U x‖ ^ 2 / (4 * θ * δ)) * h2_per v (x - y) ∂μ ≤
      ∫ y, (q (gradient U y) - q (gradient U x)) * h2_per v (x - y) ∂μ := by
    refine integral_mono ?_ ?_ hY
    · have : Integrable (fun y => -(θ * δ * ‖q‖ ^ 2) * h2_per v (x - y) +
          (-(1 / (4 * θ * δ))) * (h2_per v (x - y) * ‖gradient U y - gradient U x‖ ^ 2)) μ :=
        (hperint.const_mul _).add (hint2.const_mul _)
      refine this.congr (ae_of_all _ fun y => ?_)
      simp only; ring
    · exact (hint1.sub (hperint.const_mul (q (gradient U x)))).congr (ae_of_all _ fun y => by simp only [Pi.sub_apply]; ring)
  have hL : ∫ y, -(θ * δ * ‖q‖ ^ 2 + ‖gradient U y - gradient U x‖ ^ 2 / (4 * θ * δ)) * h2_per v (x - y) ∂μ =
      -(θ * δ * ‖q‖ ^ 2) * h2_mu v μ x - h2_C v U μ x / (4 * θ * δ) := by
    have e : ∀ y, -(θ * δ * ‖q‖ ^ 2 + ‖gradient U y - gradient U x‖ ^ 2 / (4 * θ * δ)) * h2_per v (x - y) =
        -(θ * δ * ‖q‖ ^ 2) * h2_per v (x - y) +
          (-(1 / (4 * θ * δ))) * (h2_per v (x - y) * ‖gradient U y - gradient U x‖ ^ 2) := by
      intro y; ring
    simp_rw [e]
    rw [integral_add (hperint.const_mul _) (hint2.const_mul _), integral_const_mul, integral_const_mul]
    unfold h2_mu h2_C
    ring
  have hR : ∫ y, (q (gradient U y) - q (gradient U x)) * h2_per v (x - y) ∂μ =
      ∫ y, q (gradient U y) * h2_per v (x - y) ∂μ - h2_mu v μ x * q (gradient U x) := by
    have e : ∀ y, (q (gradient U y) - q (gradient U x)) * h2_per v (x - y) =
        q (gradient U y) * h2_per v (x - y) - q (gradient U x) * h2_per v (x - y) := fun y => by ring
    simp_rw [e]
    rw [integral_sub hint1 (hperint.const_mul _), hu]
  rw [hL, hR] at hI
  rw [hsum]
  have e : θ * (h2_mu v μ x * ‖q‖ ^ 2 - h2_mu v μ x / θ * q (gradient U x)) =
      θ * h2_mu v μ x * ‖q‖ ^ 2 - h2_mu v μ x * q (gradient U x) := by
    field_simp
  rw [e]
  nlinarith [hI]

end

end HRS.MC.CepH2
