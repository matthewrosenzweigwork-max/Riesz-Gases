import HRS.MC.CepH2Aux22

/-!
# CEPH2, helper 23: the integrated dissipation inequality with a transverse cut-off

For `χ = χ_R`: `Fχ(t) + θ(1-δ) ∫_0^t Dχ ≤ Fχ(0) + t K² N v/(4θδ) - ∫_0^t Eχ`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

/-- Cut-off dissipation `∫_cell χ u ‖dℓ‖²`. -/
def h2_Dchi (θ v : ℝ) (U : Ch N → ℝ) (μ : ℝ → Measure (Ch N)) (R s : ℝ) : ℝ :=
  ∫ x in cep_cell N, h2_chi R x * (h2_mu v (μ s) x * ‖fderiv ℝ (h2_ell θ v U (μ s)) x‖ ^ 2)

/-- The cut-off error term `∫_cell ∫ (ℓ + 1) B_χ dμ`. -/
def h2_Echi (θ v : ℝ) (U : Ch N → ℝ) (μ : ℝ → Measure (Ch N)) (R s : ℝ) : ℝ :=
  ∫ x in cep_cell N, ∫ y, (h2_ell θ v U (μ s) x + 1) * h2_B θ v U (h2_chi R) x y ∂μ s

theorem h2_norm_sq_fderiv_ell {θ v : ℝ} (hv : 0 < v) {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U) (μ : Measure (Ch N))
    [IsProbabilityMeasure μ] (x : Ch N) :
    ‖fderiv ℝ (h2_ell θ v U μ) x‖ ^ 2 = ∑ k, ((h2_mu v μ x)⁻¹ * (∫ y, h2_per1 v (x - y) (h2_e k) ∂μ) +
      (1 / θ) * fderiv ℝ U x (h2_e k)) ^ 2 := by
  rw [← h2_sum_dual_self]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hi : Integrable (fun y => h2_per1 v (x - y) (h2_e k)) μ := by
    have := (ContinuousLinearMap.apply ℝ ℝ (h2_e k)).integrable_comp (h2_integrable_per1_sub hv μ x)
    simpa using this
  have e : fderiv ℝ (h2_ell θ v U μ) x (h2_e k) = (h2_mu v μ x)⁻¹ * (∫ y, h2_per1 v (x - y) (h2_e k) ∂μ) +
      (1 / θ) * fderiv ℝ U x (h2_e k) := by
    rw [h2_fderiv_ell hv hU μ x]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    congr 2
    unfold h2_mu1
    rw [ContinuousLinearMap.integral_apply (h2_integrable_per1_sub hv μ x)]
  rw [e]; ring

section
variable {θ v : ℝ} {U : Ch N → ℝ} {K : ℝ≥0} {μ : ℝ → Measure (Ch N)} {T M : ℝ}

theorem H2Set.bound_int (S : H2Set θ v U K μ T M) {H : Ch N → Ch N → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hdom : ∀ x y, |H x y| ≤ c * (1 + ‖gradient U y‖)) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ s x, |∫ y, H x y ∂μ s| ≤ Cb := by
  obtain ⟨a, b, ha, hb, hg⟩ := h2_integral_grad_le S.hUper S.hK
  have hM0 := S.hM0
  refine ⟨c * (1 + (a + b * (1 + M))), by positivity, fun s x => ?_⟩
  haveI := S.hprob s
  have hG1 := (S.gradInt s).1
  have h1 : ∫ y, ‖gradient U y‖ ∂μ s ≤ a + b * (1 + M) := by
    refine (hg (μ s) (S.hmom s) S.hU1).trans ?_
    nlinarith [S.hM s]
  have hint : Integrable (fun y => c * (1 + ‖gradient U y‖)) (μ s) := ((integrable_const 1).add hG1).const_mul _
  have h2 : ‖∫ y, H x y ∂μ s‖ ≤ ∫ y, c * (1 + ‖gradient U y‖) ∂μ s :=
    norm_integral_le_of_norm_le hint (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hdom x y)
  rw [integral_const_mul, integral_add (integrable_const _) hG1] at h2
  simp at h2
  rw [← Real.norm_eq_abs]
  refine h2.trans ?_
  exact mul_le_mul_of_nonneg_left (by linarith) hc

theorem h2_chi_bdd {R : ℝ} (hR : 0 < R) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Ch N, ‖fderiv ℝ (h2_chi R) x‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := h2_bdd_of_far (h2_contDiff_chi1 (N := N) R) (h2_chi_periodic R)
    (fun x hx => h2_chi_support hR x hx)
  exact ⟨C, hC0, fun x => (hC x).2⟩

theorem H2Set.meas_b (S : H2Set θ v U K μ T M) {R : ℝ} (hR : 0 < R) :
    Measurable (Function.uncurry fun (s : ℝ) (x : Ch N) => ∫ y, h2_B θ v U (h2_chi R) x y ∂μ s) := by
  obtain ⟨C, hC0, hC⟩ := h2_chi_bdd (N := N) hR
  haveI : ∀ s, IsProbabilityMeasure (μ s) := S.hprob
  exact h2_measurable_param S.hnar (h2_good_B S.hv θ S.hU1 S.hUper S.hK (h2_contDiff_chi1 R) hC0 hC)
    (fun s => (S.gradInt s).1)

theorem H2Set.int_E (S : H2Set θ v U K μ T M) {R : ℝ} (hR : 0 < R) (t : ℝ) :
    Integrable (fun s => h2_Echi θ v U μ R s) (volume.restrict (Icc (0 : ℝ) t)) := by
  obtain ⟨C, hC0, hC⟩ := h2_chi_bdd (N := N) hR
  have hgood := h2_good_B S.hv θ S.hU1 S.hUper S.hK (h2_contDiff_chi1 (N := N) R) hC0 hC
  obtain ⟨c, hc⟩ := hgood.2.2.2
  have hc0 : 0 ≤ c := by
    have := (abs_nonneg (h2_B θ v U (h2_chi R) 0 0)).trans (hc 0 0)
    nlinarith [norm_nonneg (gradient U 0)]
  obtain ⟨Cb, hCb0, hCb⟩ := S.bound_int hc0 hc
  obtain ⟨cE, hcE, hE⟩ := S.ell_bound
  have hχ1 := h2_contDiff_chi1 (N := N) R
  have hd0 : ∀ x : Ch N, 2 * R < ‖h2_perp x‖ → fderiv ℝ (h2_chi R) x = 0 := fun x hx =>
    h2_fderiv_eq_zero_of_far (fun x hx => h2_chi_support hR x hx) hx
  have hEeq : ∀ s, h2_Echi θ v U μ R s =
      ∫ x in cep_cell N, (h2_ell θ v U (μ s) x + 1) * ∫ y, h2_B θ v U (h2_chi R) x y ∂μ s := by
    intro s; unfold h2_Echi; simp only [integral_const_mul]
  have hF : Measurable (Function.uncurry fun (x : Ch N) (s : ℝ) =>
      (h2_ell θ v U (μ s) x + 1) * ∫ y, h2_B θ v U (h2_chi R) x y ∂μ s) := by
    have h2 : Measurable fun p : Ch N × ℝ => h2_ell θ v U (μ p.2) p.1 := S.meas_ell.comp measurable_swap
    have h3 : Measurable fun p : Ch N × ℝ => ∫ y, h2_B θ v U (h2_chi R) p.1 y ∂μ p.2 :=
      (S.meas_b hR).comp measurable_swap
    exact (h2.add measurable_const).mul h3
  have hint := h2_integrable_tube_prod hF (R := 2 * R) (C := (cE * (1 + (2 * R) ^ 2) + 1) * Cb)
    (fun x s hx => by simp [h2_B, hd0 x hx])
    (fun x s => by
      by_cases hx : ‖h2_perp x‖ ≤ 2 * R
      · rw [abs_mul]
        have h2 : |h2_ell θ v U (μ s) x + 1| ≤ cE * (1 + (2 * R) ^ 2) + 1 := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_one]
          have := hE s x
          have h3 : 1 + ‖h2_perp x‖ ^ 2 ≤ 1 + (2 * R) ^ 2 := by nlinarith [norm_nonneg (h2_perp x)]
          nlinarith [mul_le_mul_of_nonneg_left h3 hcE]
        have hC' : 0 ≤ (cE * (1 + (2 * R) ^ 2) + 1) * Cb := by positivity
        rw [abs_of_nonneg hC']
        exact mul_le_mul h2 (hCb s x) (abs_nonneg _) (by positivity)
      · have : ∫ y, h2_B θ v U (h2_chi R) x y ∂μ s = 0 := by simp [h2_B, hd0 x (not_le.1 hx)]
        simp [this] <;> positivity)
    t
  have := hint.integral_prod_right
  refine this.congr (ae_of_all _ fun s => ?_)
  simp only [hEeq, Function.uncurry_apply_pair]

theorem H2Set.meas_Dchi (S : H2Set θ v U K μ T M) (R : ℝ) : Measurable (fun s => h2_Dchi θ v U μ R s) := by
  haveI : ∀ s, IsProbabilityMeasure (μ s) := S.hprob
  have hχm : Measurable (h2_chi (N := N) R) := (h2_contDiff_chi1 R).continuous.measurable
  have hdU : ∀ k : Fin N, Measurable fun x : Ch N => fderiv ℝ U x (h2_e k) := fun k =>
    ((S.hU1.continuous_fderiv (by simp)).clm_apply continuous_const).measurable
  have hm : ∀ k : Fin N, Measurable (Function.uncurry fun (s : ℝ) (x : Ch N) =>
      ∫ y, h2_per1 v (x - y) (h2_e k) ∂μ s) := fun k =>
    h2_measurable_param S.hnar (h2_good_per1 S.hv U (h2_e k)) (fun s => (S.gradInt s).1)
  have hG : Measurable (Function.uncurry fun (x : Ch N) (s : ℝ) =>
      h2_chi R x * (h2_mu v (μ s) x * ∑ k, ((h2_mu v (μ s) x)⁻¹ * (∫ y, h2_per1 v (x - y) (h2_e k) ∂μ s) +
        (1 / θ) * fderiv ℝ U x (h2_e k)) ^ 2)) := by
    have hu : Measurable fun p : Ch N × ℝ => h2_mu v (μ p.2) p.1 := S.meas_u.comp measurable_swap
    refine (hχm.comp measurable_fst).mul (hu.mul (Finset.measurable_sum _ fun k _ => ?_))
    have hmk : Measurable fun p : Ch N × ℝ => ∫ y, h2_per1 v (p.1 - y) (h2_e k) ∂μ p.2 :=
      (hm k).comp measurable_swap
    exact ((hu.inv.mul hmk).add (measurable_const.mul ((hdU k).comp measurable_fst))).pow_const 2
  have e : (fun s => h2_Dchi θ v U μ R s) = fun s => ∫ x in cep_cell N,
      h2_chi R x * (h2_mu v (μ s) x * ∑ k, ((h2_mu v (μ s) x)⁻¹ * (∫ y, h2_per1 v (x - y) (h2_e k) ∂μ s) +
        (1 / θ) * fderiv ℝ U x (h2_e k)) ^ 2) := by
    funext s
    unfold h2_Dchi
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [h2_norm_sq_fderiv_ell S.hv S.hU1 (μ s) x]
  rw [e]
  exact (hG.stronglyMeasurable.integral_prod_left (μ := volume.restrict (cep_cell N))).measurable

theorem H2Set.Dchi_nonneg (S : H2Set θ v U K μ T M) (R s : ℝ) : 0 ≤ h2_Dchi θ v U μ R s :=
  setIntegral_nonneg h2_cell_measurable fun x _ =>
    mul_nonneg (h2_chi_nonneg R x) (mul_nonneg (S.mu_pos s x).le (sq_nonneg _))

/-- The integrated dissipation inequality with cut-off. -/
theorem H2Set.result1 (S : H2Set θ v U K μ T M) {δ R : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hR : 0 < R) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    Integrable (fun s => h2_Dchi θ v U μ R s) (volume.restrict (Icc (0 : ℝ) t)) ∧
    h2_Fchi θ v U μ R t + θ * (1 - δ) * ∫ s in Icc (0 : ℝ) t, h2_Dchi θ v U μ R s ≤
      h2_Fchi θ v U μ R 0 + t * ((K : ℝ) ^ 2 * (N * v) / (4 * θ * δ)) -
        ∫ s in Icc (0 : ℝ) t, h2_Echi θ v U μ R s := by
  have ht0 : 0 ≤ t := ht.1
  have hθ := S.hθ
  set c0 : ℝ := (K : ℝ) ^ 2 * (N * v) / (4 * θ * δ) with hc0
  -- pointwise slice inequality
  have hslice : ∀ s, h2_Tchi θ v U μ R s ≤
      -(θ * (1 - δ)) * h2_Dchi θ v U μ R s + c0 - h2_Echi θ v U μ R s := by
    intro s
    haveI := S.hprob s
    have := h2_slice (θ := θ) (v := v) (δ := δ) (R := R) hθ S.hv hδ hR S.hU S.hUper S.hK (μ s)
      (S.gradInt s).1 (S.gradInt s).2
    have h1 : h2_Tchi θ v U μ R s = ∫ x in cep_cell N,
        h2_chi R x * (h2_ell θ v U (μ s) x + 1) * (∫ y, h2_A θ v U x y ∂μ s) := by
      unfold h2_Tchi; simp only [mul_assoc]
    rw [h1]
    unfold h2_Dchi h2_Echi
    exact this
  have hTint := S.int_Tchi hR t
  have hEint := S.int_E hR t
  have hW : Integrable (fun s => c0 - h2_Echi θ v U μ R s - h2_Tchi θ v U μ R s) (volume.restrict (Icc (0 : ℝ) t)) :=
    ((integrable_const c0).sub hEint).sub hTint
  have hDle : ∀ s, θ * (1 - δ) * h2_Dchi θ v U μ R s ≤ c0 - h2_Echi θ v U μ R s - h2_Tchi θ v U μ R s := by
    intro s; have := hslice s; linarith
  have hθδ : 0 ≤ θ * (1 - δ) := mul_nonneg hθ.le (by linarith)
  have hDint : Integrable (fun s => θ * (1 - δ) * h2_Dchi θ v U μ R s) (volume.restrict (Icc (0 : ℝ) t)) := by
    refine Integrable.mono' hW ((S.meas_Dchi R).const_mul _).aestronglyMeasurable (ae_of_all _ fun s => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg hθδ (S.Dchi_nonneg R s))]
    exact hDle s
  have hmono := integral_mono hDint hW hDle
  have hW1 : Integrable (fun s => c0 - h2_Echi θ v U μ R s) (volume.restrict (Icc (0 : ℝ) t)) :=
    (integrable_const c0).sub hEint
  rw [integral_sub hW1 hTint, integral_sub (integrable_const c0) hEint, integral_const_mul] at hmono
  have hconst : ∫ s in Icc (0 : ℝ) t, c0 = t * c0 := by
    simp [ht0]
  rw [hconst] at hmono
  have hF := S.fchi_eq hR ht
  refine ⟨?_, by linarith⟩
  have hne : θ * (1 - δ) ≠ 0 := (mul_pos hθ (by linarith)).ne'
  refine (hDint.const_mul (θ * (1 - δ))⁻¹).congr (ae_of_all _ fun s => ?_)
  simp only [inv_mul_cancel_left₀ hne]

end

end HRS.MC.CepH2
