import HRS.MC.CepH2Aux6

/-!
# CEPH2, helper 7: the mollified density `u = Ĝ * μ`

Differentiation under the integral sign for convolutions with the periodised Gaussian, positivity, periodicity,
upper bounds and the identification with the vocabulary of `CepH2Spec`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ}

/-- Differentiation under the integral of a convolution against a finite measure. -/
theorem h2_hasFDerivAt_conv {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {ψ : Ch N → G} {ψ' : Ch N → Ch N →L[ℝ] G} (hψ : ∀ w, HasFDerivAt ψ (ψ' w) w)
    (hcont : Continuous ψ) (hcont' : Continuous ψ') {B0 B : ℝ} (hbd : ∀ w, ‖ψ w‖ ≤ B0)
    (hB : ∀ w, ‖ψ' w‖ ≤ B) (μ : Measure (Ch N)) [IsFiniteMeasure μ] (x : Ch N) :
    HasFDerivAt (fun x => ∫ y, ψ (x - y) ∂μ) (∫ y, ψ' (x - y) ∂μ) x := by
  have hm : ∀ x : Ch N, AEStronglyMeasurable (fun y => ψ (x - y)) μ := fun x =>
    (hcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hint : Integrable (fun y => ψ (x - y)) μ :=
    (integrable_const B0).mono' (hm x) (ae_of_all _ fun y => hbd _)
  have hm' : AEStronglyMeasurable (fun y => ψ' (x - y)) μ :=
    (hcont'.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := μ) (F := fun x y => ψ (x - y))
    (F' := fun x y => ψ' (x - y)) (x₀ := x) (bound := fun _ => B) (s := Set.univ) Filter.univ_mem
    (Eventually.of_forall hm) hint hm' (ae_of_all _ fun y x _ => hB _) (integrable_const B)
    (ae_of_all _ fun y x _ => by
      have h1 : HasFDerivAt (fun x : Ch N => x - y) (ContinuousLinearMap.id ℝ (Ch N)) x :=
        (hasFDerivAt_id x).sub_const y
      have h := (hψ (x - y)).comp x h1
      rw [ContinuousLinearMap.comp_id] at h
      exact h)
  exact this

/-- Mollified density `x ↦ ∫ Ĝ_v(x - y) dμ(y)` and its two derivatives. -/
def h2_mu (v : ℝ) (μ : Measure (Ch N)) (x : Ch N) : ℝ := ∫ y, h2_per v (x - y) ∂μ

def h2_mu1 (v : ℝ) (μ : Measure (Ch N)) (x : Ch N) : Ch N →L[ℝ] ℝ := ∫ y, h2_per1 v (x - y) ∂μ

def h2_mu2 (v : ℝ) (μ : Measure (Ch N)) (x : Ch N) : Ch N →L[ℝ] Ch N →L[ℝ] ℝ := ∫ y, h2_per2 v (x - y) ∂μ

section
variable [NeZero N]

theorem h2_per_le {v : ℝ} (hv : 0 < v) : ∃ B : ℝ, 0 ≤ B ∧ ∀ w : Ch N, ‖h2_per v w‖ ≤ B ∧ ‖h2_per1 v w‖ ≤ B ∧
    ‖h2_per2 v w‖ ≤ B := by
  obtain ⟨B, hB, h⟩ := h2_per_bounds (N := N) hv
  refine ⟨B, hB, fun w => ?_⟩
  have h1 : Real.exp (-(1 / (4 * v)) * ‖h2_perp w‖ ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg ‖h2_perp w‖, (by positivity : 0 < 1 / (4 * v))]
  have := h w
  refine ⟨this.1.trans ?_, this.2.1.trans ?_, this.2.2.trans ?_⟩ <;> nlinarith

theorem h2_continuous_per {v : ℝ} (hv : 0 < v) : Continuous (h2_per (N := N) v) :=
  (h2_contDiff_per hv).continuous

theorem h2_continuous_per1 {v : ℝ} (hv : 0 < v) : Continuous (h2_per1 (N := N) v) := by
  rw [← h2_fderiv_per hv]
  exact (h2_contDiff_per hv).continuous_fderiv (by simp)

theorem h2_hasFDerivAt_mu {v : ℝ} (hv : 0 < v) (μ : Measure (Ch N)) [IsFiniteMeasure μ] (x : Ch N) :
    HasFDerivAt (h2_mu v μ) (h2_mu1 v μ x) x := by
  obtain ⟨B, hB, h⟩ := h2_per_le (N := N) hv
  exact h2_hasFDerivAt_conv (h2_hasFDerivAt_per hv) (h2_continuous_per hv) (h2_continuous_per1 hv)
    (fun w => (h w).1) (fun w => (h w).2.1) μ x

theorem h2_hasFDerivAt_mu1 {v : ℝ} (hv : 0 < v) (μ : Measure (Ch N)) [IsFiniteMeasure μ] (x : Ch N) :
    HasFDerivAt (h2_mu1 v μ) (h2_mu2 v μ x) x := by
  obtain ⟨B, hB, h⟩ := h2_per_le (N := N) hv
  exact h2_hasFDerivAt_conv (h2_hasFDerivAt_per1 hv) (h2_continuous_per1 hv) (h2_continuous_per2 hv)
    (fun w => (h w).2.1) (fun w => (h w).2.2) μ x

theorem h2_per_nonneg {v : ℝ} (hv : 0 < v) (w : Ch N) : 0 ≤ h2_per v w := (h2_per_pos hv w).le

theorem h2_mu_periodic (v : ℝ) (μ : Measure (Ch N)) (x : Ch N) : h2_mu v μ (x + cep_diag N) = h2_mu v μ x := by
  unfold h2_mu
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  show h2_per v (x + cep_diag N - y) = h2_per v (x - y)
  rw [add_sub_right_comm]; exact h2_per_periodic v _

theorem h2_mu1_periodic (v : ℝ) (μ : Measure (Ch N)) (x : Ch N) : h2_mu1 v μ (x + cep_diag N) = h2_mu1 v μ x := by
  unfold h2_mu1
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  show h2_per1 v (x + cep_diag N - y) = h2_per1 v (x - y)
  rw [add_sub_right_comm]; exact h2_per1_periodic v _

theorem h2_mu_pos {v : ℝ} (hv : 0 < v) (μ : Measure (Ch N)) [IsProbabilityMeasure μ] (x : Ch N) :
    0 < h2_mu v μ x := by
  obtain ⟨B, hB, h⟩ := h2_per_le (N := N) hv
  have hint : Integrable (fun y => h2_per v (x - y)) μ :=
    (integrable_const B).mono' ((h2_continuous_per hv).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun y => (h _).1)
  unfold h2_mu
  rw [integral_pos_iff_support_of_nonneg (fun y => h2_per_nonneg hv _) hint]
  have : Function.support (fun y => h2_per v (x - y)) = Set.univ := by
    ext y; simp [(h2_per_pos hv (x - y)).ne']
  rw [this]; simp

theorem h2_mu_le {v : ℝ} (hv : 0 < v) (μ : Measure (Ch N)) [IsProbabilityMeasure μ] :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, h2_mu v μ x ≤ B ∧ ‖h2_mu1 v μ x‖ ≤ B ∧ ‖h2_mu2 v μ x‖ ≤ B := by
  obtain ⟨B, hB, h⟩ := h2_per_le (N := N) hv
  refine ⟨B, hB, fun x => ⟨?_, ?_, ?_⟩⟩
  · have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun y => h2_per v (x - y)) (C := B)
      (ae_of_all _ fun y => (h _).1)
    calc h2_mu v μ x ≤ ‖h2_mu v μ x‖ := Real.le_norm_self _
      _ ≤ B := by simpa [h2_mu] using this
  · have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun y => h2_per1 v (x - y)) (C := B)
      (ae_of_all _ fun y => (h _).2.1)
    show ‖∫ y, h2_per1 v (x - y) ∂μ‖ ≤ B
    simpa using this
  · have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun y => h2_per2 v (x - y)) (C := B)
      (ae_of_all _ fun y => (h _).2.2)
    show ‖∫ y, h2_per2 v (x - y) ∂μ‖ ≤ B
    simpa using this

theorem h2_kern_eq_per (θ ε : ℝ) : h2_kern (N := N) θ ε = h2_per (2 * θ * ε) := by
  funext w
  unfold h2_kern h2_per
  refine tsum_congr fun m => ?_
  unfold h2_gauss h2_g
  have e1 : 4 * Real.pi * θ * ε = 2 * Real.pi * (2 * θ * ε) := by ring
  have e2 : -‖w + (m : ℝ) • cep_diag N‖ ^ 2 / (4 * θ * ε) = -(1 / (2 * (2 * θ * ε))) * ‖w + (m : ℝ) • cep_diag N‖ ^ 2 := by
    by_cases h : θ * ε = 0
    · have : 4 * θ * ε = 0 := by linarith [show 4 * θ * ε = 4 * (θ * ε) by ring]
      have : 2 * (2 * θ * ε) = 0 := by linarith [show 2 * (2 * θ * ε) = 4 * (θ * ε) by ring]
      simp [*]
    · field_simp; ring
  rw [e1, e2]

theorem h2_mol_eq_mu (θ ε : ℝ) (μ : Measure (Ch N)) : h2_mol θ ε μ = h2_mu (2 * θ * ε) μ := by
  funext x
  unfold h2_mol h2_mu
  rw [h2_kern_eq_per]

end

end HRS.MC.CepH2
