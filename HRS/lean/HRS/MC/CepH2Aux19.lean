import HRS.MC.CepH2Aux18

/-!
# CEPH2, helper 19: `y ↦ Ĝ(x - y)` is a weak Fokker-Planck test function

Its generator is `h2_A`, and hence `u_t(x) = u_0(x) + ∫_0^t ∫ A(x,y) dμ_s(y) ds`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

theorem h2_hasFDerivAt_per_neg {v : ℝ} (hv : 0 < v) (x z : Ch N) :
    HasFDerivAt (fun z => h2_per v (x - z)) (-(h2_per1 v (x - z))) z := by
  have h1 : HasFDerivAt (fun z : Ch N => x - z) (-(ContinuousLinearMap.id ℝ (Ch N))) z :=
    (hasFDerivAt_id z).const_sub x
  have h := (h2_hasFDerivAt_per hv (x - z)).comp z h1
  exact h.congr_fderiv (by ext w; simp)

theorem h2_hasFDerivAt_per1_neg {v : ℝ} (hv : 0 < v) (x z : Ch N) :
    HasFDerivAt (fun z => -(h2_per1 v (x - z))) (h2_per2 v (x - z)) z := by
  have h1 : HasFDerivAt (fun z : Ch N => x - z) (-(ContinuousLinearMap.id ℝ (Ch N))) z :=
    (hasFDerivAt_id z).const_sub x
  have h := ((h2_hasFDerivAt_per1 hv (x - z)).comp z h1).neg
  exact h.congr_fderiv (by ext w w'; simp)

theorem h2_fderiv_per_neg {v : ℝ} (hv : 0 < v) (x : Ch N) :
    fderiv ℝ (fun z => h2_per v (x - z)) = fun z => -(h2_per1 v (x - z)) :=
  funext fun z => (h2_hasFDerivAt_per_neg hv x z).fderiv

theorem h2_fderiv_fderiv_per_neg {v : ℝ} (hv : 0 < v) (x z : Ch N) :
    fderiv ℝ (fderiv ℝ (fun z => h2_per v (x - z))) z = h2_per2 v (x - z) := by
  rw [h2_fderiv_per_neg hv x]
  exact (h2_hasFDerivAt_per1_neg hv x z).fderiv

theorem h2_per1_perp_bdd {v : ℝ} (hv : 0 < v) (x : Ch N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖h2_per1 v (x - z)‖ * (1 + ‖h2_perp z‖) ≤ C := by
  obtain ⟨B, hB0, hB⟩ := h2_per_bounds (N := N) hv
  have hc : 0 < 1 / (4 * v) := by positivity
  set S : ℝ := 1 + ‖h2_perp x‖ with hS
  have hS0 : 0 ≤ S := by positivity
  refine ⟨B * S * (2 + 2 / (1 / (4 * v))), by positivity, fun z => ?_⟩
  set r : ℝ := ‖h2_perp (x - z)‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have hy : ‖h2_perp z‖ ≤ ‖h2_perp x‖ + r := by
    have : h2_perp z = h2_perp x - h2_perp (x - z) := by rw [h2_perp_sub]; abel
    rw [this]; exact norm_sub_le _ _
  have hg : 1 + ‖h2_perp z‖ ≤ S * (1 + r) := by
    nlinarith [mul_nonneg (norm_nonneg (h2_perp x)) hr0]
  calc ‖h2_per1 v (x - z)‖ * (1 + ‖h2_perp z‖) ≤ (B * Real.exp (-(1 / (4 * v)) * r ^ 2)) * (S * (1 + r)) :=
        mul_le_mul (hB (x - z)).2.1 hg (by positivity) (by positivity)
    _ = B * S * ((1 + r) * Real.exp (-(1 / (4 * v)) * r ^ 2)) := by ring
    _ ≤ B * S * (2 + 2 / (1 / (4 * v))) :=
        mul_le_mul_of_nonneg_left (h2_sup_mul_exp hc hr0) (by positivity)

theorem h2_test_per_sub {v : ℝ} (hv : 0 < v) (x : Ch N) : H2Test (fun z => h2_per v (x - z)) where
  smooth := (h2_contDiff_per hv).comp (contDiff_const.sub contDiff_id)
  periodic := fun z => h2_sub_periodic_y (f := h2_per v) (h2_per_periodic v) x z
  bdd := by
    obtain ⟨B, hB0, hB⟩ := h2_per_le (N := N) hv
    obtain ⟨C, hC0, hC⟩ := h2_per1_perp_bdd hv x
    refine ⟨max B (max C B), fun z => ⟨?_, ?_, ?_⟩⟩
    · rw [← Real.norm_eq_abs]; exact ((hB _).1).trans (le_max_left _ _)
    · rw [h2_fderiv_per_neg hv x, norm_neg]
      exact (hC z).trans (le_max_of_le_right (le_max_left _ _))
    · rw [h2_fderiv_fderiv_per_neg hv x z]
      exact ((hB _).2.2).trans (le_max_of_le_right (le_max_right _ _))

theorem h2_gen_per_sub {v : ℝ} (hv : 0 < v) (θ : ℝ) (U : Ch N → ℝ) (x z : Ch N) :
    h2_gen θ U (fun z => h2_per v (x - z)) z = h2_A θ v U x z := by
  unfold h2_gen h2_lap h2_A
  rw [h2_fderiv_per_neg hv x]
  have hg : gradient (fun z => h2_per v (x - z)) z = h2_dg (-(h2_per1 v (x - z))) := by
    show (InnerProductSpace.toDual ℝ (Ch N)).symm (fderiv ℝ (fun z => h2_per v (x - z)) z) = _
    rw [h2_fderiv_per_neg hv x]; rfl
  rw [hg, real_inner_comm, h2_dg_inner]
  have hl : ∑ k : Fin N, fderiv ℝ (fun z => -(h2_per1 v (x - z))) z (EuclideanSpace.single k 1) (EuclideanSpace.single k 1) =
      ∑ k, h2_per2 v (x - z) (h2_e k) (h2_e k) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(h2_hasFDerivAt_per1_neg hv x z).fderiv]; rfl
  rw [hl]
  simp only [neg_apply]
  ring

/-- `u_t(x) = u_0(x) + ∫_0^t ∫ A(x,y) dμ_s(y) ds`. -/
theorem h2_mu_time {θ v : ℝ} (hv : 0 < v) {U : Ch N → ℝ} {μ : ℝ → Measure (Ch N)} (hfp : H2WeakFP θ U μ)
    (x : Ch N) {t : ℝ} (ht : 0 ≤ t) :
    h2_mu v (μ t) x = h2_mu v (μ 0) x + ∫ s in Icc (0 : ℝ) t, ∫ y, h2_A θ v U x y ∂μ s := by
  have := hfp _ (h2_test_per_sub hv x) t ht
  simp_rw [h2_gen_per_sub hv θ U x] at this
  exact this

end HRS.MC.CepH2
