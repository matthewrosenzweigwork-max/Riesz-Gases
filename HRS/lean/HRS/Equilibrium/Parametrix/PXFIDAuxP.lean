import HRS.Equilibrium.Parametrix.PXFIDAuxO

/-!
# Packet PX-FID, file P: bounds and slices of a smooth test kernel
-/

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal

noncomputable section

namespace HRS.Parx.PXFID

variable {d : ℕ} {s : ℝ}

theorem norm_rep_le (x : Torus d) : ‖Torus.rep x‖ ≤ d := by
  have h01 : ∀ i, 0 ≤ Torus.rep x i ∧ Torus.rep x i ≤ 1 := by
    intro i
    have := (AddCircle.equivIco (1 : ℝ) 0 (x i)).2
    simp only [Torus.rep]
    exact ⟨by simpa using this.1, by have := this.2; simp at this; linarith⟩
  have hsq : ‖Torus.rep x‖ ^ 2 ≤ d := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖Torus.rep x i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Real.norm_eq_abs, sq_abs]
          have := h01 i
          nlinarith
      _ = d := by simp
  by_cases hd : d = 0
  · subst hd
    have : ‖Torus.rep x‖ ^ 2 ≤ 0 := by simpa using hsq
    have h0 : ‖Torus.rep x‖ = 0 := by nlinarith [norm_nonneg (Torus.rep x)]
    simp [h0]
  · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hd
    nlinarith [norm_nonneg (Torus.rep x)]

theorem norm_rep_prod_le (x y : Torus d) : ‖(Torus.rep x, Torus.rep y)‖ ≤ d := by
  rw [Prod.norm_def]
  exact max_le (norm_rep_le x) (norm_rep_le y)

theorem exists_bounds_smooth2 {φ : Torus d → Torus d → ℝ} (hφ : ContDiff ℝ ∞ (lift2 φ)) :
    ∃ M : ℝ, ∀ x y : Torus d, |φ x y| ≤ M ∧ ‖fderiv ℝ (lift2 φ) (Torus.rep x, Torus.rep y)‖ ≤ M := by
  have hc1 : Continuous (lift2 φ) := hφ.continuous
  have hc2 : Continuous (fderiv ℝ (lift2 φ)) := hφ.continuous_fderiv (by simp)
  obtain ⟨C1, hC1⟩ := (isCompact_closedBall (0 : Euc d × Euc d) (d : ℝ)).exists_bound_of_continuousOn
    hc1.continuousOn
  obtain ⟨C2, hC2⟩ := (isCompact_closedBall (0 : Euc d × Euc d) (d : ℝ)).exists_bound_of_continuousOn
    hc2.continuousOn
  refine ⟨max C1 C2, fun x y => ?_⟩
  have hmem : (Torus.rep x, Torus.rep y) ∈ Metric.closedBall (0 : Euc d × Euc d) (d : ℝ) := by
    rw [mem_closedBall_zero_iff]; exact norm_rep_prod_le x y
  refine ⟨?_, ?_⟩
  · have := hC1 _ hmem
    have e : lift2 φ (Torus.rep x, Torus.rep y) = φ x y := by simp [lift2, Torus.mk_rep]
    rw [e, Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · exact (hC2 _ hmem).trans (le_max_right _ _)

theorem norm_gradFst_le_fderiv (φ : Torus d → Torus d → ℝ) (x y : Torus d)
    (h : DifferentiableAt ℝ (lift2 φ) (Torus.rep x, Torus.rep y)) :
    ‖gradFst φ x y‖ ≤ ‖fderiv ℝ (lift2 φ) (Torus.rep x, Torus.rep y)‖ := by
  have hn : ‖ContinuousLinearMap.inl ℝ (Euc d) (Euc d)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by simp)
  have h1 : ‖gradFst φ x y‖ = ‖fderiv ℝ (Torus.lift (fun z => φ z y)) (Torus.rep x)‖ := by
    unfold gradFst Torus.grad gradient
    exact LinearIsometryEquiv.norm_map _ _
  rw [h1, lift_slice_fst, fderiv_slice_diff (lift2 φ) (ContinuousLinearMap.inl ℝ (Euc d) (Euc d))
    (0, Torus.rep y) (by simpa using h)]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have : (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) (Torus.rep x) + (0, Torus.rep y) =
      (Torus.rep x, Torus.rep y) := by simp
  rw [this]
  calc ‖fderiv ℝ (lift2 φ) (Torus.rep x, Torus.rep y)‖ * ‖ContinuousLinearMap.inl ℝ (Euc d) (Euc d)‖
      ≤ ‖fderiv ℝ (lift2 φ) (Torus.rep x, Torus.rep y)‖ * 1 :=
        mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ = _ := mul_one _

theorem norm_gradSnd_le_fderiv (φ : Torus d → Torus d → ℝ) (x y : Torus d)
    (h : DifferentiableAt ℝ (lift2 φ) (Torus.rep x, Torus.rep y)) :
    ‖gradSnd φ x y‖ ≤ ‖fderiv ℝ (lift2 φ) (Torus.rep x, Torus.rep y)‖ := by
  have hn : ‖ContinuousLinearMap.inr ℝ (Euc d) (Euc d)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by simp)
  have h1 : ‖gradSnd φ x y‖ = ‖fderiv ℝ (Torus.lift (fun z => φ x z)) (Torus.rep y)‖ := by
    unfold gradSnd Torus.grad gradient
    exact LinearIsometryEquiv.norm_map _ _
  rw [h1, lift_slice_snd, fderiv_slice_diff (lift2 φ) (ContinuousLinearMap.inr ℝ (Euc d) (Euc d))
    (Torus.rep x, 0) (by simpa using h)]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have : (ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) (Torus.rep y) + (Torus.rep x, 0) =
      (Torus.rep x, Torus.rep y) := by simp
  rw [this]
  calc ‖fderiv ℝ (lift2 φ) (Torus.rep x, Torus.rep y)‖ * ‖ContinuousLinearMap.inr ℝ (Euc d) (Euc d)‖
      ≤ ‖fderiv ℝ (lift2 φ) (Torus.rep x, Torus.rep y)‖ * 1 :=
        mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ = _ := mul_one _

theorem isSmooth_slice_fst {φ : Torus d → Torus d → ℝ} (hφ : ContDiff ℝ ∞ (lift2 φ)) (y : Torus d) :
    Torus.IsSmooth (fun z => φ z y) := by
  unfold Torus.IsSmooth Torus.IsCk
  rw [lift_slice_fst]
  exact hφ.comp ((ContinuousLinearMap.inl ℝ (Euc d) (Euc d)).contDiff.add contDiff_const)

theorem isSmooth_slice_snd {φ : Torus d → Torus d → ℝ} (hφ : ContDiff ℝ ∞ (lift2 φ)) (x : Torus d) :
    Torus.IsSmooth (fun z => φ x z) := by
  unfold Torus.IsSmooth Torus.IsCk
  rw [lift_slice_snd]
  exact hφ.comp ((ContinuousLinearMap.inr ℝ (Euc d) (Euc d)).contDiff.add contDiff_const)

theorem measurable_of_smooth2 {φ : Torus d → Torus d → ℝ} (hφ : ContDiff ℝ ∞ (lift2 φ)) :
    Measurable (fun p : Torus d × Torus d => φ p.1 p.2) := by
  have : (fun p : Torus d × Torus d => φ p.1 p.2) =
      fun p => lift2 φ (Torus.rep p.1, Torus.rep p.2) := by
    funext p; simp [lift2, Torus.mk_rep]
  rw [this]
  exact hφ.continuous.measurable.comp (measurable_rep_prod d)

end HRS.Parx.PXFID

end
