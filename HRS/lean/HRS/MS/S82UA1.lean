import HRS.MS.S82TB
import HRS.MS.S82TJ
import HRS.MS.S82P2Cent7
import HRS.MS.S82QRows2

/-!
# S8.2 A01 (S82U): gradient differences of the pair corrector (Hessian on a ball, scalar radial inequality)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82U
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2 HRS.MS.S82T

lemma u_jb_ge_one {d : ℕ} (x : Euc d) : 1 ≤ jbracket x := HRS.MS.S82N.s82n_jb_one_le x

lemma u_jb_rpow_ge_one {d : ℕ} {M : ℝ} (hM : 0 ≤ M) (x : Euc d) : 1 ≤ jbracket x ^ M :=
  Real.one_le_rpow (u_jb_ge_one x) hM

lemma u_jb_rpow_pos {d : ℕ} (M : ℝ) (x : Euc d) : 0 < jbracket x ^ M :=
  Real.rpow_pos_of_pos (HRS.MS.S82N.s82n_jb_pos x) _

/-- Mean value bound for `x ↦ ∇_x Φ(x,w)` from a Hessian bound on a ball. -/
lemma u_grad_lip {d : ℕ} (Φ : Euc d × Euc d → ℝ)
    (hΦ : ContDiffOn ℝ 2 Φ {p | p.1 ≠ p.2}) (u v w : Euc d) (B : ℝ)
    (hw : ∀ p ∈ Metric.closedBall u ‖u - v‖, p ≠ w)
    (hB : ∀ p ∈ Metric.closedBall u ‖u - v‖, ‖iteratedFDeriv ℝ 2 Φ (p, w)‖ ≤ B) :
    ‖(InnerProductSpace.toDual ℝ (Euc d)).symm
        ((fderiv ℝ Φ (u, w)).comp (ContinuousLinearMap.inl ℝ (Euc d) (Euc d))) -
      (InnerProductSpace.toDual ℝ (Euc d)).symm
        ((fderiv ℝ Φ (v, w)).comp (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)))‖ ≤ B * ‖u - v‖ := by
  set gt : Euc d → Euc d := fun x => (InnerProductSpace.toDual ℝ (Euc d)).symm
      ((fderiv ℝ Φ (x, w)).comp (ContinuousLinearMap.inl ℝ (Euc d) (Euc d))) with hgt
  change ‖gt u - gt v‖ ≤ B * ‖u - v‖
  set Δ := gt u - gt v with hΔ
  have hopen : IsOpen {p : Euc d × Euc d | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
  have hball : Convex ℝ (Metric.closedBall u ‖u - v‖) := convex_closedBall _ _
  have hum : u ∈ Metric.closedBall u ‖u - v‖ := Metric.mem_closedBall_self (norm_nonneg _)
  have hvm : v ∈ Metric.closedBall u ‖u - v‖ := by
    rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
  -- scalar function f x = fderiv Φ (x,w) (Δ, 0)
  have hinner : ∀ x, inner ℝ (gt x) Δ = fderiv ℝ Φ (x, w) (Δ, 0) := by
    intro x
    rw [hgt]
    simp only [InnerProductSpace.toDual_symm_apply]
    simp
  have hderiv : ∀ x ∈ Metric.closedBall u ‖u - v‖, HasFDerivAt
      (fun x' : Euc d => fderiv ℝ Φ (x', w) (Δ, 0))
      (((fderiv ℝ (fderiv ℝ Φ) (x, w)).comp (ContinuousLinearMap.inl ℝ (Euc d) (Euc d))).flip (Δ, 0)) x := by
    intro x hx
    have hxw : (x, w) ∈ {p : Euc d × Euc d | p.1 ≠ p.2} := hw x hx
    have hc2 : ContDiffAt ℝ 2 Φ (x, w) := hΦ.contDiffAt (hopen.mem_nhds hxw)
    have h1 : DifferentiableAt ℝ (fderiv ℝ Φ) (x, w) :=
      (hc2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    have h2 : HasFDerivAt (fun x' : Euc d => (x', w)) (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) x :=
      (hasFDerivAt_id x).prodMk (hasFDerivAt_const w x)
    have h3 : HasFDerivAt (fun x' : Euc d => fderiv ℝ Φ (x', w))
        ((fderiv ℝ (fderiv ℝ Φ) (x, w)).comp (ContinuousLinearMap.inl ℝ (Euc d) (Euc d))) x :=
      h1.hasFDerivAt.comp x h2
    have h4 := h3.clm_apply (hasFDerivAt_const ((Δ, (0 : Euc d))) x)
    simpa using h4
  have hbound : ∀ x ∈ Metric.closedBall u ‖u - v‖,
      ‖((fderiv ℝ (fderiv ℝ Φ) (x, w)).comp (ContinuousLinearMap.inl ℝ (Euc d) (Euc d))).flip (Δ, 0)‖ ≤
        B * ‖Δ‖ := by
    intro x hx
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB u hum)
    have hxw : (x, w) ∈ {p : Euc d × Euc d | p.1 ≠ p.2} := hw x hx
    have hc2 : ContDiffAt ℝ 2 Φ (x, w) := hΦ.contDiffAt (hopen.mem_nhds hxw)
    have hH : ‖fderiv ℝ (fderiv ℝ Φ) (x, w)‖ ≤ B := by
      have e := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := Φ) (x := (x, w)) (n := 1)
      rw [norm_iteratedFDeriv_one] at e
      rw [e]; exact hB x hx
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hB0 (norm_nonneg _)) fun h => ?_
    simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply]
    have h5 : ‖(fderiv ℝ (fderiv ℝ Φ) (x, w)) (ContinuousLinearMap.inl ℝ (Euc d) (Euc d) h) (Δ, 0)‖ ≤
        ‖fderiv ℝ (fderiv ℝ Φ) (x, w)‖ * ‖ContinuousLinearMap.inl ℝ (Euc d) (Euc d) h‖ * ‖((Δ, (0 : Euc d)))‖ := by
      calc _ ≤ ‖(fderiv ℝ (fderiv ℝ Φ) (x, w)) (ContinuousLinearMap.inl ℝ (Euc d) (Euc d) h)‖ *
            ‖((Δ, (0 : Euc d)))‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ _ := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
    have h6 : ‖ContinuousLinearMap.inl ℝ (Euc d) (Euc d) h‖ = ‖h‖ := by
      simp [Prod.norm_def]
    have h7 : ‖((Δ, (0 : Euc d)))‖ = ‖Δ‖ := by simp [Prod.norm_def]
    rw [h6, h7] at h5
    calc _ ≤ _ := h5
      _ ≤ B * ‖h‖ * ‖Δ‖ := by gcongr
      _ = B * ‖Δ‖ * ‖h‖ := by ring
  have hmv := hball.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun x' : Euc d => fderiv ℝ Φ (x', w) (Δ, 0))
    (fun x hx => (hderiv x hx).hasFDerivWithinAt) hbound hvm hum
  have h1 : fderiv ℝ Φ (u, w) (Δ, 0) - fderiv ℝ Φ (v, w) (Δ, 0) = ‖Δ‖ ^ 2 := by
    rw [← hinner, ← hinner, ← inner_sub_left, real_inner_self_eq_norm_sq]
  have h2 := hmv
  rw [Real.norm_eq_abs] at h2
  have h3 : ‖Δ‖ ^ 2 ≤ B * ‖Δ‖ * ‖u - v‖ := by
    rw [h1, abs_of_nonneg (sq_nonneg ‖Δ‖)] at h2
    exact h2
  by_cases hz : ‖Δ‖ = 0
  · rw [hz]; exact mul_nonneg ((norm_nonneg _).trans (hB u hum)) (norm_nonneg _)
  · have hpos : 0 < ‖Δ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith [h3]

end HRS.MS.S82U
