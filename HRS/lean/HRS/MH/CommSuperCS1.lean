import HRS.MH.CommSuperDefs
import HRS.Stochastic.Particle

/-!
# CS1: local form of the periodic kernel and force (packet `kernel_local`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MH.CommSuper

variable {d N : ℕ} {s : ℝ}

theorem cs1_kernel_zero {d : ℕ} {s : ℝ} (hs : s = 0) (x : Euc d) :
    HRS.Whole.rieszKernel d s x = -Real.log ‖x‖ := by
  unfold HRS.Whole.rieszKernel
  rw [if_pos hs]

theorem cs1_kernel_pos {d : ℕ} {s : ℝ} (hs : s ≠ 0) (x : Euc d) :
    HRS.Whole.rieszKernel d s x = ‖x‖ ^ (-s) := by
  unfold HRS.Whole.rieszKernel
  rw [if_neg hs]

theorem cs1_grad_id {d : ℕ} {s : ℝ} (hs0 : 0 ≤ s) {x : Euc d} (hx : x ≠ 0) :
    HRS.Whole.rieszKernelGrad d s x = HRS.eucRieszGrad s x := by
  unfold HRS.Whole.rieszKernelGrad
  rcases hs0.eq_or_lt with h0 | hpos
  · subst h0
    have hfun : HRS.Whole.rieszKernel d 0 = fun z : Euc d => -Real.log ‖z‖ := by
      funext z
      exact cs1_kernel_zero rfl z
    rw [hfun]
    exact (HRS.hasGradientAt_neg_log_norm hx).gradient
  · have hfun : HRS.Whole.rieszKernel d s = fun z : Euc d => ‖z‖ ^ (-s) := by
      funext z
      exact cs1_kernel_pos hpos.ne' z
    rw [hfun]
    exact (HRS.hasGradientAt_norm_rpow_neg hpos hx).gradient

theorem cs1_D1_eq {d : ℕ} (s : ℝ) (x : Euc d) :
    HRS.KernelD1.eucRieszGrad s x = HRS.eucRieszGrad s x := rfl

/-- A smooth function on the torus is Lipschitz at `0` and bounded on a Euclidean ball. -/
theorem cs1_smooth_bounds {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : HRS.Torus d → E} (hφ : HRS.Torus.IsSmooth φ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ x : Euc d, ‖x‖ < δ → ‖φ (HRS.Torus.mk x) - φ (HRS.Torus.mk 0)‖ ≤ M * ‖x‖) ∧
      (∀ x : Euc d, ‖x‖ < δ → ‖φ (HRS.Torus.mk x)‖ ≤ M) := by
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Euc d => φ (HRS.Torus.mk x)) := hφ
  have hdiff : Differentiable ℝ (fun x : Euc d => φ (HRS.Torus.mk x)) :=
    hc.differentiable (by simp)
  have hcf : Continuous (fderiv ℝ (fun x : Euc d => φ (HRS.Torus.mk x))) :=
    hc.continuous_fderiv (by simp)
  have hcf0 : Continuous (fun x : Euc d => φ (HRS.Torus.mk x)) := hdiff.continuous
  obtain ⟨C1, hC1⟩ := (isCompact_closedBall (0 : Euc d) δ).exists_bound_of_continuousOn
    hcf.continuousOn
  obtain ⟨C2, hC2⟩ := (isCompact_closedBall (0 : Euc d) δ).exists_bound_of_continuousOn
    hcf0.continuousOn
  refine ⟨|C1| + |C2|, by positivity, ?_, ?_⟩
  · intro x hx
    have hxmem : x ∈ Metric.closedBall (0 : Euc d) δ := mem_closedBall_zero_iff.mpr hx.le
    have h0mem : (0 : Euc d) ∈ Metric.closedBall (0 : Euc d) δ :=
      mem_closedBall_zero_iff.mpr (by rw [norm_zero]; exact hδ.le)
    have key := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (s := Metric.closedBall (0 : Euc d) δ) (C := |C1| + |C2|)
      (fun y _ => hdiff y)
      (fun y hy => (hC1 y hy).trans (by linarith [le_abs_self C1, abs_nonneg C2]))
      (convex_closedBall (0 : Euc d) δ) h0mem hxmem
    simpa using key
  · intro x hx
    have hxmem : x ∈ Metric.closedBall (0 : Euc d) δ := mem_closedBall_zero_iff.mpr hx.le
    exact (hC2 x hxmem).trans (by linarith [le_abs_self C2, abs_nonneg C1])

theorem cs1_assemble {d : ℕ} {s : ℝ} (rv : HRS.Torus d → ℝ) (rg : HRS.Torus d → Euc d)
    {δv δg : ℝ} (hδv : 0 < δv) (hδg : 0 < δg) (hrv : HRS.Torus.IsSmooth rv)
    (hrg : HRS.Torus.IsSmooth rg)
    (hval : ∀ x : Euc d, ‖x‖ < δv → x ≠ 0 →
      HRS.periodicRiesz d s (HRS.Torus.mk x) = HRS.Whole.rieszKernel d s x + rv (HRS.Torus.mk x))
    (hgrad : ∀ x : Euc d, ‖x‖ < δg → x ≠ 0 →
      HRS.periodicRieszGrad d s (HRS.Torus.mk x) =
        HRS.Whole.rieszKernelGrad d s x + rg (HRS.Torus.mk x)) :
    ∃ (δ M : ℝ) (r : Euc d → ℝ) (R : Euc d → Euc d), 0 < δ ∧ δ ≤ 1 / 8 ∧ 0 ≤ M ∧
      (∀ x : Euc d, ‖x‖ < δ → |r x - r 0| ≤ M * ‖x‖) ∧
      (∀ x : Euc d, ‖x‖ < δ → ‖R x‖ ≤ M) ∧
      ∀ x : Euc d, ‖x‖ < δ → x ≠ 0 →
        HRS.periodicRiesz d s (HRS.Torus.mk x) = HRS.Whole.rieszKernel d s x + r x ∧
        HRS.periodicRieszGrad d s (HRS.Torus.mk x) = HRS.Whole.rieszKernelGrad d s x + R x := by
  set δ := min (min δv δg) (1 / 8) with hδdef
  have hδ0 : 0 < δ := lt_min (lt_min hδv hδg) (by norm_num)
  have hδ1 : δ ≤ 1 / 8 := min_le_right _ _
  have hδv' : δ ≤ δv := (min_le_left _ _).trans (min_le_left _ _)
  have hδg' : δ ≤ δg := (min_le_left _ _).trans (min_le_right _ _)
  obtain ⟨M1, hM1, hL1, _⟩ := cs1_smooth_bounds (E := ℝ) hrv hδ0
  obtain ⟨M2, hM2, _, hB2⟩ := cs1_smooth_bounds (E := Euc d) hrg hδ0
  refine ⟨δ, M1 + M2, fun x => rv (HRS.Torus.mk x), fun x => rg (HRS.Torus.mk x),
    hδ0, hδ1, by linarith, ?_, ?_, ?_⟩
  · intro x hx
    have h := hL1 x hx
    rw [Real.norm_eq_abs] at h
    have h2 := mul_le_mul_of_nonneg_right (by linarith : M1 ≤ M1 + M2) (norm_nonneg x)
    exact h.trans h2
  · intro x hx
    have h := hB2 x hx
    exact h.trans (by linarith)
  · intro x hx hx0
    exact ⟨hval x (lt_of_lt_of_le hx hδv') hx0, hgrad x (lt_of_lt_of_le hx hδg') hx0⟩

theorem kernel_local_proof (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ (δ M : ℝ) (r : Euc d → ℝ) (R : Euc d → Euc d), 0 < δ ∧ δ ≤ 1 / 8 ∧ 0 ≤ M ∧
      (∀ x : Euc d, ‖x‖ < δ → |r x - r 0| ≤ M * ‖x‖) ∧
      (∀ x : Euc d, ‖x‖ < δ → ‖R x‖ ≤ M) ∧
      ∀ x : Euc d, ‖x‖ < δ → x ≠ 0 →
        periodicRiesz d s (Torus.mk x) = Whole.rieszKernel d s x + r x ∧
        periodicRieszGrad d s (Torus.mk x) = Whole.rieszKernelGrad d s x + R x := by
  by_cases h1 : d = 1
  · subst h1
    have hs1 : s < 1 := by simpa using hsd
    rcases hs0.eq_or_lt with h0 | hpos
    · subst h0
      obtain ⟨rv, δv, hδv, hrv, hval⟩ := HRS.periodicLog_local_singularity_d1
      obtain ⟨rg, δg, hδg, hrg, _, hgrad⟩ :=
        HRS.periodicRieszGrad_local_singularity_d1 (le_refl 0) hs1
      refine cs1_assemble rv rg hδv hδg hrv hrg (fun x hx hx0 => ?_) (fun x hx hx0 => ?_)
      · rw [cs1_kernel_zero (d := 1) rfl x]
        exact hval x hx hx0
      · rw [hgrad x hx hx0, cs1_D1_eq, cs1_grad_id (le_refl 0) hx0]
    · obtain ⟨rv, δv, hδv, hrv, hval⟩ := HRS.periodicRiesz_local_singularity_d1 hpos hs1
      obtain ⟨rg, δg, hδg, hrg, _, hgrad⟩ :=
        HRS.periodicRieszGrad_local_singularity_d1 hs0 hs1
      refine cs1_assemble rv rg hδv hδg hrv hrg (fun x hx hx0 => ?_) (fun x hx hx0 => ?_)
      · rw [cs1_kernel_pos (d := 1) hpos.ne' x]
        exact hval x hx hx0
      · rw [hgrad x hx hx0, cs1_D1_eq, cs1_grad_id hs0 hx0]
  · have hd2 : 2 ≤ d := by omega
    rcases hs0.eq_or_lt with h0 | hpos
    · subst h0
      obtain ⟨rv, δv, hδv, hrv, hval⟩ := HRS.periodicLog_local_singularity hd2
      obtain ⟨rg, δg, hδg, hrg, _, hgrad⟩ :=
        HRS.periodicRieszGrad_local_singularity hd2 (le_refl 0) hsd
      refine cs1_assemble rv rg hδv hδg hrv hrg (fun x hx hx0 => ?_) (fun x hx hx0 => ?_)
      · rw [cs1_kernel_zero (d := d) rfl x]
        exact hval x hx hx0
      · rw [hgrad x hx hx0, cs1_grad_id (le_refl 0) hx0]
    · obtain ⟨rv, δv, hδv, hrv, hval⟩ := HRS.periodicRiesz_local_singularity hd2 hpos hsd
      obtain ⟨rg, δg, hδg, hrg, _, hgrad⟩ :=
        HRS.periodicRieszGrad_local_singularity hd2 hs0 hsd
      refine cs1_assemble rv rg hδv hδg hrv hrg (fun x hx hx0 => ?_) (fun x hx hx0 => ?_)
      · rw [cs1_kernel_pos (d := d) hpos.ne' x]
        exact hval x hx hx0
      · rw [hgrad x hx hx0, cs1_grad_id hs0 hx0]

end HRS.MH.CommSuper
