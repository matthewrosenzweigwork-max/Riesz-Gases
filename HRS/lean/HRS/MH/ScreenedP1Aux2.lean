import HRS.MH.ScreenedP1Aux1
import HRS.MH.ScreenedK3
import HRS.MH.ScreenedK4Aux1

/-!
# Helpers for packet P1 (`screened_pairing_lt`): a.e. measurability of `a ψ` from `IsGradKernelRep`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

/-- The Riesz gradient kernel is negative in the `i`-th coordinate on the half-space `z_i > 0`. -/
lemma p1_kernel_comp_neg {s : ℝ} (hs0 : 0 ≤ s) (i : Fin d) {z : Euc d} (hz : 0 < z i) :
    rieszKernelGrad d s z i < 0 := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  have hσ : 0 < movtr_sigma s := by
    unfold movtr_sigma
    split_ifs with h
    · norm_num
    · exact lt_of_le_of_ne hs0 (Ne.symm h)
  have hn : 0 < ‖z‖ ^ (-s - 2) := Real.rpow_pos_of_pos (norm_pos_iff.2 hz0) _
  rw [movtr_rieszKernelGrad_eq s hz0]
  simp only [PiLp.smul_apply, smul_eq_mul]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos hσ hn)) hz

/-- A nonnegative Schwartz bump, nonzero somewhere, supported in the half-space `{x_i > k}`. -/
lemma p1_bump (k : ℕ) (i : Fin d) :
    ∃ φ : SchwartzMap (Euc d) ℝ, (∀ x, 0 ≤ φ x) ∧ (∀ x, φ x ≠ 0 → (k : ℝ) < x i) ∧
      ∃ x0 : Euc d, φ x0 ≠ 0 := by
  let c : ContDiffBump (EuclideanSpace.single i ((k : ℝ) + 1) : Euc d) :=
    ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  have hg : ContDiff ℝ ∞ (c : Euc d → ℝ) := c.contDiff
  have hgc : HasCompactSupport (c : Euc d → ℝ) := c.hasCompactSupport
  obtain ⟨φ, hφ⟩ : ∃ φ : SchwartzMap (Euc d) ℝ, ⇑φ = c := ⟨hgc.toSchwartzMap hg, rfl⟩
  have hφx : ∀ x, φ x = c x := fun x => congrFun hφ x
  refine ⟨φ, fun x => ?_, fun x hx => ?_, EuclideanSpace.single i ((k : ℝ) + 1), ?_⟩
  · rw [hφx]; exact c.nonneg
  · rw [hφx] at hx
    have hsupp : x ∈ Function.support (c : Euc d → ℝ) := hx
    have hr : c.rOut = 1 / 2 := rfl
    rw [c.support_eq, Metric.mem_ball, dist_eq_norm, hr] at hsupp
    have h1 : ‖(x - EuclideanSpace.single i ((k : ℝ) + 1)) i‖ ≤ ‖x - EuclideanSpace.single i ((k : ℝ) + 1)‖ :=
      PiLp.norm_apply_le _ i
    have h2 : (x - EuclideanSpace.single i ((k : ℝ) + 1)) i = x i - ((k : ℝ) + 1) := by
      simp [EuclideanSpace.single_apply]
    rw [h2, Real.norm_eq_abs] at h1
    have h3 := abs_lt.mp (lt_of_le_of_lt h1 hsupp)
    linarith [h3.1]
  · rw [hφx]
    have hmem : (EuclideanSpace.single i ((k : ℝ) + 1) : Euc d) ∈
        Metric.closedBall (EuclideanSpace.single i ((k : ℝ) + 1) : Euc d) c.rIn :=
      Metric.mem_closedBall_self c.rIn_pos.le
    rw [c.one_of_mem_closedBall hmem]
    norm_num

/-- The convolution `g * ∂_iφ` is strictly positive on `{y_i < k}` for the bump of `p1_bump`. -/
lemma p1_conv_pos {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) (i : Fin d) (k : ℕ)
    (φ : SchwartzMap (Euc d) ℝ) (hφnn : ∀ x, 0 ≤ φ x) (hφsupp : ∀ x, φ x ≠ 0 → (k : ℝ) < x i)
    (x0 : Euc d) (hx0 : φ x0 ≠ 0) (y : Euc d) (hy : y i < k) :
    0 < HRS.Whole.convFun (rieszKernel d s) (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) y := by
  obtain ⟨hint, heq⟩ := gk_weak_proof hd hs0 hs1 i φ y
  have hpos : ∀ x, φ x ≠ 0 → 0 < x i - y i := fun x hx => by
    have := hφsupp x hx
    linarith
  have hf_nonneg : 0 ≤ fun x => -(rieszKernelGrad d s (x - y) i * φ x) := by
    intro x
    by_cases hφ0 : φ x = 0
    · simp [hφ0]
    · have hK : rieszKernelGrad d s (x - y) i < 0 := by
        apply p1_kernel_comp_neg hs0 i
        rw [PiLp.sub_apply]
        exact hpos x hφ0
      have := hφnn x
      show 0 ≤ -(rieszKernelGrad d s (x - y) i * φ x)
      nlinarith
  have hfi : Integrable (fun x => -(rieszKernelGrad d s (x - y) i * φ x)) volume := hint.neg
  have hopen : IsOpen {x : Euc d | φ x ≠ 0} :=
    isOpen_ne_fun φ.continuous continuous_const
  have hsub : {x : Euc d | φ x ≠ 0} ⊆ Function.support (fun x => -(rieszKernelGrad d s (x - y) i * φ x)) := by
    intro x hx
    have hx' : φ x ≠ 0 := hx
    have hpx : 0 < φ x := lt_of_le_of_ne (hφnn x) (Ne.symm hx')
    have hK : rieszKernelGrad d s (x - y) i < 0 := by
      apply p1_kernel_comp_neg hs0 i
      rw [PiLp.sub_apply]
      exact hpos x hx'
    show -(rieszKernelGrad d s (x - y) i * φ x) ≠ 0
    nlinarith
  have hmpos : 0 < volume {x : Euc d | φ x ≠ 0} := hopen.measure_pos volume ⟨x0, hx0⟩
  have hI : 0 < ∫ x, -(rieszKernelGrad d s (x - y) i * φ x) :=
    (integral_pos_iff_support_of_nonneg hf_nonneg hfi).2 (lt_of_lt_of_le hmpos (measure_mono hsub))
  rw [integral_neg] at hI
  rw [heq] at hI
  linarith

/-- An `IsGradKernelRep` pair has an a.e.-strongly measurable first argument. -/
lemma p1_aesm_of_rep {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) (i : Fin d)
    {v u : Euc d → ℝ} (h : IsGradKernelRep d s i v u) : AEStronglyMeasurable v volume := by
  have key : ∀ k : ℕ, AEStronglyMeasurable v (volume.restrict {y : Euc d | y i < k}) := by
    intro k
    obtain ⟨φ, hφnn, hφsupp, x0, hx0⟩ := p1_bump k i
    have hΘeq : (fun y : Euc d => HRS.Whole.convFun (rieszKernel d s) (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) y)
        = fun y => -∫ x, rieszKernelGrad d s (x - y) i * φ x := by
      funext y
      rw [(gk_weak_proof hd hs0 hs1 i φ y).2, neg_neg]
    have hΘm : AEStronglyMeasurable
        (fun y : Euc d => HRS.Whole.convFun (rieszKernel d s) (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) y)
        volume := by
      rw [hΘeq]
      have hF : AEStronglyMeasurable (fun p : Euc d × Euc d => rieszKernelGrad d s (p.2 - p.1) i * φ p.2)
          (volume.prod volume) := by
        apply Measurable.aestronglyMeasurable
        exact ((k4_comp_measurable s i).comp (measurable_snd.sub measurable_fst)).mul
          (φ.continuous.measurable.comp measurable_snd)
      exact hF.integral_prod_right'.neg
    have hUo : IsOpen {y : Euc d | y i < k} :=
      isOpen_lt (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous continuous_const
    have hUm : MeasurableSet {y : Euc d | y i < k} := hUo.measurableSet
    have hvΘ : Integrable (fun y => v y * HRS.Whole.convFun (rieszKernel d s)
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) y) volume := (h φ).2.1
    have hinvm : AEStronglyMeasurable (fun y : Euc d => (HRS.Whole.convFun (rieszKernel d s)
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) y)⁻¹) (volume.restrict {y : Euc d | y i < k}) :=
      (hΘm.restrict.aemeasurable.inv).aestronglyMeasurable
    have hprod : AEStronglyMeasurable (fun y : Euc d => v y * HRS.Whole.convFun (rieszKernel d s)
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) y * (HRS.Whole.convFun (rieszKernel d s)
        (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) y)⁻¹) (volume.restrict {y : Euc d | y i < k}) :=
      hvΘ.aestronglyMeasurable.restrict.mul hinvm
    refine hprod.congr ?_
    filter_upwards [ae_restrict_mem hUm] with y hy
    have hyk : y i < k := hy
    exact mul_inv_cancel_right₀
      (p1_conv_pos hd hs0 hs1 i k φ hφnn hφsupp x0 hx0 y hyk).ne' (v y)
  have hU : (⋃ k : ℕ, {y : Euc d | y i < k}) = univ := by
    ext y
    simp only [mem_iUnion, mem_setOf_eq, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt (y i)
    exact ⟨n, hn⟩
  have hall := (aestronglyMeasurable_iUnion_iff (μ := volume) (f := v)
    (s := fun k : ℕ => {y : Euc d | y i < k})).2 key
  rw [hU, Measure.restrict_univ] at hall
  exact hall

end HRS.MH.Screened
