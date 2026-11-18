import HRS.MS.SA16JetConv

/-!
# S.A.16: convolution with a compactly supported `L¹` kernel commutes with coordinate derivatives

For `k ∈ L¹` supported in a ball and `u` smooth, `k ⋆ u` is smooth and `∂^α (k ⋆ u) = k ⋆ ∂^α u`.  Locally
`u` is replaced by a compactly supported cutoff, to which Mathlib's convolution calculus applies.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16
open HRS HRS.Whole HRS.Whole.AppendixA

section ConvDiff
variable {d : ℕ}

lemma sa16j_cutf_contDiff {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (R : ℝ) :
    ContDiff ℝ ∞ (sa16j_cutf d R f) := (sa16j_chi_contDiff d R).mul hf

lemma sa16j_cutf_support (f : Euc d → ℝ) {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (sa16j_cutf d R f) := (sa16j_chi_support d hR).mul_right

lemma sa16j_cutf_eq (f : Euc d → ℝ) {R : ℝ} (hR : 0 < R) {y : Euc d} (hy : ‖y‖ ≤ R) :
    sa16j_cutf d R f y = f y := by
  simp [sa16j_cutf, sa16j_chi_one d hR hy]

/-- convolution against a kernel -/
def sa16j_conv (k u : Euc d → ℝ) : Euc d → ℝ := fun x => ∫ z, k z * u (x - z)

/-- on a neighbourhood of `x₀` the convolution only sees a cutoff of `u` -/
lemma sa16j_conv_local {k : Euc d → ℝ} {R : ℝ} (hksupp : ∀ z, R < ‖z‖ → k z = 0) (u : Euc d → ℝ)
    (x₀ : Euc d) (hR : 0 ≤ R) :
    ∀ᶠ y in 𝓝 x₀, sa16j_conv k u y =
      (k ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] sa16j_cutf d (‖x₀‖ + R + 1) u) y := by
  have hball : Metric.ball x₀ 1 ∈ 𝓝 x₀ := Metric.ball_mem_nhds x₀ one_pos
  filter_upwards [hball] with y hy
  have hy' : ‖y‖ ≤ ‖x₀‖ + 1 := by
    have := norm_sub_le y x₀
    rw [Metric.mem_ball, dist_eq_norm] at hy
    linarith [norm_sub_norm_le y x₀, hy]
  unfold sa16j_conv
  rw [convolution_def]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [ContinuousLinearMap.mul_apply']
  by_cases hz : R < ‖z‖
  · rw [hksupp z hz]; simp
  · push Not at hz
    have : ‖y - z‖ ≤ ‖x₀‖ + R + 1 := by
      calc ‖y - z‖ ≤ ‖y‖ + ‖z‖ := norm_sub_le _ _
        _ ≤ ‖x₀‖ + R + 1 := by linarith
    rw [sa16j_cutf_eq u (by positivity) this]

lemma sa16j_conv_contDiff {k : Euc d → ℝ} {R : ℝ} (hksupp : ∀ z, R < ‖z‖ → k z = 0) (hR : 0 ≤ R)
    (hk1 : Integrable k) {u : Euc d → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (sa16j_conv k u) := by
  rw [contDiff_iff_contDiffAt]
  intro x₀
  have h1 : ContDiff ℝ ∞ (k ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
      sa16j_cutf d (‖x₀‖ + R + 1) u) :=
    (sa16j_cutf_support u (by positivity)).contDiff_convolution_right _ hk1.locallyIntegrable
      (sa16j_cutf_contDiff hu _)
  exact h1.contDiffAt.congr_of_eventuallyEq (sa16j_conv_local hksupp u x₀ hR)

lemma sa16j_conv_fderiv {k : Euc d → ℝ} {R : ℝ} (hksupp : ∀ z, R < ‖z‖ → k z = 0) (hR : 0 ≤ R)
    (hk1 : Integrable k) {u : Euc d → ℝ} (hu : ContDiff ℝ ∞ u) (x₀ v : Euc d) :
    fderiv ℝ (sa16j_conv k u) x₀ v = sa16j_conv k (fun y => fderiv ℝ u y v) x₀ := by
  set R' : ℝ := ‖x₀‖ + R + 1 with hR'
  have hR'0 : 0 < R' := by positivity
  set u' : Euc d → ℝ := sa16j_cutf d R' u with hu'
  have hcd : ContDiff ℝ 1 u' := (sa16j_cutf_contDiff hu R').of_le (by exact_mod_cast le_top)
  have hder := (sa16j_cutf_support u hR'0).hasFDerivAt_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) hk1.locallyIntegrable hcd x₀
  have hev : sa16j_conv k u =ᶠ[𝓝 x₀] (k ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] u') :=
    sa16j_conv_local hksupp u x₀ hR
  rw [hev.fderiv_eq, hder.fderiv, convolution_def]
  obtain ⟨B, hB⟩ : ∃ B, ∀ y, ‖fderiv ℝ u' y‖ ≤ B :=
    (hcd.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
      ((sa16j_cutf_support u hR'0).fderiv (𝕜 := ℝ))
  have hpre : ∀ (a : ℝ) (A : Euc d →L[ℝ] ℝ),
      (ContinuousLinearMap.mul ℝ ℝ).precompR (Euc d) a A = a • A := by
    intro a A; ext w; simp
  simp_rw [hpre]
  have hint : Integrable (fun t => k t • fderiv ℝ u' (x₀ - t)) volume := by
    refine Integrable.mono' (hk1.norm.mul_const B)
      (hk1.aestronglyMeasurable.smul
        ((hcd.continuous_fderiv one_ne_zero).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall fun t => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
  rw [ContinuousLinearMap.integral_apply hint v]
  unfold sa16j_conv
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  by_cases ht : R < ‖t‖
  · simp [hksupp t ht]
  · push Not at ht
    have hy : ‖x₀ - t‖ < R' := by
      calc ‖x₀ - t‖ ≤ ‖x₀‖ + ‖t‖ := norm_sub_le _ _
        _ < R' := by linarith
    have hloc : u' =ᶠ[𝓝 (x₀ - t)] u := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (show x₀ - t ∈ Metric.ball (0 : Euc d) R' by
        simpa using hy)] with y hy'
      exact sa16j_cutf_eq u hR'0 (by simpa using (mem_ball_zero_iff.1 hy').le)
    show (k t • fderiv ℝ u' (x₀ - t)) v = k t * (fderiv ℝ u (x₀ - t)) v
    rw [hloc.fderiv_eq]
    simp

lemma sa16j_pd_zero (idx : Fin 0 → Fin d) (f : Euc d → ℝ) (x : Euc d) : partialDeriv idx f x = f x := by
  unfold partialDeriv
  exact iteratedFDeriv_zero_apply _

lemma sa16j_pd_smooth {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) {j : ℕ} (idx : Fin j → Fin d) :
    ContDiff ℝ ∞ (partialDeriv idx f) := by
  unfold partialDeriv
  have h := hf.iteratedFDeriv_right (m := ∞) (i := j) (by simp)
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ
    (fun l => EuclideanSpace.single (idx l) (1 : ℝ))).contDiff.comp h

lemma sa16j_pd_succ {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) {j : ℕ} (idx : Fin (j + 1) → Fin d)
    (x : Euc d) :
    partialDeriv idx f x = fderiv ℝ (partialDeriv (fun l : Fin j => idx l.succ) f) x
      (EuclideanSpace.single (idx 0) (1 : ℝ)) := by
  have hD : DifferentiableAt ℝ (iteratedFDeriv ℝ j f) x :=
    (hf.differentiable_iteratedFDeriv (m := j) (by exact_mod_cast WithTop.coe_lt_top _)) x
  unfold partialDeriv
  rw [iteratedFDeriv_succ_apply_left]
  have := fderiv_continuousMultilinear_apply_const hD
    (fun l : Fin j => EuclideanSpace.single (idx l.succ) (1 : ℝ))
  rw [this]
  rfl

/-- coordinate derivatives of a convolution are convolutions of the coordinate derivatives -/
lemma sa16j_conv_pd {k : Euc d → ℝ} {R : ℝ} (hksupp : ∀ z, R < ‖z‖ → k z = 0) (hR : 0 ≤ R)
    (hk1 : Integrable k) :
    ∀ (j : ℕ) (idx : Fin j → Fin d) (u : Euc d → ℝ), ContDiff ℝ ∞ u →
      partialDeriv idx (sa16j_conv k u) = sa16j_conv k (partialDeriv idx u) := by
  intro j
  induction j with
  | zero =>
    intro idx u hu
    funext x
    rw [sa16j_pd_zero]
    unfold sa16j_conv
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [sa16j_pd_zero]
  | succ j ih =>
    intro idx u hu
    have hc := sa16j_conv_contDiff hksupp hR hk1 hu
    funext x
    rw [sa16j_pd_succ hc, ih (fun l : Fin j => idx l.succ) u hu,
      sa16j_conv_fderiv hksupp hR hk1 (sa16j_pd_smooth hu _) x]
    unfold sa16j_conv
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [sa16j_pd_succ hu]

end ConvDiff

end HRS.Whole.AppendixA.Phase2SA16
