import HRS.MS.SA16StrongLeib

/-!
# S.A.16: convolution with a compactly supported `L¹` kernel and finite regularity

Finite-order versions of `sa16j_conv_contDiff`, `sa16j_conv_fderiv`, `sa16j_pd_succ`, `sa16j_conv_pd`:
for `u ∈ C^N` and `k ∈ L¹` supported in a ball, `k ⋆ u ∈ C^N` and `∂^α (k ⋆ u) = k ⋆ ∂^α u` for `|α| ≤ N`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16
open HRS HRS.Whole HRS.Whole.AppendixA

section ConvN
variable {d : ℕ}

lemma sa16y_cutf_contDiffN {f : Euc d → ℝ} {N : ℕ} (hf : ContDiff ℝ N f) (R : ℝ) :
    ContDiff ℝ N (sa16j_cutf d R f) :=
  ((sa16j_chi_contDiff d R).of_le (by exact_mod_cast le_top)).mul hf

lemma sa16y_conv_contDiffN {k : Euc d → ℝ} {R : ℝ} (hksupp : ∀ z, R < ‖z‖ → k z = 0) (hR : 0 ≤ R)
    (hk1 : Integrable k) {N : ℕ} {u : Euc d → ℝ} (hu : ContDiff ℝ N u) :
    ContDiff ℝ N (sa16j_conv k u) := by
  rw [contDiff_iff_contDiffAt]
  intro x₀
  have h1 : ContDiff ℝ N (k ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
      sa16j_cutf d (‖x₀‖ + R + 1) u) :=
    (sa16j_cutf_support u (by positivity)).contDiff_convolution_right _ hk1.locallyIntegrable
      (sa16y_cutf_contDiffN hu _)
  exact h1.contDiffAt.congr_of_eventuallyEq (sa16j_conv_local hksupp u x₀ hR)

lemma sa16y_conv_fderivN {k : Euc d → ℝ} {R : ℝ} (hksupp : ∀ z, R < ‖z‖ → k z = 0) (hR : 0 ≤ R)
    (hk1 : Integrable k) {N : ℕ} (hN : 1 ≤ N) {u : Euc d → ℝ} (hu : ContDiff ℝ N u) (x₀ v : Euc d) :
    fderiv ℝ (sa16j_conv k u) x₀ v = sa16j_conv k (fun y => fderiv ℝ u y v) x₀ := by
  set R' : ℝ := ‖x₀‖ + R + 1 with hR'
  have hR'0 : 0 < R' := by positivity
  set u' : Euc d → ℝ := sa16j_cutf d R' u with hu'
  have hcd : ContDiff ℝ 1 u' := (sa16y_cutf_contDiffN hu R').of_le (by exact_mod_cast hN)
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

lemma sa16y_pd_succN {f : Euc d → ℝ} {N : ℕ} (hf : ContDiff ℝ N f) {j : ℕ} (hj : j + 1 ≤ N)
    (idx : Fin (j + 1) → Fin d) (x : Euc d) :
    partialDeriv idx f x = fderiv ℝ (partialDeriv (fun l : Fin j => idx l.succ) f) x
      (EuclideanSpace.single (idx 0) (1 : ℝ)) := by
  have hD : DifferentiableAt ℝ (iteratedFDeriv ℝ j f) x :=
    (hf.differentiable_iteratedFDeriv (m := j) (by exact_mod_cast Nat.lt_of_succ_le hj)) x
  unfold partialDeriv
  rw [iteratedFDeriv_succ_apply_left]
  have := fderiv_continuousMultilinear_apply_const hD
    (fun l : Fin j => EuclideanSpace.single (idx l.succ) (1 : ℝ))
  rw [this]
  rfl

lemma sa16y_pd_contDiffN {f : Euc d → ℝ} {j r : ℕ} (hf : ContDiff ℝ (j + r : ℕ) f) (idx : Fin j → Fin d) :
    ContDiff ℝ r (partialDeriv idx f) := by
  unfold partialDeriv
  have h := hf.iteratedFDeriv_right (m := r) (i := j) (by exact_mod_cast (by omega : r + j ≤ j + r))
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ
    (fun l => EuclideanSpace.single (idx l) (1 : ℝ))).contDiff.comp h

/-- coordinate derivatives of a convolution are convolutions of the coordinate derivatives -/
lemma sa16y_conv_pdN {k : Euc d → ℝ} {R : ℝ} (hksupp : ∀ z, R < ‖z‖ → k z = 0) (hR : 0 ≤ R)
    (hk1 : Integrable k) :
    ∀ (j r : ℕ) (idx : Fin j → Fin d) (u : Euc d → ℝ), ContDiff ℝ (j + r : ℕ) u →
      partialDeriv idx (sa16j_conv k u) = sa16j_conv k (partialDeriv idx u) := by
  intro j
  induction j with
  | zero =>
    intro r idx u hu
    funext x
    rw [sa16j_pd_zero]
    unfold sa16j_conv
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [sa16j_pd_zero]
  | succ j ih =>
    intro r idx u hu
    have hu' : ContDiff ℝ (j + (r + 1) : ℕ) u := by
      have : j + 1 + r = j + (r + 1) := by omega
      rwa [this] at hu
    have hc := sa16y_conv_contDiffN hksupp hR hk1 hu
    funext x
    rw [sa16y_pd_succN hc (by omega) idx x, ih (r + 1) (fun l : Fin j => idx l.succ) u hu',
      sa16y_conv_fderivN hksupp hR hk1 (N := r + 1) (by omega)
        (sa16y_pd_contDiffN hu' _) x]
    unfold sa16j_conv
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    show k z * _ = k z * partialDeriv idx u (x - z)
    rw [sa16y_pd_succN (N := j + 1 + r) hu (by omega) idx (x - z)]

end ConvN

end HRS.Whole.AppendixA.Phase2SA16
