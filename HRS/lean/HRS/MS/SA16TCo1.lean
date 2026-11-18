import HRS.MS.SA16StrongApprox
import HRS.MS.SA16StrongSL4

/-!
# S.A.16 (SA16T) Co1: derivatives of a mollification fall on the kernel

For `k ∈ C_c^∞` and `u` merely continuous, `∂^α (k ⋆ u) = (∂^α k) ⋆ u`.  (The companion statement with the derivative on `u`
is `sa16y_conv_pdN`.)  This is what gives continuity in a parameter of the derivatives of a mollified family from
continuity of the family itself.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16

section Co1
variable {d : ℕ}

lemma sa16t_conv_smooth {k : Euc d → ℝ} (hk : IsCcInfty k) {u : Euc d → ℝ} (hu : Continuous u) :
    ContDiff ℝ ∞ (sa16j_conv k u) := by
  have : sa16j_conv k u = fun x => (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x := by
    funext x; exact sa16y_conv_eq_convolution _ _ x
  rw [this]
  exact hk.2.contDiff_convolution_left _ hk.1 hu.locallyIntegrable

lemma sa16t_conv_fderiv_kernel {k : Euc d → ℝ} (hk : ContDiff ℝ ∞ k) (hks : HasCompactSupport k)
    {u : Euc d → ℝ} (hu : Continuous u) (x v : Euc d) :
    fderiv ℝ (sa16j_conv k u) x v = ∫ z, fderiv ℝ k z v * u (x - z) := by
  have hconv : sa16j_conv k u = fun x => (k ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] u) x := by
    funext y; exact sa16y_conv_eq_convolution k u y
  have hk1 : ContDiff ℝ 1 k := hk.of_le (by exact_mod_cast le_top)
  have hder := hks.hasFDerivAt_convolution_left (μ := (volume : Measure (Euc d))) (ContinuousLinearMap.mul ℝ ℝ) hk1 hu.locallyIntegrable x
  rw [hconv, hder.fderiv, convolution_def]
  have hcd : Continuous (fderiv ℝ k) := hk1.continuous_fderiv one_ne_zero
  have hint : Integrable (fun z => (((ContinuousLinearMap.mul ℝ ℝ).precompL (Euc d)) (fderiv ℝ k z)) (u (x - z))) volume := by
    have h1 : Continuous (fun z => (((ContinuousLinearMap.mul ℝ ℝ).precompL (Euc d)) (fderiv ℝ k z)) (u (x - z))) :=
      (((ContinuousLinearMap.mul ℝ ℝ).precompL (Euc d)).continuous.comp hcd).clm_apply
        (hu.comp (continuous_const.sub continuous_id))
    refine h1.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (hks.fderiv (𝕜 := ℝ)).isCompact (fun z hz => ?_)
    have : fderiv ℝ k z = 0 := image_eq_zero_of_notMem_tsupport hz
    simp [this]
  rw [ContinuousLinearMap.integral_apply hint v]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp

lemma sa16t_pd_conv_kernel {k : Euc d → ℝ} (hk : IsCcInfty k) {u : Euc d → ℝ} (hu : Continuous u) :
    ∀ (j : ℕ) (idx : Fin j → Fin d) (x : Euc d),
      partialDeriv idx (sa16j_conv k u) x = ∫ z, partialDeriv idx k z * u (x - z) := by
  intro j
  induction j with
  | zero =>
    intro idx x
    rw [sa16j_pd_zero]
    unfold sa16j_conv
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [sa16j_pd_zero]
  | succ j ih =>
    intro idx x
    have hsm : ContDiff ℝ ∞ (sa16j_conv k u) := sa16t_conv_smooth hk hu
    rw [sa16j_pd_succ hsm idx x]
    have hfun : partialDeriv (fun l : Fin j => idx l.succ) (sa16j_conv k u) =
        sa16j_conv (partialDeriv (fun l : Fin j => idx l.succ) k) u := by
      funext y; rw [ih]; rfl
    rw [hfun]
    have hk' := sa16s_cc_partialDeriv hk (fun l : Fin j => idx l.succ)
    rw [sa16t_conv_fderiv_kernel hk'.1 hk'.2 hu]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    show _ * _ = _ * _
    rw [sa16j_pd_succ hk.1 idx z]

end Co1

end HRS.Whole.AppendixA.Phase2SA16R
