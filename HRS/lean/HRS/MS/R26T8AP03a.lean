import HRS.MS.R26T8AP02
import HRS.MS.R26T8AP01a

/-!
# S8.2 local Newton layer, packet T8A.P03 (part a): truncated Newton kernel
`truncK chi nu r0 r1 u = psiCut(2 r0) u * chi (u / (2 r1)) * newtonKernel d nu u` is `C^oo` with compact support and equals the
Newton kernel on `r0/2 <= |u| <= 2 r1`; it lets the merged global-bound differentiation under the integral (`lc4_iteratedFDeriv_integral`)
act on the singular kernel.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

def r26t8a_truncK (chi : Euc d → ℝ) (nu r0 r1 : ℝ) (u : Euc d) : ℝ :=
  r26t8a_psiCut chi (2 * r0) u * chi ((1 / (2 * r1)) • u) * newtonKernel d nu u

theorem r26t8a_truncK_eq {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {nu r0 r1 : ℝ} (h0 : 0 < r0) (h1 : 0 < r1)
    {u : Euc d} (hu0 : r0 / 2 ≤ ‖u‖) (hu1 : ‖u‖ ≤ 2 * r1) :
    r26t8a_truncK chi nu r0 r1 u = newtonKernel d nu u := by
  unfold r26t8a_truncK
  rw [r26t8a_psiCut_one hchi (by positivity) (by linarith)]
  have : ‖(1 / (2 * r1)) • u‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), one_div, inv_mul_le_iff₀ (by positivity)]
    linarith
  rw [hchi.2.2.2.1 _ this]; ring

theorem r26t8a_truncK_contDiff {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {nu r0 r1 : ℝ} (h0 : 0 < r0)
    (hK : ContDiffOn ℝ ∞ (newtonKernel d nu) {z | z ≠ 0}) :
    ContDiff ℝ ∞ (r26t8a_truncK chi nu r0 r1) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hpsi := r26t8a_psiCut_contDiff hchi (2 * r0)
  have hchi' : ContDiff ℝ ∞ (fun u : Euc d => chi ((1 / (2 * r1)) • u)) := hchi.1.comp (contDiff_const_smul _)
  by_cases hx : x = 0
  · have hev : r26t8a_truncK chi nu r0 r1 =ᶠ[𝓝 x] fun _ => 0 := by
      have hopen : IsOpen {u : Euc d | ‖u‖ < r0 / 4} := isOpen_lt continuous_norm continuous_const
      filter_upwards [hopen.mem_nhds (by simp [hx]; positivity)] with u hu
      unfold r26t8a_truncK
      rw [r26t8a_psiCut_zero hchi (by positivity) (by linarith [(show ‖u‖ < r0 / 4 from hu)]), zero_mul, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hopen : IsOpen {z : Euc d | z ≠ 0} := isOpen_ne
    exact (hpsi.contDiffAt.mul hchi'.contDiffAt).mul (hK.contDiffAt (hopen.mem_nhds hx))

theorem r26t8a_truncK_compact {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {nu r0 r1 : ℝ} (h1 : 0 < r1) :
    HasCompactSupport (r26t8a_truncK chi nu r0 r1) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Metric.closedBall (0 : Euc d) (4 * r1))
    (isCompact_closedBall _ _) (fun u hu => ?_)
  by_contra h
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at h
  apply hu
  unfold r26t8a_truncK
  have : 2 ≤ ‖(1 / (2 * r1)) • u‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), one_div, le_inv_mul_iff₀ (by positivity)]
    linarith
  rw [hchi.2.2.2.2 _ this]; ring

/-- Slice jets: `D^i_Y Theta(Y,w)` is the restriction of the joint `D^i Theta (Y,w)`. -/
theorem r26t8a_slice_jet {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Θ : Euc d × Euc d → V} {i : ℕ}
    (hΘ : ContDiff ℝ (i : WithTop ℕ∞) Θ) (X w : Euc d) :
    iteratedFDeriv ℝ i (fun Y => Θ (Y, w)) X =
      (iteratedFDeriv ℝ i Θ (X, w)).compContinuousLinearMap (fun _ => ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) := by
  have h1 : (fun Y : Euc d => Θ (Y, w)) = (fun v : Euc d × Euc d => Θ (v + (0, w))) ∘ (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) := by
    funext Y; simp [Prod.mk_add_mk]
  have hf' : ContDiff ℝ (i : WithTop ℕ∞) (fun v : Euc d × Euc d => Θ (v + (0, w))) :=
    hΘ.comp (contDiff_id.add contDiff_const)
  rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_right (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) hf' X le_rfl]
  rw [iteratedFDeriv_comp_add_right]
  simp

theorem r26t8a_slice_jet_norm {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Θ : Euc d × Euc d → V} {i : ℕ}
    (hΘ : ContDiff ℝ (i : WithTop ℕ∞) Θ) (X w : Euc d) :
    ‖iteratedFDeriv ℝ i (fun Y => Θ (Y, w)) X‖ ≤ ‖iteratedFDeriv ℝ i Θ (X, w)‖ := by
  rw [r26t8a_slice_jet hΘ]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hc : ‖ContinuousLinearMap.inl ℝ (Euc d) (Euc d)‖ ≤ 1 := ContinuousLinearMap.norm_inl_le_one ℝ _ _
  calc _ ≤ ‖iteratedFDeriv ℝ i Θ (X, w)‖ * ∏ _j : Fin i, ‖ContinuousLinearMap.inl ℝ (Euc d) (Euc d)‖ := le_rfl
    _ ≤ ‖iteratedFDeriv ℝ i Θ (X, w)‖ * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact pow_le_one₀ (norm_nonneg _) hc
    _ = _ := mul_one _

end HRS.MS.R26T8A
