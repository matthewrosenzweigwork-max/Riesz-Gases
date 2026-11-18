import HRS.MS.R26T8AP03d

/-!
# S8.2 local Newton layer, packet T8A.P03 (part e): the nested jet of the annular Newton integral as a `w`-integral
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_sep_formula {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {nu : ℝ}
    (hK : ContDiffOn ℝ ∞ (newtonKernel d nu) {z | z ≠ 0}) {R : ℝ} (hR : 0 < R)
    {F : Euc d → Euc d → ℝ} {k : ℕ} (hF : ContDiffOn ℝ k (Function.uncurry F) {p | p.1 ≠ p.2})
    {r0 r1 : ℝ} (hr0 : 0 < r0) (hr01 : r0 ≤ r1) {z : Euc d}
    (hgeo : ∀ w : Euc d, R / 2 ≤ ‖w‖ → ‖w‖ ≤ 2 * R → r0 ≤ ‖z - w‖ ∧ ‖z - w‖ ≤ r1)
    {p q : ℕ} (hpq : p + q ≤ k) (X : Euc d) :
    iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (r26t8a_annularNewton nu chi R F Y) z) X =
      ∫ w, iteratedFDeriv ℝ p (fun Y => (chi (Y - X) *
        (r26t8a_annulus chi R w * midPair F Y w)) • iteratedFDeriv ℝ q (r26t8a_truncK chi nu r0 r1) (z - w)) X := by
  set S : Euc d × Euc d → ℝ := fun Yw => r26t8a_annulus chi R Yw.2 * midPair F Yw.1 Yw.2 with hSdef
  have hS : ContDiff ℝ k S := r26t8a_S_contDiff hchi hR hF
  set Kt := r26t8a_truncK chi nu r0 r1 with hKt
  have hKtd : ContDiff ℝ ∞ Kt := r26t8a_truncK_contDiff hchi hr0 hK
  have hKtc : HasCompactSupport Kt := r26t8a_truncK_compact hchi (hr0.trans_le hr01)
  have hSz : ∀ Y w, r26t8a_annulus chi R w = 0 → S (Y, w) = 0 := fun Y w h => by simp [hSdef, h]
  have hsupp : ∀ Y, Function.support (fun w => S (Y, w)) ⊆ Metric.closedBall (0 : Euc d) (2 * R) := by
    intro Y w hw
    by_contra hn
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hn
    exact hw (hSz Y w (r26t8a_annulus_zero_large hchi hR hn.le))
  -- local equality of the annular Newton integral with the truncated one
  have hann : ∀ Y, r26t8a_annularNewton nu chi R F Y =ᶠ[𝓝 z] fun x => ∫ w, S (Y, w) * Kt (x - w) := by
    intro Y
    filter_upwards [Metric.ball_mem_nhds z (half_pos hr0)] with x hx
    unfold r26t8a_annularNewton
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    by_cases ha : r26t8a_annulus chi R w = 0
    · simp [hSdef, ha]
    · obtain ⟨hw1, hw2⟩ := r26t8a_annulus_ne_zero hchi hR ha
      obtain ⟨h0, h1⟩ := hgeo w hw1.le hw2.le
      have hxz : ‖x - z‖ < r0 / 2 := by simpa [dist_eq_norm] using hx
      have e1 : x - w = (z - w) + (x - z) := by abel
      have l1 : r0 / 2 ≤ ‖x - w‖ := by
        have := norm_sub_norm_le (z - w) (-(x - z))
        have h3 : ‖z - w - -(x - z)‖ = ‖x - w‖ := by congr 1; abel
        rw [norm_neg, h3] at this
        linarith
      have l2 : ‖x - w‖ ≤ 2 * r1 := by
        rw [e1]
        linarith [norm_add_le (z - w) (x - z)]
      have hk := r26t8a_truncK_eq hchi (nu := nu) hr0 (hr0.trans_le hr01) l1 l2
      beta_reduce
      simp only [hSdef, hKt, hk]
      ring
  have hT : ContDiff ℝ ∞ (fun w => iteratedFDeriv ℝ q Kt (z - w)) :=
    (hKtd.iteratedFDeriv_right (m := ∞) (by simp)).comp (contDiff_const.sub contDiff_id)
  have hstage1 : ∀ Y, iteratedFDeriv ℝ q (r26t8a_annularNewton nu chi R F Y) z =
      ∫ w, S (Y, w) • iteratedFDeriv ℝ q Kt (z - w) := by
    intro Y
    have hsc : Continuous fun w => S (Y, w) := hS.continuous.comp (continuous_const.prodMk continuous_id)
    have hsk : HasCompactSupport fun w => S (Y, w) :=
      HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _) (hsupp Y)
    rw [((hann Y).iteratedFDeriv ℝ q).eq_of_nhds]
    exact r26t8a_stage1 hsc hsk hKtd hKtc q z
  set Θ : Euc d × Euc d → ℝ := fun Yw => chi (Yw.1 - X) * S Yw with hΘdef
  have hΘ : ContDiff ℝ (p : WithTop ℕ∞) Θ :=
    ((hchi.1.comp (contDiff_fst.sub contDiff_const)).of_le (by exact_mod_cast le_top)).mul
      (hS.of_le (by exact_mod_cast (by omega : p ≤ k)))
  have hΘc : HasCompactSupport Θ := by
    refine HasCompactSupport.of_support_subset_isCompact
      ((isCompact_closedBall X 2).prod (isCompact_closedBall (0 : Euc d) (2 * R))) (fun Yw hYw => ?_)
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm]
      by_contra hn
      push Not at hn
      exact hYw (by simp only [hΘdef]; rw [hchi.2.2.2.2 _ hn.le, zero_mul])
    · exact hsupp Yw.1 (fun h => hYw (by simp only [hΘdef]; rw [show S Yw = 0 from h, mul_zero]))
  have hloc : (fun Y => iteratedFDeriv ℝ q (r26t8a_annularNewton nu chi R F Y) z) =ᶠ[𝓝 X]
      fun Y => ∫ w, Θ (Y, w) • iteratedFDeriv ℝ q Kt (z - w) := by
    have hopen : IsOpen {Y : Euc d | ‖Y - X‖ < 1} := isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
    filter_upwards [hopen.mem_nhds (by simp)] with Y hY
    rw [hstage1 Y]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [hΘdef, hchi.2.2.2.1 _ (le_of_lt (show ‖Y - X‖ < 1 from hY)), one_mul]
  rw [(hloc.iteratedFDeriv ℝ p).eq_of_nhds]
  exact r26t8a_stage2 hΘ (hT.of_le (by exact_mod_cast le_top)) hΘc X

end HRS.MS.R26T8A
