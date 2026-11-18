import HRS.MS.SA12C20

/-!
# S.A.12(c), packet E7.04 (part 5): the remainder `perConv - euclidean near convolution` as a smooth convolution

For `‖x - c‖ < 2`, `‖x0 - c‖ < 2`, `L ≥ 40`:
`perConv L γ f x - ∫ g(x-y) χ̂(y-c) f(y) dy = (1_Y f ⋆ Ã)(x) - (χ̂(·-c) f ⋆ B̃)(x)`,
`Y = {y | x0 - L/2 ≤ y < x0 + L/2}` a period cell containing `B(c,8)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Near

variable {d : ℕ}

/-- The period cell `[x0 - L/2, x0 + L/2)^d`. -/
def sa12cYcell (d : ℕ) (L : ℝ) (x0 : Euc d) : Set (Euc d) :=
  {y : Euc d | ∀ i, x0 i - L / 2 ≤ y i ∧ y i < x0 i + L / 2}

theorem sa12cYcell_meas (L : ℝ) (x0 : Euc d) : MeasurableSet (sa12cYcell d L x0) := by
  have : sa12cYcell d L x0 = ⋂ i : Fin d, ({y : Euc d | x0 i - L / 2 ≤ y i} ∩ {y : Euc d | y i < x0 i + L / 2}) := by
    ext y; simp [sa12cYcell]
  rw [this]
  refine MeasurableSet.iInter fun i => ?_
  have hm : Measurable fun y : Euc d => y i := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.measurable
  exact (measurableSet_le measurable_const hm).inter (measurableSet_lt hm measurable_const)

theorem sa12c_coord_le (z : Euc d) (i : Fin d) : |z i| ≤ ‖z‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le z i

theorem sa12cYcell_ball {L : ℝ} (hL : 40 ≤ L) {c x0 : Euc d} (hx0 : ‖x0 - c‖ < 2) {y : Euc d}
    (hy : ‖y - c‖ < 8) : y ∈ sa12cYcell d L x0 := by
  intro i
  have h1 : |(y - x0) i| ≤ ‖y - x0‖ := sa12c_coord_le _ i
  have h2 : ‖y - x0‖ ≤ ‖y - c‖ + ‖x0 - c‖ := by
    calc ‖y - x0‖ = ‖(y - c) - (x0 - c)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have h3 := abs_le.1 h1
  simp only [PiLp.sub_apply] at h3
  constructor <;> linarith [h3.1, h3.2]

theorem sa12c_T_identity {s L c0 : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hL : 40 ≤ L)
    {q χ χh γ : Euc d → ℝ} (hχ : IsCutoffPair χ χh) (hγ : IsPeriodicRieszKernel d s L γ)
    (hq : ContDiff ℝ ∞ q)
    (hΘ : ∀ z : Euc d, z ≠ 0 → ‖z‖ < 4 → γ z = rieszKernel d s z + sa12cTh s L c0 q z)
    {f : Euc d → ℝ} (hf : Continuous f) (hfp : ∀ (x : Euc d) (k : Fin d → ℤ), f (x + L • latticePt k) = f x)
    (c x0 x : Euc d) (hx0 : ‖x0 - c‖ < 2) (hx : ‖x - c‖ < 2) (hd : 1 ≤ d) :
    perConv L γ f x - ∫ y, rieszKernel d s (x - y) * (χh (y - c) * f y) =
      sa12cConv ((sa12cYcell d L x0).indicator f) (sa12cA s L c0 q χ γ) x -
        sa12cConv (fun y => χh (y - c) * f y) (sa12cB s L χ) x := by
  have hL0 : 0 < L := by linarith
  set Y := sa12cYcell d L x0 with hY
  have hYm := sa12cYcell_meas L x0
  set A := sa12cA s L c0 q χ γ with hA
  set B := sa12cB s L χ with hB
  have hAc : Continuous A := (sa12cA_contDiff hL0 hq hχ hγ).continuous
  have hBc : Continuous B := (sa12cB_contDiff hL0 hχ).continuous
  have hAcs : HasCompactSupport A := sa12cA_compact hL0 hχ
  have hBcs : HasCompactSupport B := sa12cB_compact hL0 hχ
  have hg := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have hζc : Continuous (sa12cZeta χ) := (sa12cZeta_contDiff hχ).continuous
  have hχhc : Continuous χh := hχ.2.1.continuous
  -- pointwise identities
  have hS1 : ∀ z : Euc d, z ≠ 0 → sa12cXi d L z = 1 →
      γ z = A z + sa12cZeta χ z * rieszKernel d s z := by
    intro z hz0 hΞ
    by_cases hζ : sa12cZeta χ z = 0
    · simp [hA, sa12cA, hζ, hΞ]
    · have h4 := sa12cZeta_lt hχ hζ
      have := hΘ z hz0 h4
      simp only [hA, sa12cA, hΞ, one_mul]
      rw [this]; ring
  have hS2 : ∀ z : Euc d, sa12cXi d L z = 1 → B z = (1 - sa12cZeta χ z) * rieszKernel d s z := by
    intro z hΞ
    simp [hB, sa12cB, hΞ]
  have hΞ1 : ∀ z : Euc d, ‖z‖ ≤ 10 → sa12cXi d L z = 1 := by
    intro z hz
    refine sa12cXi_one hL0 fun i => ?_
    have := sa12c_coord_le z i
    linarith
  -- the three functions
  set f1 : Euc d → ℝ := Y.indicator f with hf1d
  set f' : Euc d → ℝ := fun y => sa12cZeta χ (x - y) * f y with hf'd
  set f2 : Euc d → ℝ := fun y => χh (y - c) * f y with hf2d
  have hf1 : LocallyIntegrable f1 volume := hf.locallyIntegrable.indicator hYm
  have hf'c : Continuous f' := (hζc.comp (continuous_const.sub continuous_id)).mul hf
  have hf2c : Continuous f2 := (hχhc.comp (continuous_id.sub continuous_const)).mul hf
  have hf'cs : HasCompactSupport f' := by
    refine HasCompactSupport.intro (isCompact_closedBall x 4) fun y hy => ?_
    rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hy
    have : sa12cZeta χ (x - y) = 0 := by
      apply sa12cZeta_zero hχ
      rw [norm_sub_rev]; exact hy
    simp [hf'd, this]
  have hf2cs : HasCompactSupport f2 := by
    refine HasCompactSupport.intro (isCompact_closedBall c 8) fun y hy => ?_
    rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hy
    have : χh (y - c) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have := hχ.2.2.2.1 hmem
      rw [Metric.mem_ball, dist_zero_right] at this
      linarith
    simp [hf2d, this]
  have I1 : Integrable (fun y => f1 y * A (x - y)) volume := by
    have := hAcs.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ) hf1 hAc x
    simpa [ConvolutionExistsAt] using this
  have I2 : Integrable (fun y => f' y * rieszKernel d s (x - y)) volume := by
    have := hf'cs.convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ) hf'c hg x
    simpa [ConvolutionExistsAt] using this
  have I3 : Integrable (fun y => f2 y * rieszKernel d s (x - y)) volume := by
    have := hf2cs.convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ) hf2c hg x
    simpa [ConvolutionExistsAt] using this
  -- step 1: perConv over the cell Y
  have hYeq : Y = {z : Euc d | ∀ i, (x0 - WithLp.toLp 2 fun _ : Fin d => L / 2) i ≤ z i ∧
      z i < (x0 - WithLp.toLp 2 fun _ : Fin d => L / 2) i + L} := by
    ext z
    simp only [hY, sa12cYcell, Set.mem_ofPred_eq, PiLp.sub_apply]
    refine forall_congr' fun i => ?_
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hper : ∀ (y : Euc d) (k : Fin d → ℤ),
      γ (x - (y + L • latticePt k)) * f (y + L • latticePt k) = γ (x - y) * f y := by
    intro y k
    have h1 := hγ.periodic (x - y - L • latticePt k) k
    rw [sub_add_cancel] at h1
    rw [hfp, sub_add_eq_sub_sub, ← h1]
  have hP : perConv L γ f x = ∫ y in Y, γ (x - y) * f y := by
    unfold perConv
    rw [hYeq]
    exact (sa12c20_cell_shift L hL0 (Φ := fun y => γ (x - y) * f y) hper _).symm
  -- step 2
  have hae : ∀ᵐ y ∂(volume : Measure (Euc d)), y ≠ x := by
    haveI : NeZero d := ⟨by omega⟩
    exact compl_mem_ae_iff.2 (measure_singleton x)
  have hzs : ∀ y, y ∈ Y → ∀ i, |(x - y) i| ≤ 3 * L / 5 := by
    intro y hy i
    have h1 : |(x - x0) i| ≤ ‖x - x0‖ := sa12c_coord_le _ i
    have h2 : ‖x - x0‖ < 4 := by
      calc ‖x - x0‖ = ‖(x - c) - (x0 - c)‖ := by congr 1; abel
        _ ≤ ‖x - c‖ + ‖x0 - c‖ := norm_sub_le _ _
        _ < 4 := by linarith
    have h3 := hy i
    have h4 := abs_le.1 h1
    simp only [PiLp.sub_apply] at h4 ⊢
    rw [abs_le]
    constructor <;> linarith [h4.1, h4.2, h3.1, h3.2]
  have hstep2 : (∫ y in Y, γ (x - y) * f y) =
      (∫ y, f1 y * A (x - y)) + ∫ y, f' y * rieszKernel d s (x - y) := by
    rw [← integral_add I1 I2, ← integral_indicator hYm]
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hyx
    have hz0 : x - y ≠ 0 := sub_ne_zero.2 (Ne.symm hyx)
    by_cases hy : y ∈ Y
    · rw [Set.indicator_of_mem hy]
      have hΞ : sa12cXi d L (x - y) = 1 := sa12cXi_one hL0 (hzs y hy)
      have := hS1 (x - y) hz0 hΞ
      simp only [hf1d, hf'd, Set.indicator_of_mem hy]
      rw [this]; ring
    · rw [Set.indicator_of_notMem hy]
      have hζ : sa12cZeta χ (x - y) = 0 := by
        by_contra hne
        have h4 := sa12cZeta_lt hχ hne
        apply hy
        refine sa12cYcell_ball hL hx0 ?_
        calc ‖y - c‖ = ‖(y - x) + (x - c)‖ := by congr 1; abel
          _ ≤ ‖y - x‖ + ‖x - c‖ := norm_add_le _ _
          _ < 8 := by
            have hxc : ‖x - c‖ < 2 := by simpa only [norm_sub_rev] using hx
            have hyx : ‖y - x‖ < 4 := by simpa only [norm_sub_rev] using h4
            linarith
      simp [hf1d, hf'd, hζ, Set.indicator_of_notMem hy]
  -- step 3
  have hf2B : ∀ y, f2 y * B (x - y) = f2 y * rieszKernel d s (x - y) - f' y * rieszKernel d s (x - y) := by
    intro y
    by_cases hζ : sa12cZeta χ (x - y) = 0
    · have hf'0 : f' y = 0 := by simp [hf'd, hζ]
      rw [hf'0]
      by_cases hf20 : f2 y = 0
      · simp [hf20]
      · have hχy : ¬ χh (y - c) = 0 := fun h => hf20 (by simp [hf2d, h])
        have hy8 : ‖y - c‖ < 8 := by
          by_contra hge; push Not at hge
          apply hχy
          apply image_eq_zero_of_notMem_tsupport
          intro hmem
          have := hχ.2.2.2.1 hmem
          rw [Metric.mem_ball, dist_zero_right] at this
          linarith
        have hΞ : sa12cXi d L (x - y) = 1 := by
          apply hΞ1
          calc ‖x - y‖ = ‖(x - c) - (y - c)‖ := by congr 1; abel
            _ ≤ ‖x - c‖ + ‖y - c‖ := norm_sub_le _ _
            _ ≤ 10 := by linarith
        rw [hS2 _ hΞ, hζ]; ring
    · have h4 := sa12cZeta_lt hχ hζ
      have hy6 : ‖y - c‖ < 6 := by
        calc ‖y - c‖ = ‖(y - x) + (x - c)‖ := by congr 1; abel
          _ ≤ ‖y - x‖ + ‖x - c‖ := norm_add_le _ _
          _ < 6 := by
            have hxc : ‖x - c‖ < 2 := by simpa only [norm_sub_rev] using hx
            have hyx : ‖y - x‖ < 4 := by simpa only [norm_sub_rev] using h4
            linarith
      have hχ1 : χh (y - c) = 1 := by
        apply hχ.2.2.2.2.2
        rw [Metric.mem_closedBall, dist_zero_right]; linarith
      have hΞ : sa12cXi d L (x - y) = 1 := hΞ1 _ (by linarith)
      rw [hS2 _ hΞ]
      simp only [hf2d, hf'd, hχ1, one_mul]
      ring
  have hstep3 : sa12cConv f2 B x = (∫ y, f2 y * rieszKernel d s (x - y)) -
      ∫ y, f' y * rieszKernel d s (x - y) := by
    unfold sa12cConv
    simp_rw [hf2B]
    exact integral_sub I3 I2
  have hEuc : ∫ y, rieszKernel d s (x - y) * (χh (y - c) * f y) =
      ∫ y, f2 y * rieszKernel d s (x - y) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hf2d]; ring
  rw [hP, hstep2, hEuc, hstep3]
  show _ - _ = sa12cConv f1 A x - _
  unfold sa12cConv
  ring


end HRS.MH.AdjointRd.Phase2SA12C
