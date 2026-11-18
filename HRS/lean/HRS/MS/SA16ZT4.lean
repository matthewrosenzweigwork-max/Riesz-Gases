import HRS.MS.SA16ZT3

/-!
# S.A.16 (SA16Z) T4: the limits `ε → 0` for the cutoff identity

`sa16z_odd_sub`: an odd integrable `h` satisfies `∫ h F = ∫ h (F - F 0)`;
`sa16z_R2_tendsto`: `∫ F g ∂_iχ_ε → 0`; `sa16z_R3_tendsto`: `∫ ∂_iF g χ_ε → ∫ ∂_iF g`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution RealInnerProductSpace

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section T4
variable {d : ℕ} {s : ℝ}

lemma sa16z_odd_sub {h F : Euc d → ℝ} (hodd : ∀ z, h (-z) = -h z) (hint : Integrable h)
    (hint2 : Integrable (fun z => h z * F z)) : ∫ z, h z * F z = ∫ z, h z * (F z - F 0) := by
  have h0 : ∫ z, h z = 0 := by
    have := integral_neg_eq_self h (volume : Measure (Euc d))
    simp only [hodd, integral_neg] at this
    linarith
  have : (fun z => h z * (F z - F 0)) = fun z => h z * F z - F 0 * h z := by funext z; ring
  rw [this, integral_sub hint2 (hint.const_mul _), integral_const_mul, h0]
  ring

lemma sa16z_dchi_far {ε : ℝ} (hε : 0 < ε) (i : Fin d) {z : Euc d} (hz : 2 * ε ^ 2 ≤ ‖z‖ ^ 2) :
    sa16z_dchi d ε i z = 0 := by
  unfold sa16z_dchi
  have : 1 ≤ ‖z‖ ^ 2 / ε ^ 2 - 1 := by
    have : 2 ≤ ‖z‖ ^ 2 / ε ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  rw [sa16z_st_deriv_zero_of_one_le this, zero_mul]

lemma sa16z_dchi_cont (ε : ℝ) (i : Fin d) : Continuous (sa16z_dchi d ε i) := by
  have : sa16z_dchi d ε i = fun z => fderiv ℝ (sa16z_chi d ε) z (sa16z_e i) :=
    funext fun z => (sa16z_dchi_eq ε i z).symm
  rw [this]
  exact ((sa16z_chi_smooth ε).continuous_fderiv (by simp)).clm_apply continuous_const

lemma sa16z_dchi_cs {ε : ℝ} (hε : 0 < ε) (i : Fin d) : HasCompactSupport (sa16z_dchi d ε i) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Euc d) (2 * ε)) ?_
  intro z hz
  by_contra hzn
  have hz2 : 2 * ε < ‖z‖ := by simpa using hzn
  refine hz (sa16z_dchi_far hε i ?_)
  nlinarith

lemma sa16z_g_odd (s : ℝ) (z : Euc d) : rieszKernel d s (-z) = rieszKernel d s z := rieszKernel_neg z

theorem sa16z_R2_tendsto (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {F : Euc d → ℝ} (hF : IsCcInfty F)
    (i : Fin d) :
    Tendsto (fun ε : ℝ => ∫ z, F z * (rieszKernel d s z * sa16z_dchi d ε i z)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M, hM0, hM⟩ := sa16z_smoothTransition_deriv_bound
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hF.2 (hF.1.of_le (by simp)) (n := 1) one_ne_zero
  have hC0 : (0 : ℝ) ≤ C := C.2
  have hFl : ∀ z, |F z - F 0| ≤ C * ‖z‖ := by
    intro z
    have := hC.dist_le_mul z 0
    simpa [Real.dist_eq, dist_eq_norm] using this
  have hgm : Measurable (rieszKernel d s) := HRS.S16Frac.s16frac_g_meas d s
  have hgl := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  -- rewrite using oddness
  have hrw : ∀ ε : ℝ, 0 < ε → ∫ z, F z * (rieszKernel d s z * sa16z_dchi d ε i z) =
      ∫ z, (rieszKernel d s z * sa16z_dchi d ε i z) * (F z - F 0) := by
    intro ε hε
    have hint : Integrable (fun z => rieszKernel d s z * sa16z_dchi d ε i z) :=
      sa16z_g_mul_int hs0 hsd (sa16z_dchi_cont ε i) (sa16z_dchi_cs hε i)
    have hint2 : Integrable (fun z => (rieszKernel d s z * sa16z_dchi d ε i z) * F z) := by
      have := sa16z_g_mul_int hs0 hsd ((sa16z_dchi_cont ε i).mul hF.1.continuous)
        ((sa16z_dchi_cs hε i).mul_right)
      refine this.congr (Eventually.of_forall fun z => ?_)
      simp only [Pi.mul_apply]; ring
    rw [← sa16z_odd_sub (h := fun z => rieszKernel d s z * sa16z_dchi d ε i z) (F := F)
      (fun z => by simp only [sa16z_g_odd, sa16z_dchi_neg]; ring) hint hint2]
    exact integral_congr_ae (Eventually.of_forall fun z => by simp only; ring)
  have hlim : Tendsto (fun ε : ℝ => ∫ z, (rieszKernel d s z * sa16z_dchi d ε i z) * (F z - F 0))
      (𝓝[>] 0) (𝓝 0) := by
    have hint1 : IntegrableOn (fun z => 4 * M * C * |rieszKernel d s z|) (closedBall (0 : Euc d) 2) := by
      have := (hgl.integrableOn_isCompact (isCompact_closedBall (0 : Euc d) 2)).norm.const_mul (4 * M * C)
      show Integrable _ (volume.restrict (closedBall (0 : Euc d) 2))
      simpa [Real.norm_eq_abs] using this
    have key := tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure (Euc d)))
      (l := 𝓝[>] (0 : ℝ))
      (F := fun (ε : ℝ) (z : Euc d) => (rieszKernel d s z * sa16z_dchi d ε i z) * (F z - F 0))
      (f := fun _ => (0 : ℝ))
      (fun z => (indicator (closedBall (0 : Euc d) 2) (fun z => 4 * M * C * |rieszKernel d s z|)) z) ?_ ?_
      ((integrable_indicator_iff measurableSet_closedBall).2 hint1) ?_
    · simpa using key
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact ((hgm.mul (sa16z_dchi_cont ε i).measurable).mul
        ((hF.1.continuous.sub continuous_const).measurable)).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with ε hε
      refine Eventually.of_forall fun z => ?_
      have hε0 : 0 < ε := hε.1
      by_cases hz : ‖z‖ ≤ 2
      · rw [indicator_of_mem (by simpa using hz)]
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        have h1 := sa16z_dchi_mul_norm_le hM hε0 i z
        calc |rieszKernel d s z| * |sa16z_dchi d ε i z| * |F z - F 0|
            ≤ |rieszKernel d s z| * |sa16z_dchi d ε i z| * (C * ‖z‖) :=
              mul_le_mul_of_nonneg_left (hFl z) (by positivity)
          _ = C * |rieszKernel d s z| * (|sa16z_dchi d ε i z| * ‖z‖) := by ring
          _ ≤ C * |rieszKernel d s z| * (4 * M) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = 4 * M * C * |rieszKernel d s z| := by ring
      · have hz2 : 2 * ε ^ 2 ≤ ‖z‖ ^ 2 := by
          have : 2 < ‖z‖ := not_le.1 hz
          nlinarith [hε.2]
        rw [sa16z_dchi_far hε0 i hz2]
        simp
        exact indicator_nonneg (fun z _ => by positivity) z
    · filter_upwards [HRS.Commutator.Whole.ae_ne_zero_euc hd] with z hz
      have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, (rieszKernel d s z * sa16z_dchi d ε i z) * (F z - F 0) = 0 := by
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ‖z‖ / 2 by
          have := norm_pos_iff.2 hz; linarith)] with ε hε
        have hlt : ε * ε < (‖z‖ / 2) * (‖z‖ / 2) := mul_self_lt_mul_self hε.1.le hε.2
        rw [sa16z_dchi_far hε.1 i (by nlinarith [norm_nonneg z])]
        simp
      exact tendsto_const_nhds.congr' (hev.mono fun ε h => h.symm)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hrw ε hε).symm

end T4

end HRS.Whole.AppendixA.Phase2SA16R
