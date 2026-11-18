import HRS.MS.R26T8AP07j

/-!
# S8.2 local Newton layer, packet T8A.P07 (part k): series representation of the raw Newton integral
`r26t8a_p07_series_repr` (`0 <= sigma < d`): the raw integrand is integrable for every `w != 0`, and for `0 < |w| <= 4`
`HasSum (fun n => annularNewton nu chi ((1/2)^n) F X w) (∫ z, K(w-z) chi z midPair F X z)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_p07_annulus_eq {chi : Euc d → ℝ} (n : ℕ) (z : Euc d) :
    r26t8a_annulus chi (((1 : ℝ) / 2) ^ n) z = chi (((2 : ℝ) ^ n) • z) - chi (((2 : ℝ) ^ (n + 1)) • z) := by
  unfold r26t8a_annulus
  have e1 : (((1 : ℝ) / 2) ^ n)⁻¹ = (2 : ℝ) ^ n := by rw [one_div, inv_pow, inv_inv]
  have e2 : 2 / (((1 : ℝ) / 2) ^ n) = (2 : ℝ) ^ (n + 1) := by
    rw [one_div, inv_pow, div_inv_eq_mul, pow_succ]; ring
  rw [e1, e2]

theorem r26t8a_p07_series_repr (hd : 2 ≤ d) (k b : ℕ) (nu M σ : ℝ) (hnu : 0 < nu) (hM : 0 ≤ M) (hσd : σ < d) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {A : ℝ} (hA : 0 ≤ A) {F : Euc d → Euc d → ℝ}
    (hF : ConormalP k b M σ A F) (X w : Euc d) (hw : w ≠ 0) :
    Integrable (fun z => newtonKernel d nu (w - z) * chi z * midPair F X z) ∧
    (‖w‖ ≤ 4 → HasSum (fun n : ℕ => r26t8a_annularNewton nu chi (((1 : ℝ) / 2) ^ n) F X w)
      (∫ z, newtonKernel d nu (w - z) * chi z * midPair F X z)) := by
  obtain ⟨s, hs0, hsd, hFb⟩ := r26t8a_p07_midbound hd k b M σ hM hσd
  obtain ⟨c, hc0, hc⟩ := hFb A hA F (ConormalP.toConormal hA hF) X
  have hm : ContinuousOn (fun z => midPair F X z) {z : Euc d | z ≠ 0} :=
    (r26t8a_midPair_contDiffOn hF.1).continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun z hz => hz)
  have hch : Continuous chi := hchi.1.continuous
  have hdom := fun (θ : Euc d → ℝ) (h1 : Continuous θ) (h2 : ∀ z, |θ z| ≤ 1) (h3 : ∀ z, 2 < ‖z‖ → θ z = 0) =>
    r26t8a_p07_dom hd nu hs0 hsd hw hm hc0 hc θ h1 h2 h3
  have hchi1 : ∀ z, |chi z| ≤ 1 := fun z => by
    rw [abs_of_nonneg (hchi.2.2.1 z).1]; exact (hchi.2.2.1 z).2
  have hchi2 : ∀ z, 2 < ‖z‖ → chi z = 0 := fun z hz => hchi.2.2.2.2 z hz.le
  refine ⟨(hdom chi hch hchi1 hchi2).1, fun hw2 => ?_⟩
  set f : Euc d → ℝ := fun z => newtonKernel d nu (w - z) * chi z * midPair F X z with hf
  -- summability from the series bound
  obtain ⟨C, hC0, hC⟩ := r26t8a_p07_series_bound hd k b nu M σ hnu hM hσd hchi
  have hsumm : Summable (fun n : ℕ => r26t8a_annularNewton nu chi (((1 : ℝ) / 2) ^ n) F X w) := by
    have := (hC A hA F hF 0 0 (by omega) X w (norm_pos_iff.2 hw) hw2).1
    refine Summable.of_norm ?_
    simpa only [norm_iteratedFDeriv_zero] using this
  rw [hsumm.hasSum_iff_tendsto_nat]
  -- partial sums are integrals of the truncated cutoff
  have hθN : ∀ N : ℕ, Integrable (fun z => newtonKernel d nu (w - z) * (chi z - chi (((2 : ℝ) ^ N) • z)) *
      midPair F X z) ∧ ∀ z : Euc d, z ≠ 0 → ‖newtonKernel d nu (w - z) * (chi z - chi (((2 : ℝ) ^ N) • z)) *
      midPair F X z‖ ≤ c * (|newtonKernel d nu (w - z)| *
        (closedBall (0 : Euc d) 2).indicator (fun z => ‖z‖ ^ (-s)) z) := by
    intro N
    refine hdom (fun z => chi z - chi (((2 : ℝ) ^ N) • z)) (hch.sub (hch.comp (continuous_const_smul _)))
      (fun z => ?_) (fun z hz => ?_)
    · have h1 := hchi.2.2.1 z
      have h2 := hchi.2.2.1 (((2 : ℝ) ^ N) • z)
      rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    · have h2 : 2 < ‖((2 : ℝ) ^ N) • z‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
        have : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
        nlinarith [norm_nonneg z]
      simp only [hchi2 z hz, hchi2 _ h2, sub_zero]
  have hann : ∀ n : ℕ, Integrable (fun z => newtonKernel d nu (w - z) *
      r26t8a_annulus chi (((1 : ℝ) / 2) ^ n) z * midPair F X z) := by
    intro n
    have hR : (0 : ℝ) < ((1 : ℝ) / 2) ^ n := by positivity
    have hR1 : ((1 : ℝ) / 2) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    refine (hdom _ (r26t8a_annulus_contDiff hchi hR).continuous (fun z => ?_) (fun z hz => ?_)).1
    · have h1 := hchi.2.2.1 ((((1 : ℝ) / 2) ^ n)⁻¹ • z)
      have h2 := hchi.2.2.1 ((2 / (((1 : ℝ) / 2) ^ n)) • z)
      unfold r26t8a_annulus
      rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    · exact r26t8a_annulus_zero_large hchi hR (by linarith)
  have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range N, r26t8a_annularNewton nu chi (((1 : ℝ) / 2) ^ n) F X w =
      ∫ z, newtonKernel d nu (w - z) * (chi z - chi (((2 : ℝ) ^ N) • z)) * midPair F X z := by
    intro N
    unfold r26t8a_annularNewton
    rw [← integral_finsetSum _ (fun n _ => hann n)]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [r26t8a_p07_annulus_eq]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    congr 2
    rw [Finset.sum_range_sub' (fun n => chi (((2 : ℝ) ^ n) • z)) N]
    simp
  simp only [hpart]
  refine tendsto_integral_of_dominated_convergence
    (fun z => c * (|newtonKernel d nu (w - z)| * (closedBall (0 : Euc d) 2).indicator (fun z => ‖z‖ ^ (-s)) z))
    (fun N => (hθN N).1.aestronglyMeasurable) ((r26t8a_p07_major hd nu hs0 hsd hw).const_mul c)
    (fun N => ?_) ?_
  · filter_upwards [r26t8a_ae_ne_zero hd] with z hz using (hθN N).2 z hz
  · filter_upwards [r26t8a_ae_ne_zero hd] with z hz
    have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hev : ∀ᶠ N : ℕ in atTop, 2 < (2 : ℝ) ^ N * ‖z‖ :=
      ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const hzn).eventually_gt_atTop 2
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with N hN
    have h2 : 2 < ‖((2 : ℝ) ^ N) • z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]; exact hN
    simp only [hf, hchi2 _ h2, sub_zero]

end HRS.MS.R26T8A
