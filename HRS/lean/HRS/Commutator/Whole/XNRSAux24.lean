import HRS.Commutator.Whole.XNRSAux23

/-!
# Packet X-NRS, part 24: uniform convergence of the approximants
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

lemma xnorm_fourier_le (g : 𝓢(Euc d, ℂ)) (w : Euc d) : ‖𝓕 g w‖ ≤ ∫ ξ, ‖g ξ‖ := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  dsimp only
  rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

lemma xnorm_le_fourier (g : 𝓢(Euc d, ℂ)) (x : Euc d) : ‖g x‖ ≤ ∫ ξ, ‖𝓕 g ξ‖ := by
  have h : g x = 𝓕 (𝓕 g : 𝓢(Euc d, ℂ)) (-x) := by
    rw [xfourier_fourier, neg_neg]
  rw [h]
  exact xnorm_fourier_le _ _

lemma xsup_bound {a : Euc d → ℝ} {φ : 𝓢(Euc d, ℂ)} (ha : ∀ x, φ x = (a x : ℂ)) {n : ℝ} (hn : 0 < n)
    (x : Euc d) :
    |a x - xan a n x| ≤ ∫ ξ, (1 - xσ n ξ) * ‖𝓕 φ ξ‖ := by
  have h1 : ‖(φ - xφn φ n hn) x‖ ≤ ∫ ξ, ‖𝓕 (φ - xφn φ n hn) ξ‖ := xnorm_le_fourier _ x
  have h2 : (φ - xφn φ n hn) x = ((a x - xan a n x : ℝ) : ℂ) := by
    rw [sub_apply, xφn_real ha n hn, ha]; push_cast; ring
  rw [h2, Complex.norm_real, Real.norm_eq_abs] at h1
  refine h1.trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  have hsub : (𝓕 (φ - xφn φ n hn) : 𝓢(Euc d, ℂ)) = 𝓕 φ - 𝓕 (xφn φ n hn) := by
    simpa using map_sub (FourierTransform.fourierCLM ℂ 𝓢(Euc d, ℂ)) φ (xφn φ n hn)
  rw [hsub, sub_apply, fourier_xφn]
  have : 𝓕 φ ξ - 𝓕 φ ξ * ((xσ n ξ : ℝ) : ℂ) = 𝓕 φ ξ * ((1 - xσ n ξ : ℝ) : ℂ) := by push_cast; ring
  rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ 1 - xσ n ξ from sub_nonneg.2 (xcut_le_one n n ξ)), mul_comm]

lemma xcut_continuous (R r : ℝ) : Continuous (xcut R r : Euc d → ℝ) :=
  (xchi_smooth.continuous.comp (continuous_const_smul _)).mul
    (continuous_const.sub (xchi_smooth.continuous.comp (continuous_const_smul _)))

lemma xae_ne_zero (hd : 1 ≤ d) : ∀ᵐ ξ : Euc d ∂volume, ξ ≠ 0 := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  haveI : Nontrivial (Euc d) := inferInstanceAs (Nontrivial (EuclideanSpace ℝ (Fin d)))
  rw [ae_iff]
  simpa using measure_singleton (μ := (volume : Measure (Euc d))) (0 : Euc d)

lemma tendsto_xsup (hd : 1 ≤ d) (φ : 𝓢(Euc d, ℂ)) :
    Tendsto (fun n : ℝ => ∫ ξ, (1 - xσ n ξ) * ‖𝓕 φ ξ‖) atTop (nhds 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure (Euc d)))
    (F := fun (n : ℝ) ξ => (1 - xσ n ξ) * ‖𝓕 φ ξ‖) (f := fun _ => 0) (l := atTop)
    (bound := fun ξ => ‖𝓕 φ ξ‖) ?_ ?_ ?_ ?_
  · simpa using h
  · refine Eventually.of_forall fun n => ?_
    have : Continuous (fun ξ : Euc d => (1 - xσ n ξ) * ‖𝓕 φ ξ‖) :=
      (continuous_const.sub (xcut_continuous n n)).mul (𝓕 φ).continuous.norm
    exact this.aestronglyMeasurable
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
    refine Eventually.of_forall fun ξ => ?_
    have h0 := xcut_nonneg n n ξ
    have h1 := xcut_le_one n n ξ
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by unfold xσ; linarith), norm_norm]
    have : 1 - xσ n ξ ≤ 1 := by unfold xσ; linarith
    exact mul_le_of_le_one_left (norm_nonneg _) this
  · exact (𝓕 φ).integrable.norm
  · filter_upwards [xae_ne_zero hd] with ξ hξ
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_xσ_eq_one hξ] with n hn
    rw [hn]; simp

end HRS.Commutator.Whole.XNRS
