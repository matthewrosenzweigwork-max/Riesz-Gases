import HRS.MS.SpecAux78

/-!
# S8L: Gaussian log-Sobolev inequality for compactly supported `C²` functions (S8.7, block L)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_gauss_lsi_cs`: for `u ∈ C²` with compact support and `δ > 0`,
`Ent_γ(u² + δ) ≤ 2 ∫ ‖Du‖² dγ`.  Also `s8p_bdd_of_cs` (compactly supported `C¹` functions lie in the bounded class) and the
smoothness/support of the Fisher integrand of `u² + δ`.
-/

noncomputable section

open MeasureTheory Real

namespace HRS.MS.Spec

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem s8p_bdd_of_cs {g : V → ℝ} (hg : ContDiff ℝ 1 g) (hcs : HasCompactSupport g) (c : ℝ) :
    ∃ M0 M1, S8pBdd (fun x => g x + c) M0 M1 := by
  obtain ⟨B0, hB0⟩ := hg.continuous.bounded_above_of_compact_support hcs
  have hd : HasCompactSupport (fderiv ℝ g) := hcs.fderiv ℝ
  obtain ⟨B1, hB1⟩ := (hg.continuous_fderiv one_ne_zero).bounded_above_of_compact_support hd
  refine ⟨B0 + |c|, B1, hg.add contDiff_const, fun x => ?_, fun x => ?_⟩
  · calc |g x + c| ≤ |g x| + |c| := abs_add_le _ _
      _ ≤ B0 + |c| := by have := hB0 x; rw [Real.norm_eq_abs] at this; linarith
  · have : fderiv ℝ (fun x => g x + c) x = fderiv ℝ g x := by
      rw [fderiv_add_const]
    rw [this]; exact hB1 x

/-- Smoothness of the Fisher integrand of `u² + δ`. -/
theorem s8p_Fish_contDiff {u : V → ℝ} (hu : ContDiff ℝ 2 u) {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ 1 (s8p_Fish (fun x => u x ^ 2 + δ)) := by
  set f : V → ℝ := fun x => u x ^ 2 + δ with hf
  have hf2 : ContDiff ℝ 2 f := (hu.pow 2).add contDiff_const
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) := hf2.fderiv_right (by norm_num)
  set b := stdOrthonormalBasis ℝ V
  have e : s8p_Fish f = fun x => (∑ i, (fderiv ℝ f x (b i)) ^ 2) / f x := by
    funext x
    unfold s8p_Fish
    rw [OrthonormalBasis.norm_dual b]
  rw [e]
  refine ContDiff.div (ContDiff.sum fun i _ => ?_) (hf2.of_le (by norm_num)) (fun x => ?_)
  · exact (hfd.clm_apply contDiff_const).pow 2
  · have : 0 < u x ^ 2 + δ := by positivity
    exact this.ne'


theorem s8p_fderiv_sq_add {u : V → ℝ} (hu : ContDiff ℝ 2 u) (δ : ℝ) (x : V) :
    fderiv ℝ (fun x => u x ^ 2 + δ) x = (2 * u x) • fderiv ℝ u x := by
  have hu' : HasFDerivAt u (fderiv ℝ u x) x :=
    ((hu.differentiable (by norm_num)) x).hasFDerivAt
  have := ((hasDerivAt_pow 2 (u x)).comp_hasFDerivAt x hu').add_const δ
  have e : (fun x => u x ^ 2 + δ) = fun x => ((fun x => x ^ 2) ∘ u) x + δ := rfl
  rw [e, this.fderiv]
  simp

theorem s8p_Fish_eq {u : V → ℝ} (hu : ContDiff ℝ 2 u) {δ : ℝ} (hδ : 0 < δ) (x : V) :
    s8p_Fish (fun x => u x ^ 2 + δ) x = 4 * u x ^ 2 * ‖fderiv ℝ u x‖ ^ 2 / (u x ^ 2 + δ) := by
  unfold s8p_Fish
  rw [s8p_fderiv_sq_add hu, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

theorem s8p_Fish_le {u : V → ℝ} (hu : ContDiff ℝ 2 u) {δ : ℝ} (hδ : 0 < δ) (x : V) :
    s8p_Fish (fun x => u x ^ 2 + δ) x ≤ 4 * ‖fderiv ℝ u x‖ ^ 2 := by
  rw [s8p_Fish_eq hu hδ, div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (‖fderiv ℝ u x‖), sq_nonneg (u x), mul_nonneg (sq_nonneg ‖fderiv ℝ u x‖) hδ.le]

theorem s8p_Fish_cs {u : V → ℝ} (hu : ContDiff ℝ 2 u) (hcs : HasCompactSupport u) {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (s8p_Fish (fun x => u x ^ 2 + δ)) := by
  refine HasCompactSupport.intro hcs (fun x hx => ?_)
  have : u x = 0 := image_eq_zero_of_notMem_tsupport hx
  rw [s8p_Fish_eq hu hδ, this]; simp

/-- **Gaussian log-Sobolev inequality** for `C²` functions of compact support, with a shift `δ > 0`. -/
theorem s8p_gauss_lsi_cs {u : V → ℝ} (hu : ContDiff ℝ 2 u) (hcs : HasCompactSupport u) {δ : ℝ}
    (hδ : 0 < δ) :
    (∫ x, ((u x ^ 2 + δ) * Real.log (u x ^ 2 + δ)) * s8p_gd x) -
        (∫ x, (u x ^ 2 + δ) * s8p_gd x) * Real.log (∫ x, (u x ^ 2 + δ) * s8p_gd x) ≤
      2 * ∫ x, ‖fderiv ℝ u x‖ ^ 2 * s8p_gd x := by
  obtain ⟨M0, M1, hf⟩ := s8p_bdd_of_cs ((hu.of_le (by norm_num)).pow 2) (hcs.mul_left) δ
  obtain ⟨N0, N1, hF⟩ := s8p_bdd_of_cs (s8p_Fish_contDiff hu hδ) (s8p_Fish_cs hu hcs hδ) 1
  have hge : ∀ x, δ ≤ u x ^ 2 + δ := fun x => by nlinarith [sq_nonneg (u x)]
  have h := s8p_gauss_ent hδ hf hge hF
  have hint : Integrable (fun x : V => ‖fderiv ℝ u x‖ ^ 2 * s8p_gd x) := by
    have hd : HasCompactSupport (fderiv ℝ u) := hcs.fderiv ℝ
    obtain ⟨B, hB⟩ := ((hu.continuous_fderiv (by norm_num))).bounded_above_of_compact_support hd
    refine Integrable.mono' (s8p_gd_integrable.const_mul (B ^ 2))
      (((hu.continuous_fderiv (by norm_num)).norm.pow 2).mul s8p_gd_continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_of_nonneg (s8p_gd_pos x).le, Real.norm_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_right ?_ (s8p_gd_pos x).le
    exact pow_le_pow_left₀ (norm_nonneg _) (hB x) 2
  have hFint : Integrable (fun x => s8p_Fish (fun x => u x ^ 2 + δ) x * s8p_gd x) := by
    refine Integrable.mono' (hint.const_mul 4)
      (((s8p_Fish_contDiff hu hδ).continuous).mul s8p_gd_continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    have h0 : 0 ≤ s8p_Fish (fun x => u x ^ 2 + δ) x := by
      rw [s8p_Fish_eq hu hδ]; positivity
    rw [norm_mul, Real.norm_of_nonneg (s8p_gd_pos x).le, Real.norm_of_nonneg h0]
    have := mul_le_mul_of_nonneg_right (s8p_Fish_le hu hδ x) (s8p_gd_pos x).le
    linarith
  have h2 : ∫ x, s8p_Fish (fun x => u x ^ 2 + δ) x * s8p_gd x ≤ 4 * ∫ x, ‖fderiv ℝ u x‖ ^ 2 * s8p_gd x := by
    rw [← integral_const_mul]
    refine integral_mono hFint (hint.const_mul 4) (fun x => ?_)
    have := mul_le_mul_of_nonneg_right (s8p_Fish_le hu hδ x) (s8p_gd_pos x).le
    linarith
  linarith

end HRS.MS.Spec
