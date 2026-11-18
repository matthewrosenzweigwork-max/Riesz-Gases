import HRS.MS.R2SeAux5

/-!
# S9.9 `r2_static_edgeworth`, packet 6: the exact Stein identity (E1)

Worker S99, namespace `S99`.  `s99_E1`: for a corrector `χ` of a feature `w` (`S46Feat`), a summable feature family `φ`, an extra
bounded feature `b` and a `C¹` test function `Ψ : ℓ² × ℝ → ℝ` with bounded `Ψ, DΨ`:

`E[Y_w Ψ(W,Y_b)] = E[√N R_w Ψ(W,Y_b)] + ∑_l E[T_{wl} ∂_{e_l}Ψ(W,Y_b)] + E[T_{wb} ∂_yΨ(W,Y_b)]`

(`R_w = s45_Rp ...`, `T_{wl} = γ⁻¹ μ_N(⟨∇χ_w, ∇φ_l⟩)`), by `S46.s46_stein_id` applied to `F = Ψ ∘ Z`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

theorem s99_inner_grad_le {χ ψ : Euc d → ℝ} {B D : ℝ} (hχ : ∀ x, ‖gradient χ x‖ ≤ B)
    (hψ : ∀ x, ‖fderiv ℝ ψ x‖ ≤ D) (x : Euc d) :
    |⟪gradient χ x, gradient ψ x⟫| ≤ B * D := by
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [s45_norm_gradient ψ x]
  exact mul_le_mul (hχ x) (hψ x) (norm_nonneg _) ((norm_nonneg _).trans (hχ x))

theorem s99_E1 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β γ C c BU Cs : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hγ : 0 < γ) (hT : ThermalData d s a β C c BU) (hN : 2 ≤ N)
    (hS : S46.S46Static d s a β γ Cs N) {J : ℕ} (hJ : 1 ≤ J) {φ : ℕ → Euc d → ℝ}
    (hφ : IsSummableFeatureFamily J φ) {b : Euc d → ℝ} (hb : MemCb J b) {w χ : Euc d → ℝ}
    {Bw : ℝ} (hw : MemCb J w) (hwf : S46.S46Feat d s a β γ w χ Bw)
    {Ψ : SeqL2 × ℝ → ℝ} (hΨ : ContDiff ℝ 1 Ψ) {CΨ DΨ : ℝ} (hCΨ : ∀ p, |Ψ p| ≤ CΨ)
    (hDΨ : ∀ p, ‖fderiv ℝ Ψ p‖ ≤ DΨ) :
    ∫ X, s45_Yi N w (pair (S46.s46_nu d s a β γ N) w) X *
        Ψ (Zq N φ b (S46.s46_nu d s a β γ N) X) ∂(S46.s46_P d s a β γ N) =
      ∫ X, (Real.sqrt N * s45_Rp (thermalMeasure d s a β) (S46.s46_nu d s a β γ N)
          (S46.s46_P d s a β γ N) (commutatorKernel d s (gradient χ)) X) *
          Ψ (Zq N φ b (S46.s46_nu d s a β γ N) X) ∂(S46.s46_P d s a β γ N) +
      ∑' l, ∫ X, (γ⁻¹ * pair (empirical X) (fun x => ⟪gradient χ x, gradient (φ l) x⟫)) *
          fderiv ℝ Ψ (Zq N φ b (S46.s46_nu d s a β γ N) X) (s45_e1 l (1 : ℝ), 0)
          ∂(S46.s46_P d s a β γ N) +
      ∫ X, (γ⁻¹ * pair (empirical X) (fun x => ⟪gradient χ x, gradient b x⟫)) *
          fderiv ℝ Ψ (Zq N φ b (S46.s46_nu d s a β γ N) X) (0, 1) ∂(S46.s46_P d s a β γ N) := by
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  haveI hP : IsProbabilityMeasure (S46.s46_P d s a β γ N) := hS.prob
  set P := S46.s46_P d s a β γ N with hPdef
  set ν := S46.s46_nu d s a β γ N with hνdef
  haveI hνprob : IsProbabilityMeasure ν := s99_nu_prob hN1
  have hJ1 : (1 : WithTop ℕ∞) ≤ J := by exact_mod_cast hJ
  -- smoothness and bounds of `F = Ψ ∘ Z`
  have hZ : ContDiff ℝ 1 (fun X : EucConfig d N => Zq N φ b ν X) := s99_Z_contDiff hN1 hJ hφ hb
  have hF : ContDiff ℝ 1 (fun X : EucConfig d N => Ψ (Zq N φ b ν X)) := hΨ.comp hZ
  have hBF : ∀ X, |Ψ (Zq N φ b ν X)| ≤ CΨ := fun X => hCΨ _
  have hDΨ0 : 0 ≤ DΨ := le_trans (norm_nonneg (fderiv ℝ Ψ 0)) (hDΨ 0)
  set cb : ℕ → ℝ := fun l => cbNorm J (φ l) with hcb
  have hcb0 : ∀ l, 0 ≤ cb l := fun l => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hcbS : Summable cb := hφ.2
  set cbb : ℝ := cbNorm J b with hcbb
  have hcbb0 : 0 ≤ cbb := HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hDφ : ∀ l x, ‖fderiv ℝ (φ l) x‖ ≤ cb l := fun l x => s45_cb_deriv_le hJ (hφ.1 l) x
  have hDb : ∀ x, ‖fderiv ℝ b x‖ ≤ cbb := fun x => s45_cb_deriv_le hJ hb x
  have hdz : ∀ (X : EucConfig d N) (l : ℕ),
      |fderiv ℝ Ψ (Zq N φ b ν X) (s45_e1 l (1 : ℝ), 0)| ≤ DΨ := by
    intro X l
    rw [← Real.norm_eq_abs]
    refine ((fderiv ℝ Ψ _).le_opNorm _).trans ?_
    have : ‖((s45_e1 l (1 : ℝ), 0) : SeqL2 × ℝ)‖ = 1 := by
      rw [Prod.norm_def]; simp [s99_e1_norm]
    rw [this, mul_one]
    exact hDΨ _
  have hdy : ∀ X : EucConfig d N, |fderiv ℝ Ψ (Zq N φ b ν X) (0, 1)| ≤ DΨ := by
    intro X
    rw [← Real.norm_eq_abs]
    refine ((fderiv ℝ Ψ _).le_opNorm _).trans ?_
    have : ‖((0, 1) : SeqL2 × ℝ)‖ = 1 := by
      rw [Prod.norm_def]; simp
    rw [this, mul_one]
    exact hDΨ _
  set DF : ℝ := DΨ * (∑' l, Real.sqrt N * cb l + Real.sqrt N * cbb) with hDFdef
  have hDF : ∀ X, ‖fderiv ℝ (fun X : EucConfig d N => Ψ (Zq N φ b ν X)) X‖ ≤ DF := by
    intro X
    have hDF0 : 0 ≤ DF := by
      have : 0 ≤ ∑' l, Real.sqrt N * cb l := tsum_nonneg fun l => by have := hcb0 l; positivity
      positivity
    refine ContinuousLinearMap.opNorm_le_bound _ hDF0 fun u => ?_
    rw [s99_fderivF_apply hN1 hJ hφ hb hΨ X u, Real.norm_eq_abs]
    have hg : HasSum (fun l => (Real.sqrt N * cb l) * (‖u‖ * DΨ))
        ((∑' l, Real.sqrt N * cb l) * (‖u‖ * DΨ)) :=
      ((hcbS.mul_left (Real.sqrt N)).hasSum).mul_right _
    have h1 : ‖∑' l, s45_L N (φ l) X u * fderiv ℝ Ψ (Zq N φ b ν X) (s45_e1 l (1 : ℝ), 0)‖ ≤
        (∑' l, Real.sqrt N * cb l) * (‖u‖ * DΨ) := by
      refine tsum_of_norm_bounded hg fun l => ?_
      rw [Real.norm_eq_abs, abs_mul]
      have e1 := s45_L_bound (hD := fun x => hDφ l x) hN1 X u
      have e2 := hdz X l
      calc |s45_L N (φ l) X u| * |fderiv ℝ Ψ (Zq N φ b ν X) (s45_e1 l (1 : ℝ), 0)|
          ≤ (Real.sqrt N * cb l * ‖u‖) * DΨ :=
            mul_le_mul e1 e2 (abs_nonneg _) (by have := hcb0 l; positivity)
        _ = (Real.sqrt N * cb l) * (‖u‖ * DΨ) := by ring
    have h2 : |s45_L N b X u * fderiv ℝ Ψ (Zq N φ b ν X) (0, 1)| ≤
        (Real.sqrt N * cbb) * (‖u‖ * DΨ) := by
      rw [abs_mul]
      have e1 := s45_L_bound (hD := fun x => hDb x) hN1 X u
      have e2 := hdy X
      calc |s45_L N b X u| * |fderiv ℝ Ψ (Zq N φ b ν X) (0, 1)|
          ≤ (Real.sqrt N * cbb * ‖u‖) * DΨ := mul_le_mul e1 e2 (abs_nonneg _) (by positivity)
        _ = (Real.sqrt N * cbb) * (‖u‖ * DΨ) := by ring
    calc |(∑' l, s45_L N (φ l) X u * fderiv ℝ Ψ (Zq N φ b ν X) (s45_e1 l (1 : ℝ), 0)) +
            s45_L N b X u * fderiv ℝ Ψ (Zq N φ b ν X) (0, 1)|
        ≤ |∑' l, s45_L N (φ l) X u * fderiv ℝ Ψ (Zq N φ b ν X) (s45_e1 l (1 : ℝ), 0)| +
            |s45_L N b X u * fderiv ℝ Ψ (Zq N φ b ν X) (0, 1)| := abs_add_le _ _
      _ ≤ (∑' l, Real.sqrt N * cb l) * (‖u‖ * DΨ) + (Real.sqrt N * cbb) * (‖u‖ * DΨ) := by
          have := (Real.norm_eq_abs _ ▸ h1 : |∑' l, s45_L N (φ l) X u *
            fderiv ℝ Ψ (Zq N φ b ν X) (s45_e1 l (1 : ℝ), 0)| ≤ _)
          linarith
      _ = DF * ‖u‖ := by rw [hDFdef]; ring

  -- the corrector identity and the Stein identity of S4.6
  obtain ⟨c0, hstar⟩ := S46.s46_star hd hs0 hsd hγ hT hwf.smooth hwf.B1 hwf.B2 hwf.corr
  have hwc : ContDiff ℝ 1 w := hw.1.of_le hJ1
  have hwb : ∀ x, |w x| ≤ cbNorm J w := fun x => by
    have := HRS.MS.Tc5.tc5_cb_sup_le hw x
    rwa [Real.norm_eq_abs] at this
  have hid := S46.s46_stein_id hd hs0 hsd ha hβ hγ hN hT hS hwf.smooth hwf.B1 hwf.B2
    (φ := w) hwc.continuous.measurable hwb hstar hF hBF hDF
  -- the derivative along the corrector field
  have hχ1 : ContDiff ℝ 1 (gradient χ) := s45_contDiff_gradient hwf.smooth
  have hgχ : Continuous (gradient χ) := hχ1.continuous
  have hdFv : ∀ X : EucConfig d N,
      fderiv ℝ (fun X : EucConfig d N => Ψ (Zq N φ b ν X)) X (fun k => gradient χ (X k)) =
        (∑' l, (Real.sqrt N * pair (empirical X) (fun x => ⟪gradient χ x, gradient (φ l) x⟫)) *
          fderiv ℝ Ψ (Zq N φ b ν X) (s45_e1 l (1 : ℝ), 0)) +
        (Real.sqrt N * pair (empirical X) (fun x => ⟪gradient χ x, gradient b x⟫)) *
          fderiv ℝ Ψ (Zq N φ b ν X) (0, 1) := by
    intro X
    rw [s99_fderivF_apply hN1 hJ hφ hb hΨ X]
    simp_rw [s99_L_chi hN1 X]
  set cst : ℝ := Real.sqrt N * (γ * N)⁻¹ with hcst
  have hcst2 : cst * Real.sqrt N = γ⁻¹ := by
    rw [hcst]
    field_simp
    exact Real.sq_sqrt hN0.le
  set g : ℕ → EucConfig d N → ℝ := fun l X =>
    (γ⁻¹ * pair (empirical X) (fun x => ⟪gradient χ x, gradient (φ l) x⟫)) *
      fderiv ℝ Ψ (Zq N φ b ν X) (s45_e1 l (1 : ℝ), 0) with hgdef
  set gb : EucConfig d N → ℝ := fun X =>
    (γ⁻¹ * pair (empirical X) (fun x => ⟪gradient χ x, gradient b x⟫)) *
      fderiv ℝ Ψ (Zq N φ b ν X) (0, 1) with hgbdef
  have hpt : ∀ X : EucConfig d N, cst *
      fderiv ℝ (fun X : EucConfig d N => Ψ (Zq N φ b ν X)) X (fun k => gradient χ (X k)) =
        (∑' l, g l X) + gb X := by
    intro X
    rw [hdFv X, mul_add, ← tsum_mul_left]
    congr 1
    · refine tsum_congr fun l => ?_
      simp only [hgdef]
      rw [← hcst2]; ring
    · simp only [hgbdef]
      rw [← hcst2]; ring
  -- measurability / bounds of the terms
  have hZc : Continuous (fun X : EucConfig d N => Zq N φ b ν X) := hZ.continuous
  have hfdc : Continuous (fun X : EucConfig d N => fderiv ℝ Ψ (Zq N φ b ν X)) :=
    (hΨ.continuous_fderiv one_ne_zero).comp hZc
  have hΨzm : ∀ l, Measurable fun X : EucConfig d N =>
      fderiv ℝ Ψ (Zq N φ b ν X) (s45_e1 l (1 : ℝ), 0) := fun l =>
    (hfdc.clm_apply continuous_const).measurable
  have hΨym : Measurable fun X : EucConfig d N => fderiv ℝ Ψ (Zq N φ b ν X) (0, 1) :=
    (hfdc.clm_apply continuous_const).measurable
  have hpm : ∀ {ψ : Euc d → ℝ}, ContDiff ℝ 1 ψ → Measurable fun X : EucConfig d N =>
      pair (empirical X) (fun x => ⟪gradient χ x, gradient ψ x⟫) := fun {ψ} hψ =>
    s45_measurable_pair_empirical hN1 (hgχ.inner (s45_gradient_continuous hψ)).measurable
  have hgl_meas : ∀ l, Measurable (g l) := fun l =>
    (measurable_const.mul (hpm ((hφ.1 l).1.of_le hJ1))).mul (hΨzm l)
  have hgb_meas : Measurable gb :=
    (measurable_const.mul (hpm (hb.1.of_le hJ1))).mul hΨym
  have hγ0 : 0 ≤ γ⁻¹ := inv_nonneg.2 hγ.le
  have hBw0 : 0 ≤ Bw := (norm_nonneg _).trans (hwf.B1 0)
  have hgl_bd : ∀ l X, |g l X| ≤ γ⁻¹ * (Bw * cb l) * DΨ := by
    intro l X
    simp only [hgdef]
    rw [abs_mul, abs_mul, abs_of_nonneg hγ0]
    have h1 := s45_abs_pair_empirical_le hN1 (fun x => s99_inner_grad_le hwf.B1 (hDφ l) x) X
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hγ0) (hdz X l) (abs_nonneg _) (by
      have := hcb0 l; positivity)
  have hgb_bd : ∀ X, |gb X| ≤ γ⁻¹ * (Bw * cbb) * DΨ := by
    intro X
    simp only [hgbdef]
    rw [abs_mul, abs_mul, abs_of_nonneg hγ0]
    have h1 := s45_abs_pair_empirical_le hN1 (fun x => s99_inner_grad_le hwf.B1 hDb x) X
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hγ0) (hdy X) (abs_nonneg _) (by positivity)
  have hgl_int : ∀ l, Integrable (g l) P := fun l =>
    Integrable.of_bound (hgl_meas l).aestronglyMeasurable _
      (Filter.Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hgl_bd l X)
  have hgb_int : Integrable gb P :=
    Integrable.of_bound hgb_meas.aestronglyMeasurable _
      (Filter.Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hgb_bd X)
  have hg_sum : Summable fun l => ∫ X, ‖g l X‖ ∂P := by
    refine Summable.of_nonneg_of_le (fun l => integral_nonneg fun X => norm_nonneg _)
      (fun l => ?_) (hcbS.mul_left (γ⁻¹ * Bw * DΨ))
    calc ∫ X, ‖g l X‖ ∂P ≤ ∫ X, γ⁻¹ * (Bw * cb l) * DΨ ∂P :=
          integral_mono (hgl_int l).norm (integrable_const _)
            (fun X => by rw [Real.norm_eq_abs]; exact hgl_bd l X)
      _ = γ⁻¹ * Bw * DΨ * cb l := by
          rw [integral_const]; simp; ring
  have hsumInt := integral_tsum_of_summable_integral_norm hgl_int hg_sum
  -- integrability of the derivative term
  have hv_bd : ∀ X : EucConfig d N, ‖(fun k => gradient χ (X k))‖ ≤ Bw := fun X =>
    (pi_norm_le_iff_of_nonneg hBw0).2 fun k => hwf.B1 (X k)
  have hdFc : Continuous fun X : EucConfig d N =>
      fderiv ℝ (fun X : EucConfig d N => Ψ (Zq N φ b ν X)) X (fun k => gradient χ (X k)) :=
    (hF.continuous_fderiv one_ne_zero).clm_apply (continuous_pi fun k => hgχ.comp (continuous_apply k))
  have hdF_int : Integrable (fun X : EucConfig d N =>
      fderiv ℝ (fun X : EucConfig d N => Ψ (Zq N φ b ν X)) X (fun k => gradient χ (X k))) P := by
    refine Integrable.of_bound hdFc.aestronglyMeasurable (DF * Bw)
      (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, ← Real.norm_eq_abs]
    refine ((fderiv ℝ _ X).le_opNorm _).trans ?_
    exact mul_le_mul (hDF X) (hv_bd X) (norm_nonneg _) ((norm_nonneg _).trans (hDF X))
  have hsum_int : Integrable (fun X : EucConfig d N => ∑' l, g l X) P := by
    have : (fun X : EucConfig d N => ∑' l, g l X) = fun X => cst *
        fderiv ℝ (fun X : EucConfig d N => Ψ (Zq N φ b ν X)) X (fun k => gradient χ (X k)) - gb X :=
      funext fun X => by rw [hpt X]; ring
    rw [this]
    exact (hdF_int.const_mul cst).sub hgb_int
  -- assemble
  have hid' : ∫ X, (pair (empirical X) w - pair ν w) * Ψ (Zq N φ b ν X) ∂P =
      ∫ X, s45_Rp (thermalMeasure d s a β) ν P (commutatorKernel d s (gradient χ)) X *
        Ψ (Zq N φ b ν X) ∂P +
      (γ * N)⁻¹ * ∫ X, fderiv ℝ (fun X : EucConfig d N => Ψ (Zq N φ b ν X)) X
        (fun k => gradient χ (X k)) ∂P := hid
  have hL : ∫ X, s45_Yi N w (pair ν w) X * Ψ (Zq N φ b ν X) ∂P =
      Real.sqrt N * ∫ X, (pair (empirical X) w - pair ν w) * Ψ (Zq N φ b ν X) ∂P := by
    rw [← integral_const_mul]
    congr 1; funext X; simp only [s45_Yi]; ring
  have hR : ∫ X, (Real.sqrt N * s45_Rp (thermalMeasure d s a β) ν P
        (commutatorKernel d s (gradient χ)) X) * Ψ (Zq N φ b ν X) ∂P =
      Real.sqrt N * ∫ X, s45_Rp (thermalMeasure d s a β) ν P (commutatorKernel d s (gradient χ)) X *
        Ψ (Zq N φ b ν X) ∂P := by
    rw [← integral_const_mul]
    congr 1; funext X; ring
  have hTm : Real.sqrt N * ((γ * N)⁻¹ * ∫ X, fderiv ℝ (fun X : EucConfig d N => Ψ (Zq N φ b ν X)) X
      (fun k => gradient χ (X k)) ∂P) = (∑' l, ∫ X, g l X ∂P) + ∫ X, gb X ∂P := by
    have e1 : Real.sqrt N * ((γ * N)⁻¹ * ∫ X, fderiv ℝ (fun X : EucConfig d N => Ψ (Zq N φ b ν X)) X
        (fun k => gradient χ (X k)) ∂P) = ∫ X, cst * fderiv ℝ (fun X : EucConfig d N =>
          Ψ (Zq N φ b ν X)) X (fun k => gradient χ (X k)) ∂P := by
      rw [integral_const_mul, hcst]; ring
    rw [e1]
    have e2 : ∫ X, cst * fderiv ℝ (fun X : EucConfig d N => Ψ (Zq N φ b ν X)) X
        (fun k => gradient χ (X k)) ∂P = ∫ X, ((∑' l, g l X) + gb X) ∂P := by
      congr 1; funext X; exact hpt X
    rw [e2, integral_add hsum_int hgb_int, ← hsumInt]
  rw [hL, hR, hid', mul_add, hTm]
  ring

end S99

end
