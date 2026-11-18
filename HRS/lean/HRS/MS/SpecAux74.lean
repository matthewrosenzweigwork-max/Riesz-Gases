import HRS.MS.SpecAux73

/-!
# S8L: Gaussian integration by parts identity for the interpolation `P_θ` (S8.7, Gaussian log-Sobolev)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_KL`: for `f, ψ ∈ C¹` with bounded values and derivatives,
`∫ ψ ∂_θ P_θ f dγ = -sin θ ∫ (P_θ Df)(∇ψ) dγ` (three one-directional Gaussian integrations by parts, the second-derivative
terms cancel; Fubini on `V × V`).
-/

noncomputable section

open MeasureTheory Real

namespace HRS.MS.Spec

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {f ψ : V → ℝ} {M0 M1 B0 B1 : ℝ}

theorem s8p_hasFDerivAt_x (hf : S8pBdd f M0 M1) (θ : ℝ) (y x : V) :
    HasFDerivAt (fun x : V => f (Real.cos θ • x + Real.sin θ • y))
      (Real.cos θ • fderiv ℝ f (Real.cos θ • x + Real.sin θ • y)) x := by
  have h1 : HasFDerivAt (fun x : V => Real.cos θ • x + Real.sin θ • y)
      (Real.cos θ • ContinuousLinearMap.id ℝ V) x := by
    simpa using ((hasFDerivAt_id x).const_smul (Real.cos θ)).add_const (Real.sin θ • y)
  have h2 := (hf.cont.differentiable one_ne_zero (Real.cos θ • x + Real.sin θ • y)).hasFDerivAt.comp x h1
  refine h2.congr_fderiv ?_
  ext v; simp

theorem s8p_hasFDerivAt_y (hf : S8pBdd f M0 M1) (θ : ℝ) (x y : V) :
    HasFDerivAt (fun y : V => f (Real.cos θ • x + Real.sin θ • y))
      (Real.sin θ • fderiv ℝ f (Real.cos θ • x + Real.sin θ • y)) y := by
  have h1 : HasFDerivAt (fun y : V => Real.cos θ • x + Real.sin θ • y)
      (Real.sin θ • ContinuousLinearMap.id ℝ V) y := by
    simpa using ((hasFDerivAt_id y).const_smul (Real.sin θ)).const_add (Real.cos θ • x)
  have h2 := (hf.cont.differentiable one_ne_zero (Real.cos θ • x + Real.sin θ • y)).hasFDerivAt.comp y h1
  refine h2.congr_fderiv ?_
  ext v; simp

/-- IBP in `x`, for fixed `y`. -/
theorem s8p_ibp_x (hf : S8pBdd f M0 M1) (hψ : S8pBdd ψ B0 B1) (θ : ℝ) (y : V) :
    ∫ x, s8p_H1 f ψ θ (x, y) * s8p_gd x =
      -∫ x, (s8p_H3 f ψ θ (x, y) - s8p_H4 f ψ θ (x, y)) * s8p_gd x := by
  obtain ⟨c1, c2, c3, c4⟩ := s8p_H_cont hf hψ θ
  have hcx : ∀ H : V × V → ℝ, Continuous H → Continuous fun x : V => H (x, y) := fun H hH =>
    hH.comp (by fun_prop)
  set Kc := B0 * M1 + B1 * M0 + B0 * M0
  have hbx : ∀ H : V × V → ℝ, (∀ p, |H p| ≤ Kc * ((1 + ‖p.1‖) * (1 + ‖p.2‖))) →
      ∀ x, |H (x, y)| ≤ (Kc * (1 + ‖y‖)) * (1 + ‖x‖) := fun H hH x => by
    have := hH (x, y); simp only at this; nlinarith
  have i1 := s8p_int_gd (hcx _ c1) (hbx _ (fun p => (s8p_H_bd hf hψ θ p).1))
  have i34 := s8p_int_gd ((hcx _ c3).sub (hcx _ c4)) (K := 2 * (Kc * (1 + ‖y‖))) (fun x => by
    have h3 := hbx _ (fun p => (s8p_H_bd hf hψ θ p).2.2.1) x
    have h4 := hbx _ (fun p => (s8p_H_bd hf hψ θ p).2.2.2) x
    simp only [Pi.sub_apply]
    calc _ ≤ |s8p_H3 f ψ θ (x, y)| + |s8p_H4 f ψ θ (x, y)| := abs_sub _ _
      _ ≤ _ := by nlinarith)
  -- the functions a = ψ gd and q = f(c x + s y)
  have hq := s8p_hasFDerivAt_x hf θ y
  have ha : ∀ x, HasFDerivAt (fun x => ψ x * s8p_gd x)
      (ψ x • ((-(s8p_gd x)) • innerSL ℝ x) + s8p_gd x • fderiv ℝ ψ x) x := fun x =>
    (hψ.cont.differentiable one_ne_zero x).hasFDerivAt.mul (s8p_gd_hasFDerivAt x)
  have h0 : Integrable (fun x : V => (ψ x * f (Real.cos θ • x + Real.sin θ • y)) * s8p_gd x) := by
    refine s8p_int_gd ((hψ.cont'.mul (hf.cont'.comp (by fun_prop)))) (K := B0 * M0) (fun x => ?_)
    rw [abs_mul]
    have := mul_le_mul (hψ.bd0 x) (hf.bd0 (Real.cos θ • x + Real.sin θ • y)) (abs_nonneg _)
      (by have := (abs_nonneg _).trans (hψ.bd0 x); exact this)
    nlinarith [norm_nonneg x, mul_nonneg ((abs_nonneg _).trans (hψ.bd0 x)) ((abs_nonneg _).trans (hf.bd0 0))]
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure V))
    (f := fun x => ψ x * s8p_gd x) (g := fun x => f (Real.cos θ • x + Real.sin θ • y)) (v := y)
    (by
      refine i34.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [(ha x).fderiv, (hq x).fderiv, s8p_H3, s8p_H4]
      simp [innerSL_apply_apply]; ring)
    (by
      refine i1.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [(s8p_hasFDerivAt_x hf θ y x).fderiv, s8p_H1]
      simp; ring)
    (by refine h0.congr (Filter.Eventually.of_forall fun x => ?_); simp only; ring)
    (fun x _ => (ha x).differentiableAt) (fun x _ => (s8p_hasFDerivAt_x hf θ y x).differentiableAt)
  calc ∫ x, s8p_H1 f ψ θ (x, y) * s8p_gd x
      = ∫ x, (ψ x * s8p_gd x) * fderiv ℝ (fun x => f (Real.cos θ • x + Real.sin θ • y)) x y := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [(hq x).fderiv, s8p_H1]; simp; ring
    _ = -∫ x, fderiv ℝ (fun x => ψ x * s8p_gd x) x y * f (Real.cos θ • x + Real.sin θ • y) := this
    _ = _ := by
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [(ha x).fderiv, s8p_H3, s8p_H4]; simp [innerSL_apply_apply]; ring


/-- IBP in `y`, for fixed `x`. -/
theorem s8p_ibp_y (hf : S8pBdd f M0 M1) (hψ : S8pBdd ψ B0 B1) (θ : ℝ) (x : V) :
    ∫ y, s8p_H2 f ψ θ (x, y) * s8p_gd y = ∫ y, s8p_H4 f ψ θ (x, y) * s8p_gd y := by
  have hq := s8p_hasFDerivAt_y hf θ x
  have hQc : Continuous fun y : V => f (Real.cos θ • x + Real.sin θ • y) :=
    hf.cont'.comp (by fun_prop)
  have hKc : Continuous fun y : V => fderiv ℝ f (Real.cos θ • x + Real.sin θ • y) :=
    (hf.cont.continuous_fderiv one_ne_zero).comp (by fun_prop)
  have hi1 : Integrable (fun y : V => (Real.sin θ * fderiv ℝ f (Real.cos θ • x + Real.sin θ • y) x) *
      s8p_gd y) := by
    refine s8p_int_gd (continuous_const.mul (hKc.clm_apply continuous_const)) (K := M1 * ‖x‖)
      (fun y => ?_)
    rw [abs_mul]
    have := Real.abs_sin_le_one θ
    have h2 := s8p_clm_le (fderiv ℝ f (Real.cos θ • x + Real.sin θ • y)) x
    have h3 := hf.bd1 (Real.cos θ • x + Real.sin θ • y)
    have : |fderiv ℝ f (Real.cos θ • x + Real.sin θ • y) x| ≤ M1 * ‖x‖ :=
      h2.trans (mul_le_mul_of_nonneg_right h3 (norm_nonneg _))
    have h4 := mul_nonneg hf.M1_nonneg (norm_nonneg x)
    nlinarith [norm_nonneg y, abs_nonneg (fderiv ℝ f (Real.cos θ • x + Real.sin θ • y) x)]
  have hi2 : Integrable (fun y : V => (-(s8p_gd y) * inner ℝ y x) * f (Real.cos θ • x + Real.sin θ • y)) := by
    have := s8p_int_gd (H := fun y : V => -(inner ℝ y x * f (Real.cos θ • x + Real.sin θ • y)))
      (((continuous_id.inner continuous_const).mul hQc).neg) (K := ‖x‖ * M0) (fun y => by
        rw [abs_neg, abs_mul]
        have h1 : |inner ℝ y x| ≤ ‖y‖ * ‖x‖ := by
          simpa [Real.norm_eq_abs] using abs_real_inner_le_norm y x
        have h2 := hf.bd0 (Real.cos θ • x + Real.sin θ • y)
        have h3 := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        have h4 := mul_nonneg (norm_nonneg x) hf.M0_nonneg
        nlinarith [norm_nonneg y])
    exact this.congr (Filter.Eventually.of_forall fun y => by simp only; ring)
  have hi3 : Integrable (fun y : V => s8p_gd y * f (Real.cos θ • x + Real.sin θ • y)) := by
    have := s8p_int_gd (H := fun y : V => f (Real.cos θ • x + Real.sin θ • y)) hQc (K := M0)
      (fun y => by nlinarith [hf.bd0 (Real.cos θ • x + Real.sin θ • y), norm_nonneg y, hf.M0_nonneg])
    exact this.congr (Filter.Eventually.of_forall fun y => by simp only; ring)
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure V))
    (f := s8p_gd) (g := fun y => f (Real.cos θ • x + Real.sin θ • y)) (v := x)
    (by refine hi2.congr (Filter.Eventually.of_forall fun y => ?_); simp [s8p_gd_fderiv_apply])
    (by refine hi1.congr (Filter.Eventually.of_forall fun y => ?_); simp [(hq y).fderiv]; ring)
    hi3 (fun y _ => s8p_gd_differentiable y) (fun y _ => (hq y).differentiableAt)
  have e2 : ∫ y, s8p_H2 f ψ θ (x, y) * s8p_gd y = ψ x * ∫ y, s8p_gd y *
      fderiv ℝ (fun y => f (Real.cos θ • x + Real.sin θ • y)) y x := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [(hq y).fderiv, s8p_H2]; simp; ring
  have e4 : ∫ y, s8p_H4 f ψ θ (x, y) * s8p_gd y = ψ x * (-∫ y,
      fderiv ℝ s8p_gd y x * f (Real.cos θ • x + Real.sin θ • y)) := by
    rw [← integral_neg, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [s8p_gd_fderiv_apply, s8p_H4]
    rw [real_inner_comm]; ring
  rw [e2, e4, this]


/-- The Riesz vector of the differential of `ψ`. -/
def s8p_w (ψ : V → ℝ) (x : V) : V := (InnerProductSpace.toDual ℝ V).symm (fderiv ℝ ψ x)

/-- Gaussian IBP in `y` for fixed `x`. -/
theorem s8p_stein_y (hf : S8pBdd f M0 M1) (hψ : S8pBdd ψ B0 B1) (θ : ℝ) (x : V) :
    ∫ y, s8p_H3 f ψ θ (x, y) * s8p_gd y = Real.sin θ * s8p_Pd f θ x (s8p_w ψ x) := by
  set v := s8p_w ψ x with hv
  have hq := s8p_hasFDerivAt_y hf θ x
  have hQc : Continuous fun y : V => f (Real.cos θ • x + Real.sin θ • y) :=
    hf.cont'.comp (by fun_prop)
  have hKc : Continuous fun y : V => fderiv ℝ f (Real.cos θ • x + Real.sin θ • y) :=
    (hf.cont.continuous_fderiv one_ne_zero).comp (by fun_prop)
  have hD : ∀ y, fderiv ℝ ψ x y = inner ℝ y v := fun y => by
    rw [hv, s8p_w, real_inner_comm, InnerProductSpace.toDual_symm_apply]
  have h1 : Integrable (fun y : V => f (Real.cos θ • x + Real.sin θ • y) * inner ℝ y v * s8p_gd y) := by
    refine s8p_int_gd ((hQc.mul (continuous_id.inner continuous_const))) (K := M0 * ‖v‖) (fun y => ?_)
    rw [abs_mul]
    have h1 : |inner ℝ y v| ≤ ‖y‖ * ‖v‖ := by
      simpa [Real.norm_eq_abs] using abs_real_inner_le_norm y v
    have h2 := hf.bd0 (Real.cos θ • x + Real.sin θ • y)
    have h3 := mul_le_mul h2 h1 (abs_nonneg _) hf.M0_nonneg
    have h4 := mul_nonneg hf.M0_nonneg (norm_nonneg v)
    nlinarith [norm_nonneg y]
  have h2 : Integrable (fun y : V => fderiv ℝ (fun y => f (Real.cos θ • x + Real.sin θ • y)) y v * s8p_gd y) := by
    refine s8p_int_gd (H := fun y => fderiv ℝ (fun y => f (Real.cos θ • x + Real.sin θ • y)) y v) ?_
      (K := M1 * ‖v‖) (fun y => ?_)
    · simp only [fun y => (hq y).fderiv]
      exact (continuous_const.mul (hKc.clm_apply continuous_const) : Continuous fun y : V =>
        Real.sin θ * fderiv ℝ f (Real.cos θ • x + Real.sin θ • y) v)
    · simp only [(hq y).fderiv]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [abs_mul]
      have := Real.abs_sin_le_one θ
      have h2 := s8p_clm_le (fderiv ℝ f (Real.cos θ • x + Real.sin θ • y)) v
      have h3 := hf.bd1 (Real.cos θ • x + Real.sin θ • y)
      have : |fderiv ℝ f (Real.cos θ • x + Real.sin θ • y) v| ≤ M1 * ‖v‖ :=
        h2.trans (mul_le_mul_of_nonneg_right h3 (norm_nonneg _))
      have h4 := mul_nonneg hf.M1_nonneg (norm_nonneg v)
      nlinarith [norm_nonneg y, abs_nonneg (fderiv ℝ f (Real.cos θ • x + Real.sin θ • y) v)]
  have h3 : Integrable (fun y : V => f (Real.cos θ • x + Real.sin θ • y) * s8p_gd y) :=
    s8p_f_aff_integrable hf _ _ x
  have hst := s8p_stein (h := fun y => f (Real.cos θ • x + Real.sin θ • y))
    (fun y => (hq y).differentiableAt) v h1 h2 h3
  have e1 : ∫ y, s8p_H3 f ψ θ (x, y) * s8p_gd y =
      ∫ y, f (Real.cos θ • x + Real.sin θ • y) * inner ℝ y v * s8p_gd y := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [s8p_H3, hD]; ring
  rw [e1, hst]
  have hPd : s8p_Pd f θ x v = ∫ y, s8p_gd y * fderiv ℝ f (Real.cos θ • x + Real.sin θ • y) v := by
    unfold s8p_Pd
    rw [ContinuousLinearMap.integral_apply (s8p_Df_aff_integrable hf _ _ x)]
    rfl
  rw [hPd, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [(hq y).fderiv]; simp; ring


/-- **Key identity** `∫ ψ ∂_θ P_θ f dγ = -sin θ ∫ ⟨∇ψ, P_θ (Df)⟩ dγ`. -/
theorem s8p_KL (hf : S8pBdd f M0 M1) (hψ : S8pBdd ψ B0 B1) (θ : ℝ) :
    ∫ x, ψ x * s8p_Pth f θ x * s8p_gd x =
      -(Real.sin θ * ∫ x, s8p_Pd f θ x (s8p_w ψ x) * s8p_gd x) := by
  obtain ⟨i1, i2, i3, i4⟩ := s8p_H_int hf hψ θ
  have i12 := i1.sub i2
  have i34 := i3.sub i4
  -- LHS as a product integral
  have hL : ∫ x, ψ x * s8p_Pth f θ x * s8p_gd x = ∫ p, (s8p_H1 f ψ θ p * s8p_gd p.1 * s8p_gd p.2) -
      (s8p_H2 f ψ θ p * s8p_gd p.1 * s8p_gd p.2) ∂(volume.prod volume) := by
    rw [integral_prod (fun p : V × V => (s8p_H1 f ψ θ p * s8p_gd p.1 * s8p_gd p.2) -
      (s8p_H2 f ψ θ p * s8p_gd p.1 * s8p_gd p.2)) i12]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    unfold s8p_Pth
    rw [mul_assoc, mul_comm (∫ y, _) (s8p_gd x), ← mul_assoc, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [s8p_H1, s8p_H2, map_add, map_smul, smul_eq_mul]
    ring
  -- ∫F1 = -∫(F3 - F4)
  have h1 : ∫ p, s8p_H1 f ψ θ p * s8p_gd p.1 * s8p_gd p.2 ∂(volume.prod volume) =
      -∫ p, (s8p_H3 f ψ θ p * s8p_gd p.1 * s8p_gd p.2 - s8p_H4 f ψ θ p * s8p_gd p.1 * s8p_gd p.2)
        ∂(volume.prod volume) := by
    rw [integral_prod_symm _ i1, integral_prod_symm (fun p : V × V => s8p_H3 f ψ θ p * s8p_gd p.1 * s8p_gd p.2 -
      s8p_H4 f ψ θ p * s8p_gd p.1 * s8p_gd p.2) i34, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have := s8p_ibp_x hf hψ θ y
    have e1 : ∫ x, s8p_H1 f ψ θ (x, y) * s8p_gd x * s8p_gd y =
        (∫ x, s8p_H1 f ψ θ (x, y) * s8p_gd x) * s8p_gd y := integral_mul_const _ _
    have e2 : ∫ x, (s8p_H3 f ψ θ (x, y) * s8p_gd x * s8p_gd y - s8p_H4 f ψ θ (x, y) * s8p_gd x * s8p_gd y) =
        (∫ x, (s8p_H3 f ψ θ (x, y) - s8p_H4 f ψ θ (x, y)) * s8p_gd x) * s8p_gd y := by
      rw [← integral_mul_const]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only; ring
    simp only
    rw [e1, e2, this]; ring
  have h2 : ∫ p, s8p_H2 f ψ θ p * s8p_gd p.1 * s8p_gd p.2 ∂(volume.prod volume) =
      ∫ p, s8p_H4 f ψ θ p * s8p_gd p.1 * s8p_gd p.2 ∂(volume.prod volume) := by
    rw [integral_prod _ i2, integral_prod _ i4]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have := s8p_ibp_y hf hψ θ x
    have e : ∀ H : V × V → ℝ, ∫ y, H (x, y) * s8p_gd x * s8p_gd y = s8p_gd x * ∫ y, H (x, y) * s8p_gd y := by
      intro H
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only; ring
    simp only
    rw [e (s8p_H2 f ψ θ), e (s8p_H4 f ψ θ), this]
  have h3 : ∫ p, s8p_H3 f ψ θ p * s8p_gd p.1 * s8p_gd p.2 ∂(volume.prod volume) =
      Real.sin θ * ∫ x, s8p_Pd f θ x (s8p_w ψ x) * s8p_gd x := by
    rw [integral_prod _ i3, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have := s8p_stein_y hf hψ θ x
    have e : ∫ y, s8p_H3 f ψ θ (x, y) * s8p_gd x * s8p_gd y = s8p_gd x * ∫ y, s8p_H3 f ψ θ (x, y) * s8p_gd y := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only; ring
    simp only
    rw [e, this]; ring
  rw [hL, integral_sub i1 i2, h1, h2, integral_sub i3 i4, h3]
  ring

end HRS.MS.Spec
