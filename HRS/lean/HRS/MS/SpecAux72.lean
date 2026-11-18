import HRS.MS.SpecAux71

/-!
# S8L: the Mehler-type operator `P_θ f(x) = ∫ f(x cos θ + y sin θ) dγ(y)` and its derivatives (S8.7, Gaussian log-Sobolev)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  For `f` of class `C¹` with `f` and `Df` bounded (`S8pBdd`): `s8p_Pt f θ x` is
`P_θ f(x)`, `s8p_Pd f θ x = ∫ Df(x cos θ + y sin θ) dγ(y)`, `s8p_Pth f θ x = ∫ Df(x cos θ + y sin θ)(-x sin θ + y cos θ) dγ(y)`.
Proved: `D (P_θ f) = cos θ • s8p_Pd f θ` (`s8p_Pt_hasFDerivAt`), `∂_θ P_θ f = s8p_Pth` (`s8p_Pt_hasDerivAt_theta`), the
bounds and the endpoint values.
-/

noncomputable section

open MeasureTheory Real

namespace HRS.MS.Spec

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The class of `C¹` functions with `|f| ≤ M0` and `‖Df‖ ≤ M1`. -/
structure S8pBdd (f : V → ℝ) (M0 M1 : ℝ) : Prop where
  cont : ContDiff ℝ 1 f
  bd0 : ∀ x, |f x| ≤ M0
  bd1 : ∀ x, ‖fderiv ℝ f x‖ ≤ M1

/-- `P_θ f (x) = ∫ f (x cos θ + y sin θ) dγ(y)`. -/
def s8p_Pt (f : V → ℝ) (θ : ℝ) (x : V) : ℝ := ∫ y, f (Real.cos θ • x + Real.sin θ • y) * s8p_gd y

/-- `P_θ (Df)(x)` as a continuous linear functional. -/
def s8p_Pd (f : V → ℝ) (θ : ℝ) (x : V) : V →L[ℝ] ℝ :=
  ∫ y, s8p_gd y • fderiv ℝ f (Real.cos θ • x + Real.sin θ • y)

/-- `∂_θ P_θ f (x)`. -/
def s8p_Pth (f : V → ℝ) (θ : ℝ) (x : V) : ℝ :=
  ∫ y, fderiv ℝ f (Real.cos θ • x + Real.sin θ • y) (-Real.sin θ • x + Real.cos θ • y) * s8p_gd y

variable {f : V → ℝ} {M0 M1 : ℝ}

theorem S8pBdd.cont' (hf : S8pBdd f M0 M1) : Continuous f := hf.cont.continuous

theorem S8pBdd.M0_nonneg (hf : S8pBdd f M0 M1) : 0 ≤ M0 := (abs_nonneg _).trans (hf.bd0 0)

theorem S8pBdd.M1_nonneg (hf : S8pBdd f M0 M1) : 0 ≤ M1 := (norm_nonneg _).trans (hf.bd1 0)

theorem s8p_aff_continuous (c s : ℝ) (x : V) : Continuous fun y : V => c • x + s • y := by fun_prop

theorem s8p_f_aff_integrable (hf : S8pBdd f M0 M1) (c s : ℝ) (x : V) :
    Integrable (fun y => f (c • x + s • y) * s8p_gd y) := by
  refine Integrable.mono' (s8p_gd_integrable.const_mul M0) ?_ (Filter.Eventually.of_forall fun y => ?_)
  · exact ((hf.cont'.comp (s8p_aff_continuous c s x)).mul s8p_gd_continuous).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (s8p_gd_pos y)]
    exact mul_le_mul_of_nonneg_right (hf.bd0 _) (s8p_gd_pos y).le

theorem s8p_Df_aff_integrable (hf : S8pBdd f M0 M1) (c s : ℝ) (x : V) :
    Integrable (fun y => s8p_gd y • fderiv ℝ f (c • x + s • y)) := by
  have hc : Continuous fun y : V => fderiv ℝ f (c • x + s • y) :=
    (hf.cont.continuous_fderiv one_ne_zero).comp (s8p_aff_continuous c s x)
  refine Integrable.mono' (s8p_gd_integrable.const_mul M1) ?_ (Filter.Eventually.of_forall fun y => ?_)
  · exact (s8p_gd_continuous.smul hc).aestronglyMeasurable
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (s8p_gd_pos y)]
    calc s8p_gd y * ‖fderiv ℝ f (c • x + s • y)‖ ≤ s8p_gd y * M1 :=
          mul_le_mul_of_nonneg_left (hf.bd1 _) (s8p_gd_pos y).le
      _ = M1 * s8p_gd y := mul_comm _ _

theorem s8p_Pt_hasFDerivAt (hf : S8pBdd f M0 M1) (θ : ℝ) (x : V) :
    HasFDerivAt (s8p_Pt f θ) (Real.cos θ • s8p_Pd f θ x) x := by
  set c := Real.cos θ with hc
  set s := Real.sin θ with hs
  have hc1 : |c| ≤ 1 := Real.abs_cos_le_one θ
  have hF' : ∀ y : V, ∀ x : V, HasFDerivAt (fun x : V => f (c • x + s • y) * s8p_gd y)
      (c • (s8p_gd y • fderiv ℝ f (c • x + s • y))) x := fun y x => by
    have h1 : HasFDerivAt (fun x : V => c • x + s • y) (c • ContinuousLinearMap.id ℝ V) x := by
      simpa using ((hasFDerivAt_id x).const_smul c).add_const (s • y)
    have h2 := (hf.cont.differentiable one_ne_zero (c • x + s • y)).hasFDerivAt.comp x h1
    have h3 := h2.mul_const (s8p_gd y)
    refine h3.congr_fderiv ?_
    ext v; simp [mul_comm, mul_left_comm]
  have hint := s8p_Df_aff_integrable hf c s x
  have := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := (volume : Measure V))
    (F := fun x y => f (c • x + s • y) * s8p_gd y)
    (F' := fun x y => c • (s8p_gd y • fderiv ℝ f (c • x + s • y)))
    (x₀ := x) (s := Set.univ) (bound := fun y => M1 * s8p_gd y) Filter.univ_mem
    (Filter.Eventually.of_forall fun x' => (s8p_f_aff_integrable hf c s x').aestronglyMeasurable)
    (s8p_f_aff_integrable hf c s x) (Integrable.smul c hint).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y x' _ => by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (s8p_gd_pos y)]
      calc |c| * (s8p_gd y * ‖fderiv ℝ f (c • x' + s • y)‖) ≤ 1 * (s8p_gd y * M1) :=
            mul_le_mul hc1 (mul_le_mul_of_nonneg_left (hf.bd1 _) (s8p_gd_pos y).le)
              (by have := s8p_gd_pos y; positivity) zero_le_one
        _ = M1 * s8p_gd y := by ring)
    (s8p_gd_integrable.const_mul M1)
    (Filter.Eventually.of_forall fun y x' _ => hF' y x')
  have e : s8p_Pt f θ = fun x => ∫ a, f (c • x + s • a) * s8p_gd a := rfl
  rw [e]
  convert this using 1
  show _ = ∫ y, c • (s8p_gd y • fderiv ℝ f (c • x + s • y))
  rw [integral_smul]; rfl


theorem s8p_Pd_continuous (hf : S8pBdd f M0 M1) (θ : ℝ) : Continuous (s8p_Pd f θ) := by
  unfold s8p_Pd
  refine continuous_of_dominated (bound := fun y => M1 * s8p_gd y) ?_ ?_ ?_ ?_
  · intro x
    exact (s8p_Df_aff_integrable hf (Real.cos θ) (Real.sin θ) x).aestronglyMeasurable
  · intro x
    refine Filter.Eventually.of_forall fun y => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (s8p_gd_pos y)]
    calc s8p_gd y * ‖fderiv ℝ f (Real.cos θ • x + Real.sin θ • y)‖ ≤ s8p_gd y * M1 :=
          mul_le_mul_of_nonneg_left (hf.bd1 _) (s8p_gd_pos y).le
      _ = M1 * s8p_gd y := mul_comm _ _
  · exact s8p_gd_integrable.const_mul M1
  · refine Filter.Eventually.of_forall fun y => ?_
    exact (continuous_const : Continuous fun _ : V => s8p_gd y).smul ((hf.cont.continuous_fderiv one_ne_zero).comp
        (by fun_prop : Continuous fun x : V => Real.cos θ • x + Real.sin θ • y))

theorem s8p_Pt_hasDerivAt_theta (hf : S8pBdd f M0 M1) (θ : ℝ) (x : V) :
    HasDerivAt (fun θ => s8p_Pt f θ x) (s8p_Pth f θ x) θ := by
  have hF' : ∀ y : V, ∀ θ' : ℝ, HasDerivAt (fun θ' : ℝ => f (Real.cos θ' • x + Real.sin θ' • y) * s8p_gd y)
      (fderiv ℝ f (Real.cos θ' • x + Real.sin θ' • y) (-Real.sin θ' • x + Real.cos θ' • y) * s8p_gd y) θ' :=
    fun y θ' => by
    have h1 : HasDerivAt (fun θ' : ℝ => Real.cos θ' • x + Real.sin θ' • y)
        (-Real.sin θ' • x + Real.cos θ' • y) θ' :=
      ((Real.hasDerivAt_cos θ').smul_const x).add ((Real.hasDerivAt_sin θ').smul_const y)
    have h2 := (hf.cont.differentiable one_ne_zero (Real.cos θ' • x + Real.sin θ' • y)).hasFDerivAt.comp_hasDerivAt θ' h1
    exact h2.mul_const (s8p_gd y)
  have hbd : ∀ θ' y, ‖fderiv ℝ f (Real.cos θ' • x + Real.sin θ' • y) (-Real.sin θ' • x + Real.cos θ' • y) *
      s8p_gd y‖ ≤ M1 * ((‖x‖ + ‖y‖) * s8p_gd y) := fun θ' y => by
    rw [norm_mul, Real.norm_of_nonneg (s8p_gd_pos y).le]
    have h1 : ‖fderiv ℝ f (Real.cos θ' • x + Real.sin θ' • y) (-Real.sin θ' • x + Real.cos θ' • y)‖ ≤
        M1 * (‖x‖ + ‖y‖) := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      have h2 : ‖-Real.sin θ' • x + Real.cos θ' • y‖ ≤ ‖x‖ + ‖y‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
        have := Real.abs_sin_le_one θ'; have := Real.abs_cos_le_one θ'
        nlinarith [norm_nonneg x, norm_nonneg y, abs_nonneg (Real.sin θ'), abs_nonneg (Real.cos θ')]
      exact mul_le_mul (hf.bd1 _) h2 (norm_nonneg _) hf.M1_nonneg
    calc _ ≤ M1 * (‖x‖ + ‖y‖) * s8p_gd y := mul_le_mul_of_nonneg_right h1 (s8p_gd_pos y).le
      _ = M1 * ((‖x‖ + ‖y‖) * s8p_gd y) := by ring
  have hint : Integrable (fun y : V => M1 * ((‖x‖ + ‖y‖) * s8p_gd y)) := by
    refine Integrable.const_mul ?_ M1
    have := (s8p_gd_integrable (V := V)).const_mul ‖x‖
    exact (this.add s8p_gd_mul_norm_integrable).congr (Filter.Eventually.of_forall fun y => by
      simp only [Pi.add_apply]; ring)
  have hmeasF' : ∀ θ', AEStronglyMeasurable (fun y : V => fderiv ℝ f (Real.cos θ' • x + Real.sin θ' • y)
      (-Real.sin θ' • x + Real.cos θ' • y) * s8p_gd y) volume := fun θ' => by
    refine Continuous.aestronglyMeasurable ?_
    have hc : Continuous fun y : V => fderiv ℝ f (Real.cos θ' • x + Real.sin θ' • y) :=
      (hf.cont.continuous_fderiv one_ne_zero).comp (s8p_aff_continuous _ _ x)
    exact (hc.clm_apply (by fun_prop)).mul s8p_gd_continuous
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure V))
    (F := fun θ y => f (Real.cos θ • x + Real.sin θ • y) * s8p_gd y)
    (F' := fun θ y => fderiv ℝ f (Real.cos θ • x + Real.sin θ • y) (-Real.sin θ • x + Real.cos θ • y) *
      s8p_gd y)
    (x₀ := θ) (s := Set.univ) (bound := fun y => M1 * ((‖x‖ + ‖y‖) * s8p_gd y)) Filter.univ_mem
    (Filter.Eventually.of_forall fun θ' => (s8p_f_aff_integrable hf _ _ x).aestronglyMeasurable)
    (s8p_f_aff_integrable hf _ _ x) (hmeasF' θ)
    (Filter.Eventually.of_forall fun y θ' _ => hbd θ' y) hint
    (Filter.Eventually.of_forall fun y θ' _ => hF' y θ')
  exact this.2


theorem s8p_Pt_abs_le (hf : S8pBdd f M0 M1) (θ : ℝ) (x : V) : |s8p_Pt f θ x| ≤ M0 := by
  unfold s8p_Pt
  refine (abs_integral_le_integral_abs).trans ?_
  have h1 : ∫ y, |f (Real.cos θ • x + Real.sin θ • y) * s8p_gd y| ≤ ∫ y, M0 * s8p_gd y :=
    integral_mono (s8p_f_aff_integrable hf _ _ x).abs (s8p_gd_integrable.const_mul M0) (fun y => by
      simp only
      rw [abs_mul, abs_of_pos (s8p_gd_pos y)]
      exact mul_le_mul_of_nonneg_right (hf.bd0 _) (s8p_gd_pos y).le)
  rw [integral_const_mul, s8p_gd_integral, mul_one] at h1
  exact h1

theorem s8p_Pt_ge {δ : ℝ} (hf : S8pBdd f M0 M1) (hδ : ∀ x, δ ≤ f x) (θ : ℝ) (x : V) :
    δ ≤ s8p_Pt f θ x := by
  unfold s8p_Pt
  have h1 : ∫ y, δ * s8p_gd y ≤ ∫ y, f (Real.cos θ • x + Real.sin θ • y) * s8p_gd y :=
    integral_mono (s8p_gd_integrable.const_mul δ) (s8p_f_aff_integrable hf _ _ x) (fun y =>
      mul_le_mul_of_nonneg_right (hδ _) (s8p_gd_pos y).le)
  rw [integral_const_mul, s8p_gd_integral, mul_one] at h1
  exact h1

theorem s8p_Pd_norm_le (hf : S8pBdd f M0 M1) (θ : ℝ) (x : V) : ‖s8p_Pd f θ x‖ ≤ M1 := by
  unfold s8p_Pd
  refine (norm_integral_le_integral_norm _).trans ?_
  have h1 : ∫ y, ‖s8p_gd y • fderiv ℝ f (Real.cos θ • x + Real.sin θ • y)‖ ≤ ∫ y, M1 * s8p_gd y :=
    integral_mono (s8p_Df_aff_integrable hf _ _ x).norm (s8p_gd_integrable.const_mul M1) (fun y => by
      simp only
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (s8p_gd_pos y)]
      calc s8p_gd y * ‖fderiv ℝ f (Real.cos θ • x + Real.sin θ • y)‖ ≤ s8p_gd y * M1 :=
            mul_le_mul_of_nonneg_left (hf.bd1 _) (s8p_gd_pos y).le
        _ = M1 * s8p_gd y := mul_comm _ _)
  rw [integral_const_mul, s8p_gd_integral, mul_one] at h1
  exact h1

/-- `m1 = ∫ ‖y‖ dγ`. -/
def s8p_m1 (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] : ℝ := ∫ y : V, ‖y‖ * s8p_gd y

theorem s8p_Pth_abs_le (hf : S8pBdd f M0 M1) (θ : ℝ) (x : V) :
    |s8p_Pth f θ x| ≤ M1 * (‖x‖ + s8p_m1 V) := by
  unfold s8p_Pth s8p_m1
  refine (abs_integral_le_integral_abs).trans ?_
  have hint : Integrable (fun y : V => M1 * ((‖x‖ + ‖y‖) * s8p_gd y)) := by
    refine Integrable.const_mul ?_ M1
    have := (s8p_gd_integrable (V := V)).const_mul ‖x‖
    exact (this.add s8p_gd_mul_norm_integrable).congr (Filter.Eventually.of_forall fun y => by
      simp only [Pi.add_apply]; ring)
  have hc : Continuous fun y : V => fderiv ℝ f (Real.cos θ • x + Real.sin θ • y) :=
    (hf.cont.continuous_fderiv one_ne_zero).comp (s8p_aff_continuous _ _ x)
  have hmeas : Continuous fun y : V => fderiv ℝ f (Real.cos θ • x + Real.sin θ • y)
      (-Real.sin θ • x + Real.cos θ • y) * s8p_gd y :=
    (hc.clm_apply (by fun_prop)).mul s8p_gd_continuous
  have hI : Integrable (fun y : V => fderiv ℝ f (Real.cos θ • x + Real.sin θ • y)
      (-Real.sin θ • x + Real.cos θ • y) * s8p_gd y) := by
    refine Integrable.mono' hint hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_mul, Real.norm_of_nonneg (s8p_gd_pos y).le]
    have h1 : ‖fderiv ℝ f (Real.cos θ • x + Real.sin θ • y) (-Real.sin θ • x + Real.cos θ • y)‖ ≤
        M1 * (‖x‖ + ‖y‖) := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      have h2 : ‖-Real.sin θ • x + Real.cos θ • y‖ ≤ ‖x‖ + ‖y‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
        have := Real.abs_sin_le_one θ; have := Real.abs_cos_le_one θ
        nlinarith [norm_nonneg x, norm_nonneg y, abs_nonneg (Real.sin θ), abs_nonneg (Real.cos θ)]
      exact mul_le_mul (hf.bd1 _) h2 (norm_nonneg _) hf.M1_nonneg
    calc _ ≤ M1 * (‖x‖ + ‖y‖) * s8p_gd y := mul_le_mul_of_nonneg_right h1 (s8p_gd_pos y).le
      _ = M1 * ((‖x‖ + ‖y‖) * s8p_gd y) := by ring
  have h1 : ∫ y, |fderiv ℝ f (Real.cos θ • x + Real.sin θ • y) (-Real.sin θ • x + Real.cos θ • y) *
      s8p_gd y| ≤ ∫ y : V, M1 * ((‖x‖ + ‖y‖) * s8p_gd y) := by
    refine integral_mono hI.abs hint (fun y => ?_)
    simp only
    rw [← Real.norm_eq_abs, norm_mul, Real.norm_of_nonneg (s8p_gd_pos y).le]
    have h1 : ‖fderiv ℝ f (Real.cos θ • x + Real.sin θ • y) (-Real.sin θ • x + Real.cos θ • y)‖ ≤
        M1 * (‖x‖ + ‖y‖) := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      have h2 : ‖-Real.sin θ • x + Real.cos θ • y‖ ≤ ‖x‖ + ‖y‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
        have := Real.abs_sin_le_one θ; have := Real.abs_cos_le_one θ
        nlinarith [norm_nonneg x, norm_nonneg y, abs_nonneg (Real.sin θ), abs_nonneg (Real.cos θ)]
      exact mul_le_mul (hf.bd1 _) h2 (norm_nonneg _) hf.M1_nonneg
    calc _ ≤ M1 * (‖x‖ + ‖y‖) * s8p_gd y := mul_le_mul_of_nonneg_right h1 (s8p_gd_pos y).le
      _ = M1 * ((‖x‖ + ‖y‖) * s8p_gd y) := by ring
  refine h1.trans (le_of_eq ?_)
  rw [integral_const_mul]
  congr 1
  have e : ∀ y : V, (‖x‖ + ‖y‖) * s8p_gd y = ‖x‖ * s8p_gd y + ‖y‖ * s8p_gd y := fun y => by ring
  simp_rw [e]
  rw [integral_add (s8p_gd_integrable.const_mul _) s8p_gd_mul_norm_integrable, integral_const_mul,
    s8p_gd_integral]
  ring

theorem s8p_Pt_zero (x : V) (f : V → ℝ) : s8p_Pt f 0 x = f x := by
  unfold s8p_Pt
  simp [integral_const_mul, s8p_gd_integral]

theorem s8p_Pt_pi_div_two (x : V) (f : V → ℝ) :
    s8p_Pt f (π / 2) x = ∫ y, f y * s8p_gd y := by
  unfold s8p_Pt
  simp

end HRS.MS.Spec
