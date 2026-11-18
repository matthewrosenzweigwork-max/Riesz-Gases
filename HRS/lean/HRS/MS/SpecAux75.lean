import HRS.MS.SpecAux74

/-!
# S8L: differentiability of the interpolated functionals `Λ(θ) = ∫ Φ(P_θ f) dγ` (S8.7, Gaussian log-Sobolev)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_Lam_hasDerivAt`: `Λ'(θ) = ∫ Φ'(P_θ f) ∂_θP_θ f dγ` for `f ≥ δ > 0`
in the bounded `C¹` class (`S8pBdd`), `Φ` with bounded derivative on `[δ, M0]` (`S8pPhi`); `s8p_Pth_continuous`.
-/

noncomputable section

open MeasureTheory Real

namespace HRS.MS.Spec

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {f : V → ℝ} {M0 M1 : ℝ}

theorem s8p_Pth_continuous (hf : S8pBdd f M0 M1) (θ : ℝ) : Continuous (s8p_Pth f θ) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  unfold s8p_Pth
  have hint : Integrable (fun y : V => M1 * (((‖x₀‖ + 1) + ‖y‖) * s8p_gd y)) := by
    refine Integrable.const_mul ?_ M1
    have := (s8p_gd_integrable (V := V)).const_mul (‖x₀‖ + 1)
    exact (this.add s8p_gd_mul_norm_integrable).congr (Filter.Eventually.of_forall fun y => by
      simp only [Pi.add_apply]; ring)
  refine continuousAt_of_dominated (bound := fun y => M1 * (((‖x₀‖ + 1) + ‖y‖) * s8p_gd y)) ?_ ?_ hint ?_
  · refine Filter.Eventually.of_forall fun x => ?_
    have hc : Continuous fun y : V => fderiv ℝ f (Real.cos θ • x + Real.sin θ • y) :=
      (hf.cont.continuous_fderiv one_ne_zero).comp (s8p_aff_continuous _ _ x)
    exact ((hc.clm_apply (by fun_prop)).mul s8p_gd_continuous).aestronglyMeasurable
  · have hball : ∀ᶠ x in nhds x₀, ‖x - x₀‖ < 1 := by
      have := Metric.ball_mem_nhds x₀ one_pos
      filter_upwards [this] with x hx
      simpa [dist_eq_norm] using hx
    filter_upwards [hball] with x hx
    refine Filter.Eventually.of_forall fun y => ?_
    have hx' : ‖x‖ ≤ ‖x₀‖ + 1 := by
      have := norm_sub_norm_le x x₀
      linarith
    rw [norm_mul, Real.norm_of_nonneg (s8p_gd_pos y).le]
    have h1 : ‖fderiv ℝ f (Real.cos θ • x + Real.sin θ • y) (-Real.sin θ • x + Real.cos θ • y)‖ ≤
        M1 * ((‖x₀‖ + 1) + ‖y‖) := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      have h2 : ‖-Real.sin θ • x + Real.cos θ • y‖ ≤ (‖x₀‖ + 1) + ‖y‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
        have := Real.abs_sin_le_one θ; have := Real.abs_cos_le_one θ
        nlinarith [norm_nonneg x, norm_nonneg y, abs_nonneg (Real.sin θ), abs_nonneg (Real.cos θ)]
      exact mul_le_mul (hf.bd1 _) h2 (norm_nonneg _) hf.M1_nonneg
    calc _ ≤ M1 * ((‖x₀‖ + 1) + ‖y‖) * s8p_gd y := mul_le_mul_of_nonneg_right h1 (s8p_gd_pos y).le
      _ = M1 * (((‖x₀‖ + 1) + ‖y‖) * s8p_gd y) := by ring
  · refine Filter.Eventually.of_forall fun y => ?_
    have hc : Continuous fun x : V => fderiv ℝ f (Real.cos θ • x + Real.sin θ • y) :=
      (hf.cont.continuous_fderiv one_ne_zero).comp (by fun_prop)
    exact ((hc.clm_apply (by fun_prop)).mul continuous_const).continuousAt

/-- A function `Φ` with derivative `Φ'`, bounded together with `Φ'` on `[δ, M]`. -/
structure S8pPhi (Φ Φ' : ℝ → ℝ) (δ M BΦ : ℝ) : Prop where
  pos : 0 < δ
  deriv'c : ContinuousOn Φ' (Set.Ioi 0)
  deriv : ∀ t, 0 < t → HasDerivAt Φ (Φ' t) t
  bd : ∀ t, δ ≤ t → t ≤ M → |Φ t| ≤ BΦ ∧ |Φ' t| ≤ BΦ

theorem s8p_Pt_continuous (hf : S8pBdd f M0 M1) (θ : ℝ) : Continuous (s8p_Pt f θ) :=
  continuous_iff_continuousAt.2 fun x => (s8p_Pt_hasFDerivAt hf θ x).continuousAt

theorem s8p_Lam_hasDerivAt {Φ Φ' : ℝ → ℝ} {δ BΦ : ℝ} (hf : S8pBdd f M0 M1) (hδ : ∀ x, δ ≤ f x)
    (hΦ : S8pPhi Φ Φ' δ M0 BΦ) (θ : ℝ) :
    HasDerivAt (fun θ => ∫ x, Φ (s8p_Pt f θ x) * s8p_gd x)
      (∫ x, Φ' (s8p_Pt f θ x) * s8p_Pth f θ x * s8p_gd x) θ := by
  have hP : ∀ θ x, δ ≤ s8p_Pt f θ x ∧ s8p_Pt f θ x ≤ M0 := fun θ x =>
    ⟨s8p_Pt_ge hf hδ θ x, (le_abs_self _).trans (s8p_Pt_abs_le hf θ x)⟩
  have hpos : ∀ θ x, 0 < s8p_Pt f θ x := fun θ x => lt_of_lt_of_le hΦ.pos (hP θ x).1
  have hΦc : ∀ θ, Continuous fun x => Φ (s8p_Pt f θ x) := fun θ => by
    have hc : ContinuousOn Φ (Set.Ioi 0) := fun t ht => (hΦ.deriv t ht).continuousAt.continuousWithinAt
    exact hc.comp_continuous (s8p_Pt_continuous hf θ) (fun x => hpos θ x)
  have hm1 := s8p_m1 V
  set m1 := s8p_m1 V
  have hb : ∀ θ x, |Φ' (s8p_Pt f θ x) * s8p_Pth f θ x * s8p_gd x| ≤
      BΦ * (M1 * (‖x‖ * s8p_gd x + m1 * s8p_gd x)) := fun θ x => by
    rw [abs_mul, abs_mul, abs_of_pos (s8p_gd_pos x)]
    have h1 := (hΦ.bd _ (hP θ x).1 (hP θ x).2).2
    have h2 := s8p_Pth_abs_le hf θ x
    have hg := (s8p_gd_pos x).le
    have : |Φ' (s8p_Pt f θ x)| * |s8p_Pth f θ x| ≤ BΦ * (M1 * (‖x‖ + m1)) :=
      mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
    calc _ ≤ BΦ * (M1 * (‖x‖ + m1)) * s8p_gd x := mul_le_mul_of_nonneg_right this hg
      _ = _ := by ring
  have hint : Integrable (fun x : V => BΦ * (M1 * (‖x‖ * s8p_gd x + m1 * s8p_gd x))) :=
    ((s8p_gd_mul_norm_integrable.add (s8p_gd_integrable.const_mul m1)).const_mul M1).const_mul BΦ
  have hF' : ∀ x θ', HasDerivAt (fun θ' => Φ (s8p_Pt f θ' x) * s8p_gd x)
      (Φ' (s8p_Pt f θ' x) * s8p_Pth f θ' x * s8p_gd x) θ' := fun x θ' =>
    (((hΦ.deriv _ (hpos θ' x)).comp θ' (s8p_Pt_hasDerivAt_theta hf θ' x)).mul_const (s8p_gd x))
  have hmeasF' : AEStronglyMeasurable (fun x : V => Φ' (s8p_Pt f θ x) * s8p_Pth f θ x * s8p_gd x) volume := by
    have hc : ContinuousOn Φ' (Set.Ioi 0) := hΦ.deriv'c
    exact (((hc.comp_continuous (s8p_Pt_continuous hf θ) (fun x => hpos θ x)).mul
      (s8p_Pth_continuous hf θ)).mul s8p_gd_continuous).aestronglyMeasurable
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure V))
    (F := fun θ x => Φ (s8p_Pt f θ x) * s8p_gd x)
    (F' := fun θ x => Φ' (s8p_Pt f θ x) * s8p_Pth f θ x * s8p_gd x)
    (x₀ := θ) (s := Set.univ) (bound := fun x => BΦ * (M1 * (‖x‖ * s8p_gd x + m1 * s8p_gd x)))
    Filter.univ_mem
    (Filter.Eventually.of_forall fun θ' => ((hΦc θ').mul s8p_gd_continuous).aestronglyMeasurable)
    (by
      refine Integrable.mono' (s8p_gd_integrable.const_mul BΦ)
        ((hΦc θ).mul s8p_gd_continuous).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
      rw [norm_mul, Real.norm_of_nonneg (s8p_gd_pos x).le, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hΦ.bd _ (hP θ x).1 (hP θ x).2).1 (s8p_gd_pos x).le)
    hmeasF'
    (Filter.Eventually.of_forall fun x θ' _ => by rw [Real.norm_eq_abs]; exact hb θ' x) hint
    (Filter.Eventually.of_forall fun x θ' _ => hF' x θ')
  exact this.2

end HRS.MS.Spec
