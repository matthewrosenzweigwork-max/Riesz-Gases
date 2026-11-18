import HRS.MS.SpecAux76

/-!
# S8L: Cauchy-Schwarz and invariance for the Gaussian interpolation (S8.7, Gaussian log-Sobolev)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_Pd_sq_le`: `‖P_θ Df‖² ≤ P_θ(‖Df‖²/f) P_θ f`; `s8p_inv`: `∫ P_θ G dγ = ∫ G dγ`
(derivative zero, by `s8p_KL` with `ψ = 1`); `s8p_inv_Fish`: the same for the Fisher integrand.
-/

noncomputable section

open MeasureTheory Real

namespace HRS.MS.Spec

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {f : V → ℝ} {M0 M1 : ℝ}

theorem s8p_cs_aux {a A B : ℝ} (ha : 0 ≤ a) (hA : 0 ≤ A) (hB : 0 < B)
    (h : ∀ l : ℝ, 0 < l → 2 * a ≤ l * A + B / l) : a ^ 2 ≤ A * B := by
  rcases ha.eq_or_lt with h0 | hpos
  · rw [← h0]; nlinarith
  rcases hA.eq_or_lt with hA0 | hApos
  · exfalso
    have := h (B / a) (by positivity)
    rw [← hA0] at this
    have e : B / (B / a) = a := by field_simp
    rw [e] at this
    nlinarith
  · have := h (a / A) (by positivity)
    have e : B / (a / A) = B * A / a := by field_simp
    rw [e] at this
    have e2 : a / A * A = a := by field_simp
    rw [e2] at this
    have : a ≤ B * A / a := by linarith
    rw [le_div_iff₀ hpos] at this
    nlinarith

/-- The integrand `‖Df‖²/f` of the Fisher information. -/
def s8p_Fish (f : V → ℝ) (x : V) : ℝ := ‖fderiv ℝ f x‖ ^ 2 / f x

theorem s8p_Fish_cont {δ : ℝ} (hδ0 : 0 < δ) (hf : S8pBdd f M0 M1) (hδ : ∀ x, δ ≤ f x) :
    Continuous (s8p_Fish f) := by
  unfold s8p_Fish
  exact ((hf.cont.continuous_fderiv one_ne_zero).norm.pow 2).div hf.cont'
    (fun x => (lt_of_lt_of_le hδ0 (hδ x)).ne')

theorem s8p_Fish_bd {δ : ℝ} (hδ0 : 0 < δ) (hf : S8pBdd f M0 M1) (hδ : ∀ x, δ ≤ f x) (x : V) :
    0 ≤ s8p_Fish f x ∧ s8p_Fish f x ≤ M1 ^ 2 / δ := by
  unfold s8p_Fish
  have hp := lt_of_lt_of_le hδ0 (hδ x)
  refine ⟨by positivity, ?_⟩
  rw [div_le_div_iff₀ hp hδ0]
  have := hf.bd1 x
  have h2 : ‖fderiv ℝ f x‖ ^ 2 ≤ M1 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
  nlinarith [hδ x, sq_nonneg M1]

theorem s8p_Fish_aff_integrable {δ : ℝ} (hδ0 : 0 < δ) (hf : S8pBdd f M0 M1) (hδ : ∀ x, δ ≤ f x)
    (c s : ℝ) (x : V) :
    Integrable (fun y => s8p_Fish f (c • x + s • y) * s8p_gd y) := by
  refine Integrable.mono' (s8p_gd_integrable.const_mul (M1 ^ 2 / δ))
    (((s8p_Fish_cont hδ0 hf hδ).comp (s8p_aff_continuous c s x)).mul s8p_gd_continuous).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [norm_mul, Real.norm_of_nonneg (s8p_gd_pos y).le, Real.norm_of_nonneg (s8p_Fish_bd hδ0 hf hδ _).1]
  exact mul_le_mul_of_nonneg_right (s8p_Fish_bd hδ0 hf hδ _).2 (s8p_gd_pos y).le

/-- Cauchy-Schwarz: `‖P_θ Df‖² ≤ P_θ(‖Df‖²/f) · P_θ f`. -/
theorem s8p_Pd_sq_le {δ : ℝ} (hδ0 : 0 < δ) (hf : S8pBdd f M0 M1) (hδ : ∀ x, δ ≤ f x) (θ : ℝ) (x : V) :
    ‖s8p_Pd f θ x‖ ^ 2 ≤
      (∫ y, s8p_Fish f (Real.cos θ • x + Real.sin θ • y) * s8p_gd y) * s8p_Pt f θ x := by
  set A := ∫ y, s8p_Fish f (Real.cos θ • x + Real.sin θ • y) * s8p_gd y with hA
  have hA0 : 0 ≤ A := integral_nonneg fun y => mul_nonneg (s8p_Fish_bd hδ0 hf hδ _).1 (s8p_gd_pos y).le
  have hB : 0 < s8p_Pt f θ x := lt_of_lt_of_le hδ0 (s8p_Pt_ge hf hδ θ x)
  refine s8p_cs_aux (norm_nonneg _) hA0 hB (fun l hl => ?_)
  have h1 : ‖s8p_Pd f θ x‖ ≤ ∫ y, ‖s8p_gd y • fderiv ℝ f (Real.cos θ • x + Real.sin θ • y)‖ :=
    norm_integral_le_integral_norm _
  have hint2 : Integrable (fun y => (l * (s8p_Fish f (Real.cos θ • x + Real.sin θ • y) * s8p_gd y) +
      (1 / l) * (f (Real.cos θ • x + Real.sin θ • y) * s8p_gd y)) / 2) :=
    (((s8p_Fish_aff_integrable hδ0 hf hδ _ _ x).const_mul l).add
      ((s8p_f_aff_integrable hf _ _ x).const_mul (1 / l))).div_const 2
  have h2 : ∫ y, ‖s8p_gd y • fderiv ℝ f (Real.cos θ • x + Real.sin θ • y)‖ ≤
      ∫ y, (l * (s8p_Fish f (Real.cos θ • x + Real.sin θ • y) * s8p_gd y) +
        (1 / l) * (f (Real.cos θ • x + Real.sin θ • y) * s8p_gd y)) / 2 := by
    refine integral_mono (s8p_Df_aff_integrable hf _ _ x).norm hint2 (fun y => ?_)
    simp only
    rw [norm_smul, Real.norm_of_nonneg (s8p_gd_pos y).le]
    have hp := lt_of_lt_of_le hδ0 (hδ (Real.cos θ • x + Real.sin θ • y))
    set a := ‖fderiv ℝ f (Real.cos θ • x + Real.sin θ • y)‖
    set F := f (Real.cos θ • x + Real.sin θ • y)
    have key : a ≤ (l * (a ^ 2 / F) + (1 / l) * F) / 2 := by
      have : 0 ≤ (l * a - F) ^ 2 / (l * F) := by positivity
      have e : (l * (a ^ 2 / F) + (1 / l) * F) / 2 - a = (l * a - F) ^ 2 / (2 * (l * F)) := by
        field_simp; ring
      have : 0 ≤ (l * a - F) ^ 2 / (2 * (l * F)) := by positivity
      linarith
    have hg := (s8p_gd_pos y).le
    have := mul_le_mul_of_nonneg_left key hg
    simp only [s8p_Fish]
    nlinarith [this]
  have h3 : ∫ y, (l * (s8p_Fish f (Real.cos θ • x + Real.sin θ • y) * s8p_gd y) +
      (1 / l) * (f (Real.cos θ • x + Real.sin θ • y) * s8p_gd y)) / 2 = (l * A + s8p_Pt f θ x / l) / 2 := by
    rw [integral_div, integral_add ((s8p_Fish_aff_integrable hδ0 hf hδ _ _ x).const_mul l)
      ((s8p_f_aff_integrable hf _ _ x).const_mul (1 / l)), integral_const_mul, integral_const_mul]
    simp only [hA, s8p_Pt]
    ring
  have : 2 * ‖s8p_Pd f θ x‖ ≤ l * A + s8p_Pt f θ x / l := by linarith
  exact this


/-- Invariance of the Gaussian measure under `P_θ`. -/
theorem s8p_inv {G : V → ℝ} {N0 N1 : ℝ} (hG : S8pBdd G N0 N1) (hδ : ∀ x, 1 ≤ G x) (θ : ℝ) :
    ∫ x, s8p_Pt G θ x * s8p_gd x = ∫ x, G x * s8p_gd x := by
  have hΦ : S8pPhi (fun t : ℝ => t) (fun _ => (1 : ℝ)) 1 N0 (N0 + 1) :=
    { pos := one_pos
      deriv'c := continuousOn_const
      deriv := fun t _ => hasDerivAt_id t
      bd := fun t h1 h2 => ⟨by rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ t)]; linarith, by simp; exact hG.M0_nonneg⟩ }
  have hd : ∀ θ, HasDerivAt (fun θ => ∫ x, s8p_Pt G θ x * s8p_gd x) 0 θ := fun θ => by
    have h := s8p_Lam_hasDerivAt hG hδ hΦ θ
    have hψ : S8pBdd (fun _ : V => (1 : ℝ)) 1 0 :=
      ⟨contDiff_const, fun x => by simp, fun x => by simp⟩
    have hk := s8p_KL hG hψ θ
    have e : ∀ x, s8p_Pd G θ x (s8p_w (fun _ : V => (1 : ℝ)) x) = 0 := fun x => by
      simp [s8p_w]
    simp only [e, zero_mul, integral_zero, mul_zero, neg_zero, one_mul] at hk h
    simpa [hk] using h
  have hconst := is_const_of_deriv_eq_zero (f := fun θ => ∫ x, s8p_Pt G θ x * s8p_gd x)
    (fun θ => (hd θ).differentiableAt) (fun θ => (hd θ).deriv) θ 0
  rw [hconst]
  simp [s8p_Pt_zero]


/-- `∫ P_θ(Fish) dγ = ∫ Fish dγ`. -/
theorem s8p_inv_Fish {δ N0 N1 : ℝ} (hδ0 : 0 < δ) (hf : S8pBdd f M0 M1) (hδ : ∀ x, δ ≤ f x)
    (hF : S8pBdd (fun x => s8p_Fish f x + 1) N0 N1) (θ : ℝ) :
    ∫ x, (∫ y, s8p_Fish f (Real.cos θ • x + Real.sin θ • y) * s8p_gd y) * s8p_gd x =
      ∫ x, s8p_Fish f x * s8p_gd x := by
  have h := s8p_inv hF (fun x => by have := (s8p_Fish_bd hδ0 hf hδ x).1; linarith) θ
  have e1 : ∀ x, s8p_Pt (fun x => s8p_Fish f x + 1) θ x =
      (∫ y, s8p_Fish f (Real.cos θ • x + Real.sin θ • y) * s8p_gd y) + 1 := fun x => by
    unfold s8p_Pt
    simp only [add_mul, one_mul]
    rw [integral_add (s8p_Fish_aff_integrable hδ0 hf hδ _ _ x) s8p_gd_integrable, s8p_gd_integral]
  have hI1 : Integrable (fun x => s8p_Pt (fun x => s8p_Fish f x + 1) θ x * s8p_gd x) := by
    refine Integrable.mono' (s8p_gd_integrable.const_mul N0)
      ((s8p_Pt_continuous hF θ).mul s8p_gd_continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_of_nonneg (s8p_gd_pos x).le, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (s8p_Pt_abs_le hF θ x) (s8p_gd_pos x).le
  have hI2 : Integrable (fun x => s8p_Fish f x * s8p_gd x) := by
    refine Integrable.mono' (s8p_gd_integrable.const_mul (M1 ^ 2 / δ))
      ((s8p_Fish_cont hδ0 hf hδ).mul s8p_gd_continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_of_nonneg (s8p_gd_pos x).le, Real.norm_of_nonneg (s8p_Fish_bd hδ0 hf hδ x).1]
    exact mul_le_mul_of_nonneg_right (s8p_Fish_bd hδ0 hf hδ x).2 (s8p_gd_pos x).le
  have hlhs : ∫ x, s8p_Pt (fun x => s8p_Fish f x + 1) θ x * s8p_gd x =
      (∫ x, (∫ y, s8p_Fish f (Real.cos θ • x + Real.sin θ • y) * s8p_gd y) * s8p_gd x) + 1 := by
    have : ∀ x, s8p_Pt (fun x => s8p_Fish f x + 1) θ x * s8p_gd x =
        s8p_Pt (fun x => s8p_Fish f x + 1) θ x * s8p_gd x := fun x => rfl
    have e2 : ∀ x, (∫ y, s8p_Fish f (Real.cos θ • x + Real.sin θ • y) * s8p_gd y) * s8p_gd x =
        s8p_Pt (fun x => s8p_Fish f x + 1) θ x * s8p_gd x - s8p_gd x := fun x => by
      rw [e1 x]; ring
    simp_rw [e2]
    rw [integral_sub hI1 s8p_gd_integrable, s8p_gd_integral]; ring
  have hrhs : ∫ x, (s8p_Fish f x + 1) * s8p_gd x = (∫ x, s8p_Fish f x * s8p_gd x) + 1 := by
    simp_rw [add_mul, one_mul]
    rw [integral_add hI2 s8p_gd_integrable, s8p_gd_integral]
  rw [hlhs, hrhs] at h
  linarith

end HRS.MS.Spec
