import HRS.MS.SpecAux77

/-!
# S8L: the entropy bound along the Gaussian interpolation (S8.7, Gaussian log-Sobolev)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_gauss_ent`: for `f ≥ δ > 0` in the bounded `C¹` class whose Fisher
integrand `‖Df‖²/f` is again in that class,
`∫ f log f dγ - (∫ f dγ) log (∫ f dγ) ≤ (1/2) ∫ ‖Df‖²/f dγ`
(monotonicity of `Λ(θ) + (I/2) sin²θ`, `Λ(θ) = ∫ P_θ f log P_θ f dγ`).
-/

noncomputable section

open MeasureTheory Real

namespace HRS.MS.Spec

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable {f : V → ℝ} {M0 M1 : ℝ}

theorem s8p_PFish_cont {δ N0 N1 : ℝ} (hδ0 : 0 < δ) (hf : S8pBdd f M0 M1) (hδ : ∀ x, δ ≤ f x)
    (hF : S8pBdd (fun x => s8p_Fish f x + 1) N0 N1) (θ : ℝ) :
    Continuous fun x : V => ∫ y, s8p_Fish f (Real.cos θ • x + Real.sin θ • y) * s8p_gd y := by
  have e1 : ∀ x, (∫ y, s8p_Fish f (Real.cos θ • x + Real.sin θ • y) * s8p_gd y) =
      s8p_Pt (fun x => s8p_Fish f x + 1) θ x - 1 := fun x => by
    unfold s8p_Pt
    simp only [add_mul, one_mul]
    rw [integral_add (s8p_Fish_aff_integrable hδ0 hf hδ _ _ x) s8p_gd_integrable, s8p_gd_integral]; ring
  simp_rw [e1]
  exact (s8p_Pt_continuous hF θ).sub continuous_const

theorem s8p_PFish_bd {δ : ℝ} (hδ0 : 0 < δ) (hf : S8pBdd f M0 M1) (hδ : ∀ x, δ ≤ f x) (θ : ℝ) (x : V) :
    0 ≤ (∫ y, s8p_Fish f (Real.cos θ • x + Real.sin θ • y) * s8p_gd y) ∧
      (∫ y, s8p_Fish f (Real.cos θ • x + Real.sin θ • y) * s8p_gd y) ≤ M1 ^ 2 / δ := by
  constructor
  · exact integral_nonneg fun y => mul_nonneg (s8p_Fish_bd hδ0 hf hδ _).1 (s8p_gd_pos y).le
  · have h1 : ∫ y, s8p_Fish f (Real.cos θ • x + Real.sin θ • y) * s8p_gd y ≤ ∫ y, (M1 ^ 2 / δ) * s8p_gd y :=
      integral_mono (s8p_Fish_aff_integrable hδ0 hf hδ _ _ x) (s8p_gd_integrable.const_mul _) (fun y =>
        mul_le_mul_of_nonneg_right (s8p_Fish_bd hδ0 hf hδ _).2 (s8p_gd_pos y).le)
    rw [integral_const_mul, s8p_gd_integral, mul_one] at h1
    exact h1

/-- **Gaussian entropy bound (Bakry-Emery along the interpolation)**:
`∫ f log f dγ - m log m ≤ (1/2) ∫ ‖Df‖²/f dγ`, `m = ∫ f dγ`, for `f ≥ δ > 0` in the bounded `C¹` class whose
Fisher integrand is again in the bounded `C¹` class. -/
theorem s8p_gauss_ent {δ N0 N1 : ℝ} (hδ0 : 0 < δ) (hf : S8pBdd f M0 M1) (hδ : ∀ x, δ ≤ f x)
    (hF : S8pBdd (fun x => s8p_Fish f x + 1) N0 N1) :
    (∫ x, (f x * Real.log (f x)) * s8p_gd x) -
        (∫ x, f x * s8p_gd x) * Real.log (∫ x, f x * s8p_gd x) ≤
      (1 / 2) * ∫ x, s8p_Fish f x * s8p_gd x := by
  set I := ∫ x, s8p_Fish f x * s8p_gd x with hI
  set Λ : ℝ → ℝ := fun θ => ∫ x, (s8p_Pt f θ x * Real.log (s8p_Pt f θ x)) * s8p_gd x with hΛ
  set Mf : ℝ → ℝ := fun θ => Λ θ + (I / 2) * Real.sin θ ^ 2 with hMf
  have hI0 : 0 ≤ I := integral_nonneg fun x => mul_nonneg (s8p_Fish_bd hδ0 hf hδ x).1 (s8p_gd_pos x).le
  have hMd : ∀ θ, HasDerivAt Mf (-(Real.sin θ * Real.cos θ * ∫ x, ‖s8p_Pd f θ x‖ ^ 2 / s8p_Pt f θ x *
      s8p_gd x) + I * (Real.sin θ * Real.cos θ)) θ := fun θ => by
    have h1 := s8p_Lam_ent_deriv hδ0 hf hδ θ
    have h2 : HasDerivAt (fun θ => (I / 2) * Real.sin θ ^ 2) ((I / 2) * (2 * Real.sin θ * Real.cos θ)) θ := by
      have := ((Real.hasDerivAt_sin θ).pow 2).const_mul (I / 2)
      simpa using this
    have := h1.add h2
    convert this using 1
    ring
  have hmono : MonotoneOn Mf (Set.Icc 0 (π / 2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 (π / 2))
      (fun θ _ => (hMd θ).continuousAt.continuousWithinAt)
      (fun θ _ => (hMd θ).differentiableAt.differentiableWithinAt) (fun θ hθ => ?_)
    rw [interior_Icc] at hθ
    rw [(hMd θ).deriv]
    have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le (by linarith [hθ.2, Real.pi_pos])
    have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2.le⟩
    have hJ : ∫ x, ‖s8p_Pd f θ x‖ ^ 2 / s8p_Pt f θ x * s8p_gd x ≤ I := by
      have hP := fun x => lt_of_lt_of_le hδ0 (s8p_Pt_ge hf hδ θ x)
      have hc1 := s8p_PFish_cont hδ0 hf hδ hF θ
      calc _ ≤ ∫ x, (∫ y, s8p_Fish f (Real.cos θ • x + Real.sin θ • y) * s8p_gd y) * s8p_gd x := by
            refine integral_mono ?_ ?_ (fun x => ?_)
            · refine Integrable.mono' (s8p_gd_integrable.const_mul (M1 ^ 2 / δ)) ?_
                (Filter.Eventually.of_forall fun x => ?_)
              · exact (((s8p_Pd_continuous hf θ).norm.pow 2).div (s8p_Pt_continuous hf θ)
                  (fun x => (hP x).ne')).mul s8p_gd_continuous |>.aestronglyMeasurable
              · rw [norm_mul, Real.norm_of_nonneg (s8p_gd_pos x).le, Real.norm_of_nonneg (by
                  have := hP x; positivity)]
                refine mul_le_mul_of_nonneg_right ?_ (s8p_gd_pos x).le
                rw [div_le_div_iff₀ (hP x) hδ0]
                have h1 := s8p_Pd_norm_le hf θ x
                have h2 : ‖s8p_Pd f θ x‖ ^ 2 ≤ M1 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
                nlinarith [s8p_Pt_ge hf hδ θ x]
            · refine Integrable.mono' (s8p_gd_integrable.const_mul (M1 ^ 2 / δ))
                (hc1.mul s8p_gd_continuous).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
              rw [norm_mul, Real.norm_of_nonneg (s8p_gd_pos x).le, Real.norm_of_nonneg (s8p_PFish_bd hδ0 hf hδ θ x).1]
              exact mul_le_mul_of_nonneg_right (s8p_PFish_bd hδ0 hf hδ θ x).2 (s8p_gd_pos x).le
            · refine mul_le_mul_of_nonneg_right ?_ (s8p_gd_pos x).le
              rw [div_le_iff₀ (hP x)]
              exact s8p_Pd_sq_le hδ0 hf hδ θ x
        _ = I := s8p_inv_Fish hδ0 hf hδ hF θ
    have hsc := mul_nonneg hs hc
    nlinarith [mul_le_mul_of_nonneg_left hJ hsc]
  have h := hmono ⟨le_rfl, by linarith [Real.pi_pos]⟩ ⟨by linarith [Real.pi_pos], le_rfl⟩
    (by linarith [Real.pi_pos])
  have e0 : Mf 0 = ∫ x, (f x * Real.log (f x)) * s8p_gd x := by
    simp [hMf, hΛ, s8p_Pt_zero]
  have e1 : Mf (π / 2) = (∫ x, f x * s8p_gd x) * Real.log (∫ x, f x * s8p_gd x) + I / 2 := by
    simp only [hMf, hΛ, s8p_Pt_pi_div_two, Real.sin_pi_div_two]
    rw [integral_const_mul, s8p_gd_integral]; ring
  rw [e0, e1] at h
  linarith

end HRS.MS.Spec
