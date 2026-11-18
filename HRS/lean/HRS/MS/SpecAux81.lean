import HRS.MS.SpecAux80
import HRS.MS.SpecAux70

/-!
# S8L: log-Sobolev inequality for a measure with density comparable to the Gaussian (S8.7, block L)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_lsi_of_comparable`: if `ρ` is a probability density (continuous or merely
measurable) with `c₁ gd ≤ ρ ≤ c₂ gd`, then `s8p_LSI (volume.withDensity ρ) (2 c₂ / c₁)`.  (Variational form of the entropy,
`Ent_μ(F) ≤ ∫ (F log (F/m) - F + m) dμ`, comparison of densities, `s8p_gauss_lsi`.)
-/

noncomputable section

open MeasureTheory Real Filter Topology

namespace HRS.MS.Spec

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem s8p_J_nonneg {t m : ℝ} (ht : 0 ≤ t) (hm : 0 < m) :
    0 ≤ t * Real.log t - t * Real.log m - t + m := by
  rcases ht.eq_or_lt with h | h
  · rw [← h]; simp; exact hm.le
  · have := Real.one_sub_inv_le_log_of_pos (div_pos h hm)
    rw [Real.log_div h.ne' hm.ne', inv_div] at this
    have h2 := mul_le_mul_of_nonneg_left this h.le
    have e : t * (1 - m / t) = t - m := by field_simp
    nlinarith

/-- Transfer of the log-Sobolev inequality to a measure with density comparable to the Gaussian. -/
theorem s8p_lsi_of_comparable {ρ : V → ℝ} (hρm : Measurable ρ) {c1 c2 : ℝ} (hc1 : 0 < c1)
    (hlo : ∀ x, c1 * s8p_gd x ≤ ρ x) (hhi : ∀ x, ρ x ≤ c2 * s8p_gd x) (hone : ∫ x, ρ x = 1) :
    s8p_LSI (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) (2 * c2 / c1) := by
  set μ : Measure V := volume.withDensity (fun x => ENNReal.ofReal (ρ x)) with hμ
  have hρ0 : ∀ x, 0 < ρ x := fun x => lt_of_lt_of_le (mul_pos hc1 (s8p_gd_pos x)) (hlo x)
  have hc2 : 0 < c2 := by
    have := (hlo 0).trans (hhi 0)
    have hg := s8p_gd_pos (0 : V)
    by_contra hneg
    push_neg at hneg
    nlinarith
  have tr : ∀ h : V → ℝ, ∫ x, h x ∂μ = ∫ x, ρ x * h x := fun h => by
    rw [hμ, integral_withDensity_eq_integral_toReal_smul (hρm.ennreal_ofReal)
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp [ENNReal.toReal_ofReal (hρ0 x).le]
  have trI : ∀ h : V → ℝ, Integrable h μ ↔ Integrable (fun x => ρ x * h x) := fun h => by
    rw [hμ, integrable_withDensity_iff_integrable_smul' (hρm.ennreal_ofReal)
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
    refine integrable_congr (ae_of_all _ fun x => ?_)
    simp [ENNReal.toReal_ofReal (hρ0 x).le]
  have hρint : Integrable ρ := by
    refine Integrable.mono' (s8p_gd_integrable.const_mul c2) hρm.aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (hρ0 x).le]; exact hhi x
  have hprob : IsProbabilityMeasure μ := ⟨by
    rw [hμ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hρint (ae_of_all _ fun x => (hρ0 x).le), hone]
    simp⟩
  intro u hu hmem hD
  have hu2 : Integrable (fun x => u x ^ 2) μ :=
    (memLp_two_iff_integrable_sq hu.continuous.aestronglyMeasurable).1 hmem
  have hu2' := (trI _).1 hu2
  have hD' := (trI _).1 hD
  have hg_u : Integrable (fun x => u x ^ 2 * s8p_gd x) := by
    refine Integrable.mono' (hu2'.const_mul (1 / c1))
      ((hu.continuous.pow 2).mul s8p_gd_continuous).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [norm_mul, Real.norm_of_nonneg (s8p_gd_pos x).le, Real.norm_of_nonneg (sq_nonneg _)]
    have := mul_le_mul_of_nonneg_left (hlo x) (sq_nonneg (u x))
    have h1 : u x ^ 2 * s8p_gd x ≤ 1 / c1 * (ρ x * u x ^ 2) := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc1]; nlinarith
    exact h1
  have hg_D : Integrable (fun x => ‖fderiv ℝ u x‖ ^ 2 * s8p_gd x) := by
    refine Integrable.mono' (hD'.const_mul (1 / c1))
      (((hu.continuous_fderiv (by norm_num)).norm.pow 2).mul s8p_gd_continuous).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [norm_mul, Real.norm_of_nonneg (s8p_gd_pos x).le, Real.norm_of_nonneg (sq_nonneg _)]
    have := mul_le_mul_of_nonneg_left (hlo x) (sq_nonneg ‖fderiv ℝ u x‖)
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc1]; nlinarith
  obtain ⟨hFint, hlsi⟩ := s8p_gauss_lsi hu hg_u hg_D
  set F : V → ℝ := fun x => u x ^ 2 * Real.log (u x ^ 2) with hF
  have hFρ : Integrable (fun x => ρ x * F x) := by
    refine Integrable.mono' (hFint.norm.const_mul c2) (hρm.mul
      (Real.continuous_mul_log.comp (hu.continuous.pow 2)).measurable).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [norm_mul, Real.norm_of_nonneg (hρ0 x).le]
    have : ρ x * ‖F x‖ ≤ c2 * s8p_gd x * ‖F x‖ := mul_le_mul_of_nonneg_right (hhi x) (norm_nonneg _)
    simp only [norm_mul, Real.norm_of_nonneg (s8p_gd_pos x).le, hF] at this ⊢
    nlinarith
  have hFμ : Integrable F μ := (trI F).2 hFρ
  refine ⟨hFμ, ?_⟩
  rw [tr F, tr (fun x => u x ^ 2), tr (fun x => ‖fderiv ℝ u x‖ ^ 2)]
  set m := ∫ x, u x ^ 2 * s8p_gd x with hm
  set a := ∫ x, ρ x * u x ^ 2 with ha
  set Ed := ∫ x, ‖fderiv ℝ u x‖ ^ 2 * s8p_gd x with hEd
  have hm0 : 0 ≤ m := integral_nonneg fun x => mul_nonneg (sq_nonneg _) (s8p_gd_pos x).le
  have ha0 : 0 ≤ a := integral_nonneg fun x => mul_nonneg (hρ0 x).le (sq_nonneg _)
  have hEd0 : 0 ≤ ∫ x, ρ x * ‖fderiv ℝ u x‖ ^ 2 := integral_nonneg fun x => mul_nonneg (hρ0 x).le (sq_nonneg _)
  have hEdle : Ed ≤ (1 / c1) * ∫ x, ρ x * ‖fderiv ℝ u x‖ ^ 2 := by
    rw [← integral_const_mul]
    refine integral_mono hg_D (hD'.const_mul _) (fun x => ?_)
    have := mul_le_mul_of_nonneg_left (hlo x) (sq_nonneg ‖fderiv ℝ u x‖)
    simp only
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc1]; nlinarith
  rcases hm0.eq_or_lt with hmz | hmpos
  · -- u vanishes identically
    have hzero : ∀ x, u x = 0 := by
      have h1 : (fun x => u x ^ 2 * s8p_gd x) =ᵐ[volume] 0 := by
        refine (integral_eq_zero_iff_of_nonneg (fun x => mul_nonneg (sq_nonneg _) (s8p_gd_pos x).le) hg_u).1 hmz.symm
      have h2 : (fun x => u x) =ᵐ[volume] fun _ => 0 := by
        filter_upwards [h1] with x hx
        have := s8p_gd_pos x
        simp only [Pi.zero_apply] at hx
        have : u x ^ 2 = 0 := by
          rcases mul_eq_zero.1 hx with h | h
          · exact h
          · exact absurd h this.ne'
        exact pow_eq_zero_iff (by norm_num) |>.1 this
      exact fun x => congrFun (hu.continuous.ae_eq_iff_eq volume continuous_const |>.1 h2) x
    have hu0 : u = fun _ => 0 := funext hzero
    subst hu0
    simp [ha, hF]
  · -- main case
    have hlogm := Real.log m
    set J : V → ℝ := fun x => F x - Real.log m * u x ^ 2 - u x ^ 2 + m with hJ
    have hJ0 : ∀ x, 0 ≤ J x := fun x => by
      have := s8p_J_nonneg (sq_nonneg (u x)) hmpos
      simp only [hJ, hF]; linarith
    have hgJ : Integrable (fun x => s8p_gd x * J x) := by
      have e : ∀ x, s8p_gd x * J x = (F x * s8p_gd x) - Real.log m * (u x ^ 2 * s8p_gd x) -
          (u x ^ 2 * s8p_gd x) + m * s8p_gd x := fun x => by simp only [hJ]; ring
      simp_rw [e]
      exact (((hFint.sub (hg_u.const_mul _)).sub hg_u).add (s8p_gd_integrable.const_mul m))
    have hρJ : Integrable (fun x => ρ x * J x) := by
      refine Integrable.mono' (hgJ.const_mul c2) (hρm.mul
        ((Real.continuous_mul_log.comp (hu.continuous.pow 2)).sub ((continuous_const.mul (hu.continuous.pow 2)))
          |>.sub (hu.continuous.pow 2) |>.add continuous_const).measurable).aestronglyMeasurable
        (ae_of_all _ fun x => ?_)
      rw [norm_mul, Real.norm_of_nonneg (hρ0 x).le, Real.norm_of_nonneg (hJ0 x)]
      have := mul_le_mul_of_nonneg_right (hhi x) (hJ0 x)
      nlinarith
    -- integral of gd * J
    have hgJint : ∫ x, s8p_gd x * J x = (∫ x, (F x * s8p_gd x)) - m * Real.log m := by
      have e : ∀ x, s8p_gd x * J x = (F x * s8p_gd x) - Real.log m * (u x ^ 2 * s8p_gd x) -
          (u x ^ 2 * s8p_gd x) + m * s8p_gd x := fun x => by simp only [hJ]; ring
      simp_rw [e]
      have i1 : Integrable (fun x => F x * s8p_gd x - Real.log m * (u x ^ 2 * s8p_gd x)) :=
        hFint.sub (hg_u.const_mul _)
      have i2 : Integrable (fun x => F x * s8p_gd x - Real.log m * (u x ^ 2 * s8p_gd x) -
          u x ^ 2 * s8p_gd x) := i1.sub hg_u
      have i3 : Integrable (fun x : V => m * s8p_gd x) := s8p_gd_integrable.const_mul m
      rw [integral_add i2 i3, integral_sub i1 hg_u, integral_sub hFint (hg_u.const_mul _),
        integral_const_mul, integral_const_mul, s8p_gd_integral]
      ring
    have hρJint : ∫ x, ρ x * J x = (∫ x, ρ x * F x) - Real.log m * a - a + m := by
      have e : ∀ x, ρ x * J x = (ρ x * F x) - Real.log m * (ρ x * u x ^ 2) - (ρ x * u x ^ 2) + m * ρ x :=
        fun x => by simp only [hJ]; ring
      simp_rw [e]
      have i1 : Integrable (fun x => ρ x * F x - Real.log m * (ρ x * u x ^ 2)) :=
        hFρ.sub (hu2'.const_mul _)
      have i2 : Integrable (fun x => ρ x * F x - Real.log m * (ρ x * u x ^ 2) - ρ x * u x ^ 2) :=
        i1.sub hu2'
      have i3 : Integrable (fun x : V => m * ρ x) := hρint.const_mul m
      rw [integral_add i2 i3, integral_sub i1 hu2', integral_sub hFρ (hu2'.const_mul _),
        integral_const_mul, integral_const_mul, hone]
      ring
    have hle1 : ∫ x, ρ x * J x ≤ c2 * ∫ x, s8p_gd x * J x := by
      rw [← integral_const_mul]
      refine integral_mono hρJ (hgJ.const_mul c2) (fun x => ?_)
      have := mul_le_mul_of_nonneg_right (hhi x) (hJ0 x)
      nlinarith
    have hent := s8p_J_nonneg ha0 hmpos
    have hlsi' : (∫ x, (F x * s8p_gd x)) - m * Real.log m ≤ 2 * Ed := hlsi
    have hc2' : 0 ≤ c2 := hc2.le
    have h5 : c2 * (2 * Ed) ≤ 2 * c2 / c1 * ∫ x, ρ x * ‖fderiv ℝ u x‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_left hEdle (by positivity : 0 ≤ 2 * c2)
      have e : 2 * c2 / c1 = 2 * c2 * (1 / c1) := by ring
      rw [e]; nlinarith
    have h6 := mul_le_mul_of_nonneg_left hlsi' hc2'
    nlinarith [hρJint, hgJint, hle1, hent, h6, h5]

end HRS.MS.Spec
