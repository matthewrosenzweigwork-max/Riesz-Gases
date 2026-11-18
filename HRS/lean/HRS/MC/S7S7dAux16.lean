import HRS.MC.S7S7dAux15

/-!
# Packet `s7_S7d_uniform_limits`, helper 16: membership of the Stein derivatives in the class `s7d_Th`; Gaussian truncation
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7d

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux

variable {d : ℕ} {r : ℝ}

section ThInst

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem s7d_Th_D2 {f : E → ℝ} (hf : s7d_Cl f) (u u' : E) (hu : ‖u‖ ≤ 1) (hu' : ‖u'‖ ≤ 1) :
    s7d_Th (fun x => iteratedFDeriv ℝ 2 f x ![u, u']) := by
  refine ⟨?_, fun x => ?_, fun x y => s7d_D2_min hf x y u u' hu hu'⟩
  · exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ ![u, u']).continuous.comp
      (hf.1.continuous_iteratedFDeriv (m := 2) (by norm_num))
  · refine (s7d_D2_abs hf x u u').trans ?_
    calc ‖u‖ * ‖u'‖ ≤ 1 * 1 := mul_le_mul hu hu' (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

theorem s7d_Th_D3 {f : E → ℝ} (hf : s7d_Cl f) (u u' e : E) (hu : ‖u‖ ≤ 1) (hu' : ‖u'‖ ≤ 1)
    (he : ‖e‖ ≤ 1) : s7d_Th (fun x => iteratedFDeriv ℝ 3 f x ![u, u', e]) := by
  refine ⟨?_, fun x => ?_, fun x y => s7d_D3_min hf x y u u' e hu hu' he⟩
  · exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 3 => E) ℝ ![u, u', e]).continuous.comp
      (hf.1.continuous_iteratedFDeriv (m := 3) (by norm_num))
  · refine (s7d_D3_abs hf x u u' e).trans ?_
    calc ‖u‖ * ‖u'‖ * ‖e‖ ≤ 1 * 1 * 1 :=
          mul_le_mul (mul_le_mul hu hu' (norm_nonneg _) zero_le_one) he (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num

theorem s7d_Th_D1 {f : E → ℝ} (hf : s7d_Cl f) (u : E) (hu : ‖u‖ ≤ 1) :
    s7d_Th (fun x => fderiv ℝ f x u) := by
  have e : ∀ z, iteratedFDeriv ℝ 1 f z ![u] = fderiv ℝ f z u := fun z => by
    simp [iteratedFDeriv_one_apply]
  refine ⟨?_, fun x => ?_, fun x y => ?_⟩
  · exact ((hf.1.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  · have h1 := (iteratedFDeriv ℝ 1 f x).le_opNorm ![u]
    rw [e, Real.norm_eq_abs] at h1
    simp only [Fin.prod_univ_one, Matrix.cons_val_zero] at h1
    have h2 := hf.2 1 le_rfl (by norm_num) x
    calc _ ≤ _ := h1
      _ ≤ 1 * 1 := mul_le_mul h2 hu (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  · have h1 := (s7d_iter_lip hf (n := 1) (by norm_num)).dist_le_mul x y
    rw [dist_eq_norm, dist_eq_norm] at h1
    have h2 := (iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 f y).le_opNorm ![u]
    rw [ContinuousMultilinearMap.sub_apply, Real.norm_eq_abs] at h2
    simp only [Fin.prod_univ_one, Matrix.cons_val_zero] at h2
    rw [e, e] at h2
    refine le_min ?_ ?_
    · have hb : ∀ z, |fderiv ℝ f z u| ≤ 1 := by
        intro z
        have h1 := (iteratedFDeriv ℝ 1 f z).le_opNorm ![u]
        rw [e, Real.norm_eq_abs] at h1
        simp only [Fin.prod_univ_one, Matrix.cons_val_zero] at h1
        have h2 := hf.2 1 le_rfl (by norm_num) z
        calc _ ≤ _ := h1
          _ ≤ 1 * 1 := mul_le_mul h2 hu (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      calc _ ≤ |fderiv ℝ f x u| + |fderiv ℝ f y u| := abs_sub _ _
        _ ≤ 1 + 1 := add_le_add (hb x) (hb y)
        _ = 2 := by norm_num
    · calc _ ≤ _ := h2
        _ ≤ ‖x - y‖ * 1 := mul_le_mul (by simpa using h1) hu (norm_nonneg _) (norm_nonneg _)
        _ = ‖x - y‖ := mul_one _

end ThInst

section GSide

variable {Θ : NegSobolev d r → ℝ}

theorem s7d_Th_abs_int (G : Measure (NegSobolev d r)) [IsProbabilityMeasure G] (hΘ : s7d_Th Θ) :
    |∫ F, Θ F ∂G| ≤ 1 := by
  have := norm_integral_le_of_norm_le_const (μ := G) (f := Θ) (C := 1)
    (Eventually.of_forall fun F => by rw [Real.norm_eq_abs]; exact hΘ.2.1 F)
  simpa [Real.norm_eq_abs] using this

theorem s7d_G_trunc_err (G : Measure (NegSobolev d r)) [IsProbabilityMeasure G] (hΘ : s7d_Th Θ)
    (K : Finset (NonzeroLattice d)) :
    |∫ F, Θ (truncE K F) ∂G - ∫ F, Θ F ∂G| ≤ ∫ F, min 2 ‖F - truncE K F‖ ∂G := by
  have hmeas : Measurable fun F : NegSobolev d r => min 2 ‖F - truncE K F‖ :=
    (continuous_const.min
      (continuous_norm.comp (continuous_id.sub (s7d_truncE_continuous K)))).measurable
  have hmi : Integrable (fun F : NegSobolev d r => min 2 ‖F - truncE K F‖) G :=
    Integrable.of_bound hmeas.aestronglyMeasurable 2 (Eventually.of_forall fun F => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by norm_num) (norm_nonneg _))]
      exact min_le_left _ _)
  have hint : ∀ {Z : NegSobolev d r → ℝ}, Measurable Z → (∀ F, |Z F| ≤ 1) → Integrable Z G :=
    fun hZ hb => Integrable.of_bound hZ.aestronglyMeasurable 1
      (Eventually.of_forall fun F => by rw [Real.norm_eq_abs]; exact hb F)
  refine s7d_int_sub_le G (hint (hΘ.1.measurable.comp (s7d_truncE_continuous K).measurable)
    fun F => hΘ.2.1 _) (hint hΘ.1.measurable hΘ.2.1) hmi (fun F => ?_)
  refine (hΘ.2.2 _ _).trans ?_
  rw [norm_sub_rev]

end GSide

end HRS.MC.Sec7.S7d

end
