import HRS.MS.SuppU8Aux10

/-!
# Worker U8 aux 11: Fubini in `(y, ξ)`: the singular integral of a Schwartz function is `M |D|^α φ`
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace HRS.U8

variable {d : ℕ}

theorem u8_schwartz_rpow_int (ψ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) (α : ℝ)
    (hα : 0 ≤ α) : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => ‖ξ‖ ^ α * ‖ψ ξ‖) := by
  have hint := ψ.integrable.norm.add (SchwartzMap.integrable_pow_mul volume ψ ⌈α⌉₊)
  refine Integrable.mono' hint ?_ (Filter.Eventually.of_forall (fun ξ => ?_))
  · exact ((measurable_norm.pow_const α).mul ψ.continuous.norm.measurable).aestronglyMeasurable
  · have h0 : 0 ≤ ‖ξ‖ ^ α * ‖ψ ξ‖ := by positivity
    rw [Real.norm_of_nonneg h0]
    show ‖ξ‖ ^ α * ‖ψ ξ‖ ≤ ‖ψ ξ‖ + ‖ξ‖ ^ ⌈α⌉₊ * ‖ψ ξ‖
    by_cases h1 : ‖ξ‖ ≤ 1
    · have : ‖ξ‖ ^ α ≤ 1 := Real.rpow_le_one (norm_nonneg _) h1 hα
      have h2 : 0 ≤ ‖ξ‖ ^ ⌈α⌉₊ * ‖ψ ξ‖ := by positivity
      nlinarith [norm_nonneg (ψ ξ)]
    · push Not at h1
      have : ‖ξ‖ ^ α ≤ ‖ξ‖ ^ (⌈α⌉₊ : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1.le (Nat.le_ceil α)
      rw [Real.rpow_natCast] at this
      nlinarith [norm_nonneg (ψ ξ)]

theorem u8_symInt_measurable_prod (m : ℕ) (α : ℝ) :
    Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      u8_symInt d m α p.2 p.1) := by
  unfold u8_symInt u8_g
  fun_prop

theorem u8_Lam_phi (hd : 1 ≤ d) (m : ℕ) (hm : 1 ≤ m) (α : ℝ) (hα : 0 < α) (hαm : α < 2 * m)
    (M : ℝ) (hM : ∀ ξ, u8_sym d m α ξ = M * (2 * Real.pi * ‖ξ‖) ^ α)
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) (x : EuclideanSpace ℝ (Fin d)) :
    ∫ y, ‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L m y) (⇑φ) x =
      ∫ ξ, ((u8_sym d m α ξ : ℝ) : ℂ) * (u8_E ξ x * 𝓕 (⇑φ) ξ) := by
  obtain ⟨f, hf⟩ : ∃ f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℂ,
      f = fun y ξ => ((u8_symInt d m α ξ y : ℝ) : ℂ) * (u8_E ξ x * 𝓕 (⇑φ) ξ) := ⟨_, rfl⟩
  have h1 : ∀ y, ‖y‖ ^ (-((d : ℝ) + α)) • u8_fd (u8_L m y) (⇑φ) x = ∫ ξ, f y ξ := by
    intro y
    rw [u8_fd_phi, ← integral_smul]
    congr 1; funext ξ
    rw [hf, Complex.real_smul]
    simp only [u8_symInt]
    push_cast
    ring
  simp_rw [h1]
  have hmeas : AEStronglyMeasurable (Function.uncurry f)
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).prod volume) := by
    have : Measurable (Function.uncurry f) := by
      have e : Function.uncurry f = fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
          ((u8_symInt d m α p.2 p.1 : ℝ) : ℂ) * (u8_E p.2 x * 𝓕 (⇑φ) p.2) := by
        funext p; rw [hf]; rfl
      rw [e]
      have h2 : Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
          ((u8_symInt d m α p.2 p.1 : ℝ) : ℂ)) :=
        Complex.measurable_ofReal.comp (u8_symInt_measurable_prod m α)
      have h3 : Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
          u8_E p.2 x) := (u8_E_cont x).measurable.comp measurable_snd
      have h4 : Measurable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
          𝓕 (⇑φ) p.2) := (u8_fourier_continuous φ).measurable.comp measurable_snd
      exact h2.mul (h3.mul h4)
    exact this.aestronglyMeasurable
  have hint : Integrable (Function.uncurry f)
      ((volume : Measure (EuclideanSpace ℝ (Fin d))).prod volume) := by
    rw [integrable_prod_iff' hmeas]
    refine ⟨Filter.Eventually.of_forall (fun ξ => ?_), ?_⟩
    · have := ((u8_symInt_integrable hd m hm α hα hαm ξ).ofReal (𝕜 := ℂ)).mul_const
        (u8_E ξ x * 𝓕 (⇑φ) ξ)
      simpa [Function.uncurry, hf] using this
    · have hnorm : ∀ ξ, ∫ y, ‖Function.uncurry f (y, ξ)‖ =
          M * (2 * Real.pi) ^ α * (‖ξ‖ ^ α * ‖𝓕 (⇑φ) ξ‖) := by
        intro ξ
        have : ∀ y, ‖Function.uncurry f (y, ξ)‖ = u8_symInt d m α ξ y * ‖𝓕 (⇑φ) ξ‖ := by
          intro y
          simp only [Function.uncurry, hf, norm_mul, Complex.norm_real, u8_E_norm, one_mul]
          rw [Real.norm_of_nonneg (u8_symInt_nonneg m α ξ y)]
        simp_rw [this]
        rw [integral_mul_const]
        change u8_sym d m α ξ * ‖𝓕 (⇑φ) ξ‖ = _
        rw [hM ξ, Real.mul_rpow (by positivity) (norm_nonneg _)]
        ring
      simp_rw [hnorm]
      have := (u8_schwartz_rpow_int (𝓕 φ) α hα.le).const_mul (M * (2 * Real.pi) ^ α)
      have e := u8_fourier_coe φ
      rw [e] at this
      exact this
  rw [integral_integral_swap hint]
  congr 1; funext ξ
  rw [hf]
  simp only
  rw [integral_mul_const]
  congr 1
  exact integral_ofReal

end HRS.U8
