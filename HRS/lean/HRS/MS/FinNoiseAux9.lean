import HRS.MS.FinNoiseAux8
import HRS.Uniform.Comp28W1

/-!
# S8.6 `finite_noise`, packet P6a (S86): `IsHilbertItoIntegral` is linear in the integrand

`s86_hito_sub`: if `M₁ = ∫Φ₁ dW`, `M₂ = ∫Φ₂ dW` (Hilbert-Schmidt on every horizon), then `M₁ - M₂ = ∫(Φ₁ - Φ₂) dW`.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.FinNoise

open HRS HRS.Whole

theorem s86_enorm_sq_sub_le (a b : ℝ) : ‖a - b‖ₑ ^ 2 ≤ 2 * (‖a‖ₑ ^ 2 + ‖b‖ₑ ^ 2) := by
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [Real.norm_eq_abs, sq_abs]
  nlinarith [sq_nonneg (a + b)]

theorem s86_hito_sub {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    {κ : Type*} [Countable κ] (W : ℝ≥0 → Ω → κ → ℝ) (hW : IsCylindricalBrownian P ℱ W)
    {Φ₁ Φ₂ : ℝ → Ω → κ → H} (h₁ : ∀ T : ℝ, IsHSIntegrand P ℱ T Φ₁)
    (h₂ : ∀ T : ℝ, IsHSIntegrand P ℱ T Φ₂) {M₁ M₂ : ℝ → Ω → H}
    (hM₁ : IsHilbertItoIntegral P ℱ W Φ₁ M₁) (hM₂ : IsHilbertItoIntegral P ℱ W Φ₂ M₂) :
    IsHilbertItoIntegral P ℱ W (fun r w k => Φ₁ r w k - Φ₂ r w k) (fun τ w => M₁ τ w - M₂ τ w) := by
  refine { cont := fun w => (hM₁.cont w).sub (hM₂.cont w),
           adapted := fun τ => (hM₁.adapted τ).sub (hM₂.adapted τ),
           zero := fun τ hτ w => by simp [hM₁.zero τ hτ w, hM₂.zero τ hτ w],
           approx := ?_ }
  intro τ hτ x
  have hmeas : ∀ (s : Finset κ) (Φ : ℝ → Ω → κ → H) (M : ℝ → Ω → H),
      IsHilbertItoIntegral P ℱ W Φ M → Measurable fun w =>
        ‖itoIntegral P ℱ (fun t w (k : s) => W t w k)
          (fun r w (k : s) => inner ℝ (Φ r w k) x) τ w - inner ℝ (M τ w) x‖ₑ ^ 2 := by
    intro s Φ M hM
    have h1 : Measurable fun w => itoIntegral P ℱ (fun t w (k : s) => W t w k)
        (fun r w (k : s) => inner ℝ (Φ r w k) x) τ w :=
      (adapted_itoIntegral P ℱ _ _ τ).mono (ℱ.le τ) le_rfl
    have h2 : Measurable fun w => inner ℝ (M τ w) x :=
      (continuous_id.inner continuous_const).measurable.comp ((hM.adapted τ).mono (ℱ.le τ) le_rfl)
    exact ((h1.sub h2).enorm).pow_const 2
  have hae : ∀ s : Finset κ, ∀ᵐ w ∂P,
      itoIntegral P ℱ (fun t w (k : s) => W t w k)
        (fun r w (k : s) => inner ℝ (Φ₁ r w k - Φ₂ r w k) x) τ w =
      itoIntegral P ℱ (fun t w (k : s) => W t w k) (fun r w (k : s) => inner ℝ (Φ₁ r w k) x) τ w -
      itoIntegral P ℱ (fun t w (k : s) => W t w k) (fun r w (k : s) => inner ℝ (Φ₂ r w k) x) τ w := by
    intro s
    have := itoIntegral_sub (hW s) (hdsum_isProgressiveL2_inner P Φ₁ h₁ x s)
      (hdsum_isProgressiveL2_inner P Φ₂ h₂ x s)
    filter_upwards [this] with w hw
    have e : (fun r w (k : s) => inner ℝ (Φ₁ r w k - Φ₂ r w k) x) =
        fun r w (k : s) => inner ℝ (Φ₁ r w k) x - inner ℝ (Φ₂ r w k) x := by
      funext r w k; simp [inner_sub_left]
    rw [e]; exact hw τ
  have hbound : ∀ s : Finset κ,
      ∫⁻ w, ‖itoIntegral P ℱ (fun t w (k : s) => W t w k)
          (fun r w (k : s) => inner ℝ (Φ₁ r w k - Φ₂ r w k) x) τ w -
          inner ℝ (M₁ τ w - M₂ τ w) x‖ₑ ^ 2 ∂P ≤
      2 * (∫⁻ w, ‖itoIntegral P ℱ (fun t w (k : s) => W t w k)
          (fun r w (k : s) => inner ℝ (Φ₁ r w k) x) τ w - inner ℝ (M₁ τ w) x‖ₑ ^ 2 ∂P +
        ∫⁻ w, ‖itoIntegral P ℱ (fun t w (k : s) => W t w k)
          (fun r w (k : s) => inner ℝ (Φ₂ r w k) x) τ w - inner ℝ (M₂ τ w) x‖ₑ ^ 2 ∂P) := by
    intro s
    rw [← lintegral_add_left (hmeas s Φ₁ M₁ hM₁), ← lintegral_const_mul' _ _ (by simp)]
    refine lintegral_mono_ae ?_
    filter_upwards [hae s] with w hw
    rw [hw]
    have := s86_enorm_sq_sub_le
      (itoIntegral P ℱ (fun t w (k : s) => W t w k) (fun r w (k : s) => inner ℝ (Φ₁ r w k) x) τ w -
        inner ℝ (M₁ τ w) x)
      (itoIntegral P ℱ (fun t w (k : s) => W t w k) (fun r w (k : s) => inner ℝ (Φ₂ r w k) x) τ w -
        inner ℝ (M₂ τ w) x)
    refine le_trans (le_of_eq ?_) this
    congr 2
    simp only [inner_sub_left]; ring
  have hlim : Tendsto (fun s : Finset κ => 2 * (∫⁻ w, ‖itoIntegral P ℱ (fun t w (k : s) => W t w k)
          (fun r w (k : s) => inner ℝ (Φ₁ r w k) x) τ w - inner ℝ (M₁ τ w) x‖ₑ ^ 2 ∂P +
        ∫⁻ w, ‖itoIntegral P ℱ (fun t w (k : s) => W t w k)
          (fun r w (k : s) => inner ℝ (Φ₂ r w k) x) τ w - inner ℝ (M₂ τ w) x‖ₑ ^ 2 ∂P)) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞))
      ((hM₁.approx τ hτ x).add (hM₂.approx τ hτ x)) (Or.inr (by norm_num))
    simpa using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun s => zero_le) hbound

end HRS.MS.FinNoise
