import HRS.Commutator.Torus.LEIBTAux8

/-!
# LEIB-T helpers, part 9: the shifted-symbol integrals `∫ m(a + N⁻¹ζ) ψ(ζ) dζ`
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma leibt_shift_bound (α : ℝ) (ψ : SchwartzMap 𝔼 ℂ) :
    ∃ (B : ℝ) (k₀ : ℕ), 0 ≤ B ∧ ∀ (N : ℝ), 1 ≤ N → ∀ a : 𝔼,
      Integrable (fun ζ : 𝔼 => leibt_m α (a + N⁻¹ • ζ) * ψ ζ) ∧
      ∫ ζ : 𝔼, ‖leibt_m α (a + N⁻¹ • ζ) * ψ ζ‖ ≤ B * (1 + ‖a‖) ^ k₀ := by
  obtain ⟨C₀, k₀, hC₀, hm⟩ := leibt_m_bound (d := d) α
  set J : ℝ := ∫ ζ : 𝔼, (1 + ‖ζ‖) ^ k₀ * ‖ψ ζ‖ with hJ
  have hJint := leibt_psi_integrable ψ k₀
  have hJ0 : 0 ≤ J := integral_nonneg fun ζ => by positivity
  refine ⟨C₀ * J, k₀, by positivity, fun N hN a => ?_⟩
  have hN0 : 0 < N := by linarith
  have hbd : ∀ ζ : 𝔼, ‖leibt_m α (a + N⁻¹ • ζ) * ψ ζ‖ ≤
      C₀ * (1 + ‖a‖) ^ k₀ * ((1 + ‖ζ‖) ^ k₀ * ‖ψ ζ‖) := by
    intro ζ
    rw [norm_mul]
    have h1 : ‖a + N⁻¹ • ζ‖ ≤ ‖a‖ + ‖ζ‖ := by
      calc ‖a + N⁻¹ • ζ‖ ≤ ‖a‖ + ‖N⁻¹ • ζ‖ := norm_add_le _ _
        _ ≤ ‖a‖ + ‖ζ‖ := by
          gcongr
          rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hN0]
          calc N⁻¹ * ‖ζ‖ ≤ 1 * ‖ζ‖ := by gcongr; exact inv_le_one_of_one_le₀ hN
            _ = ‖ζ‖ := one_mul _
    have h2 : 1 + ‖a + N⁻¹ • ζ‖ ≤ (1 + ‖a‖) * (1 + ‖ζ‖) := by
      nlinarith [norm_nonneg a, norm_nonneg ζ]
    have h3 := hm (a + N⁻¹ • ζ)
    calc ‖leibt_m α (a + N⁻¹ • ζ)‖ * ‖ψ ζ‖ ≤ (C₀ * (1 + ‖a + N⁻¹ • ζ‖) ^ k₀) * ‖ψ ζ‖ := by gcongr
      _ ≤ (C₀ * ((1 + ‖a‖) * (1 + ‖ζ‖)) ^ k₀) * ‖ψ ζ‖ := by gcongr
      _ = _ := by rw [mul_pow]; ring
  have hcont : Continuous fun ζ : 𝔼 => leibt_m α (a + N⁻¹ • ζ) * ψ ζ := by
    have := (HRS.Commutator.Whole.XLI.bsymX_temperate (d := d) α).1.continuous
    exact (this.comp (continuous_const.add (continuous_const_smul _))).mul ψ.continuous
  have hint : Integrable (fun ζ : 𝔼 => leibt_m α (a + N⁻¹ • ζ) * ψ ζ) :=
    ((hJint.const_mul (C₀ * (1 + ‖a‖) ^ k₀))).mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hbd)
  refine ⟨hint, ?_⟩
  calc ∫ ζ : 𝔼, ‖leibt_m α (a + N⁻¹ • ζ) * ψ ζ‖
      ≤ ∫ ζ : 𝔼, C₀ * (1 + ‖a‖) ^ k₀ * ((1 + ‖ζ‖) ^ k₀ * ‖ψ ζ‖) :=
        integral_mono hint.norm (hJint.const_mul _) hbd
    _ = C₀ * J * (1 + ‖a‖) ^ k₀ := by
        rw [integral_const_mul, hJ]; ring

end HRS.Commutator.TorusNote
