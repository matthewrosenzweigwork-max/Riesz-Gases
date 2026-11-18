import HRS.Commutator.Torus.LEIBTAux7

/-!
# LEIB-T helpers, part 8: integrability / change of variables for the shifted symbol integrals
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma leibt_cov0 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (G : 𝔼 → F) {N : ℝ}
    (hN : 0 < N) (a : 𝔼) :
    ∫ ξ, G ξ = ((N ^ d : ℝ)⁻¹) • ∫ ζ, G (a + N⁻¹ • ζ) := by
  have h1 : ∫ ξ, G ξ = ∫ z, G (a + z) := (integral_add_left_eq_self (μ := (volume : Measure 𝔼)) G a).symm
  have h2 := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure 𝔼) (fun z : 𝔼 => G (a + z)) hN.le
  rw [finrank_euclideanSpace_fin] at h2
  have hNd : (0 : ℝ) < N ^ d := by positivity
  rw [h1, h2, smul_smul, inv_mul_cancel₀ hNd.ne', one_smul]

lemma leibt_integrable_cov {F : Type*} [NormedAddCommGroup F] (G : 𝔼 → F) {N : ℝ} (hN : 0 < N)
    (a : 𝔼) (h : Integrable (fun ζ : 𝔼 => G (a + N⁻¹ • ζ))) : Integrable G := by
  have h1 : Integrable (fun z : 𝔼 => G (a + z)) :=
    (integrable_comp_smul_iff (volume : Measure 𝔼) (fun z : 𝔼 => G (a + z)) (inv_ne_zero hN.ne')).1 h
  have := h1.comp_add_left (-a)
  simpa using this

lemma leibt_m_bound (α : ℝ) : ∃ (C₀ : ℝ) (k₀ : ℕ), 0 ≤ C₀ ∧ ∀ ξ : 𝔼, ‖leibt_m α ξ‖ ≤ C₀ * (1 + ‖ξ‖) ^ k₀ := by
  obtain ⟨k₀, C₀, hC₀, hb⟩ := (HRS.Commutator.Whole.XLI.bsymX_temperate (d := d) α).norm_iteratedFDeriv_le_uniform 0
  exact ⟨C₀, k₀, hC₀, fun ξ => by simpa using hb 0 le_rfl ξ⟩

lemma leibt_psi_integrable (ψ : SchwartzMap 𝔼 ℂ) (k : ℕ) :
    Integrable (fun ζ : 𝔼 => (1 + ‖ζ‖) ^ k * ‖ψ ζ‖) := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ ζ : 𝔼, (1 + ‖ζ‖) ^ (k + (d + 1)) * ‖ψ ζ‖ ≤ C := by
    refine ⟨2 ^ (k + (d + 1)) * (Finset.Iic (k + (d + 1), 0)).sup (schwartzSeminormFamily ℂ 𝔼 ℂ) ψ, fun ζ => ?_⟩
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k + (d + 1), 0)) (k := k + (d + 1))
      (n := 0) le_rfl le_rfl ψ ζ
    rw [norm_iteratedFDeriv_zero] at this
    exact this
  have hint : Integrable (fun ζ : 𝔼 => (1 + ‖ζ‖) ^ (-((d : ℝ) + 1))) (volume : Measure 𝔼) :=
    integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; linarith)
  refine (hint.const_mul C).mono' ?_ (Filter.Eventually.of_forall fun ζ => ?_)
  · exact (by fun_prop : Continuous fun ζ : 𝔼 => (1 + ‖ζ‖) ^ k * ‖ψ ζ‖).aestronglyMeasurable
  · have hpos : 0 < 1 + ‖ζ‖ := by positivity
    rw [Real.norm_of_nonneg (by positivity)]
    have h1 := hC ζ
    have : (1 + ‖ζ‖) ^ (k + (d + 1)) = (1 + ‖ζ‖) ^ k * (1 + ‖ζ‖) ^ (d + 1) := pow_add _ _ _
    rw [this, mul_assoc] at h1
    have h2 : (1 + ‖ζ‖) ^ k * ‖ψ ζ‖ = ((1 + ‖ζ‖) ^ (d + 1))⁻¹ * ((1 + ‖ζ‖) ^ k * (1 + ‖ζ‖) ^ (d + 1) * ‖ψ ζ‖) := by
      field_simp
    rw [h2, Real.rpow_neg hpos.le]
    have h3 : (1 + ‖ζ‖) ^ ((d : ℝ) + 1) = (1 + ‖ζ‖) ^ (d + 1) := by
      rw [← Real.rpow_natCast]; push_cast; ring_nf
    rw [h3]
    calc ((1 + ‖ζ‖) ^ (d + 1))⁻¹ * ((1 + ‖ζ‖) ^ k * (1 + ‖ζ‖) ^ (d + 1) * ‖ψ ζ‖)
        ≤ ((1 + ‖ζ‖) ^ (d + 1))⁻¹ * C := by
          gcongr
          simpa [mul_assoc] using h1
      _ = C * ((1 + ‖ζ‖) ^ (d + 1))⁻¹ := mul_comm _ _

end HRS.Commutator.TorusNote
