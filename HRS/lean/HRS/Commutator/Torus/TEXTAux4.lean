import HRS.Commutator.Torus.TEXTAux3

/-!
# T-EXT-A helpers, part 4: rescaling of an `ℝ^d` kernel

`Keta Kt γ η (x) = η^{γ-d} Kt(x/η)`: global decay bound, integrability, Fourier transform
`𝓕 Keta (ξ) = η^γ 𝓕 Kt (ηξ)`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

/-- The rescaled kernel `η^{γ-d} K̃(x/η)`. -/
def textKeta (Kt : Euc d → ℝ) (γ η : ℝ) (x : Euc d) : ℝ := η ^ (γ - d) * Kt (η⁻¹ • x)

lemma text_Kt_global {γ : ℝ} (hγ : 0 < γ) (hγd : γ < d) {Kt : Euc d → ℝ} {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hnear : ∀ x : Euc d, x ≠ 0 → ‖x‖ ≤ 1 → |Kt x| ≤ C₀ * ‖x‖ ^ (γ - d))
    {M : ℕ} (hM : d ≤ M) {Cm : ℝ} (hCm : 0 < Cm)
    (hfar : ∀ x : Euc d, 1 ≤ ‖x‖ → |Kt x| ≤ Cm * ‖x‖ ^ (-(M : ℝ))) :
    ∀ z : Euc d, z ≠ 0 → |Kt z| ≤ (C₀ + Cm) * ‖z‖ ^ (-(M : ℝ)) := by
  intro z hz
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  by_cases h1 : ‖z‖ ≤ 1
  · have h2 : ‖z‖ ^ (γ - d) ≤ ‖z‖ ^ (-(M : ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_ge hzpos h1 ?_
      have : (d : ℝ) ≤ M := by exact_mod_cast hM
      linarith
    have h3 : 0 ≤ ‖z‖ ^ (-(M : ℝ)) := by positivity
    calc |Kt z| ≤ C₀ * ‖z‖ ^ (γ - d) := hnear z hz h1
      _ ≤ C₀ * ‖z‖ ^ (-(M : ℝ)) := mul_le_mul_of_nonneg_left h2 hC₀.le
      _ ≤ (C₀ + Cm) * ‖z‖ ^ (-(M : ℝ)) := by nlinarith
  · push Not at h1
    have h3 : 0 ≤ ‖z‖ ^ (-(M : ℝ)) := by positivity
    calc |Kt z| ≤ Cm * ‖z‖ ^ (-(M : ℝ)) := hfar z h1.le
      _ ≤ (C₀ + Cm) * ‖z‖ ^ (-(M : ℝ)) := by nlinarith

lemma text_Keta_bound {γ η : ℝ} (hη : 0 < η) {Kt : Euc d → ℝ} {A : ℝ} {M : ℕ} (hA : 0 ≤ A)
    (hb : ∀ z : Euc d, z ≠ 0 → |Kt z| ≤ A * ‖z‖ ^ (-(M : ℝ))) :
    ∀ z : Euc d, z ≠ 0 → |textKeta Kt γ η z| ≤ (A * η ^ (γ - d + M)) * ‖z‖ ^ (-(M : ℝ)) := by
  intro z hz
  have hz' : η⁻¹ • z ≠ 0 := by
    intro h; apply hz
    have := congrArg (fun v => η • v) h
    simpa [smul_smul, hη.ne'] using this
  have h1 := hb _ hz'
  have hn : ‖η⁻¹ • z‖ = η⁻¹ * ‖z‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hη)]
  rw [hn] at h1
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h2 : (η⁻¹ * ‖z‖) ^ (-(M : ℝ)) = η ^ (M : ℝ) * ‖z‖ ^ (-(M : ℝ)) := by
    rw [Real.mul_rpow (inv_pos.2 hη).le hzpos.le, Real.inv_rpow hη.le, Real.rpow_neg hη.le,
      inv_inv]
  rw [h2] at h1
  unfold textKeta
  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hη _)]
  calc η ^ (γ - d) * |Kt (η⁻¹ • z)| ≤ η ^ (γ - d) * (A * (η ^ (M : ℝ) * ‖z‖ ^ (-(M : ℝ)))) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_pos_of_pos hη _).le
    _ = (A * η ^ (γ - d + M)) * ‖z‖ ^ (-(M : ℝ)) := by
        rw [Real.rpow_add hη]; ring

lemma text_Keta_measurable {Kt : Euc d → ℝ} (hK : Measurable Kt) (γ η : ℝ) :
    Measurable (textKeta Kt γ η) := by
  unfold textKeta
  exact measurable_const.mul (hK.comp (by fun_prop))

lemma text_Keta_integrable {Kt : Euc d → ℝ} (hK : Integrable Kt) {η : ℝ} (hη : 0 < η) (γ : ℝ) :
    Integrable (textKeta Kt γ η) := by
  unfold textKeta
  exact (hK.comp_smul (inv_ne_zero hη.ne')).const_mul _

lemma text_fourier_Keta {η : ℝ} (hη : 0 < η) (Kt : Euc d → ℝ) (γ : ℝ) (ξ : Euc d) :
    𝓕 (fun x : Euc d => ((textKeta Kt γ η x : ℝ) : ℂ)) ξ =
      ((η ^ γ : ℝ) : ℂ) * 𝓕 (fun x : Euc d => ((Kt x : ℝ) : ℂ)) (η • ξ) := by
  rw [Real.fourier_eq, Real.fourier_eq]
  have key : ∀ v : Euc d, 𝐞 (-inner ℝ v ξ) • (((textKeta Kt γ η v : ℝ)) : ℂ) =
      ((η ^ (γ - d) : ℝ) : ℂ) *
        ((fun u : Euc d => 𝐞 (-inner ℝ (η • u) ξ) • ((Kt u : ℝ) : ℂ)) (η⁻¹ • v)) := by
    intro v
    simp only [textKeta, smul_smul, mul_inv_cancel₀ hη.ne', one_smul]
    simp only [Circle.smul_def, smul_eq_mul]
    push_cast
    ring
  simp_rw [key]
  rw [integral_const_mul]
  have := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg (μ := (volume : Measure (Euc d)))
    (fun u : Euc d => 𝐞 (-inner ℝ (η • u) ξ) • ((Kt u : ℝ) : ℂ)) hη.le
  rw [this, finrank_euclideanSpace_fin]
  have h2 : ∀ u : Euc d, 𝐞 (-inner ℝ (η • u) ξ) • ((Kt u : ℝ) : ℂ) =
      𝐞 (-inner ℝ u (η • ξ)) • ((Kt u : ℝ) : ℂ) := by
    intro u
    rw [inner_smul_left, inner_smul_right]
    simp
  simp_rw [h2]
  rw [Complex.real_smul]
  have h3 : ((η ^ (γ - d) : ℝ) : ℂ) * ((η ^ d : ℝ) : ℂ) = ((η ^ γ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.rpow_sub hη, Real.rpow_natCast]
    congr 1
    field_simp
  rw [← mul_assoc, h3]

end HRS.Commutator.TorusNote
