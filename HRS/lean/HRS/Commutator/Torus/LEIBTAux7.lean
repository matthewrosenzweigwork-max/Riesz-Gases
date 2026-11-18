import HRS.Commutator.Torus.LEIBTAux6

/-!
# LEIB-T helpers, part 7: Fourier transform of a modulated dilated cutoff, and its Bessel derivative

For `ψ = 𝓕 χ`: `𝓕[e_a χ(N⁻¹ ·)](ξ) = N^d ψ(N(ξ - a))`, and the change of variables `ξ = a + N⁻¹ ζ`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- The exponential `e_a(y) = exp(2π i ⟨a, y⟩)`. -/
def leibt_e (a y : 𝔼) : ℂ := Complex.exp (((2 * Real.pi * ⟪a, y⟫ : ℝ) : ℂ) * Complex.I)

lemma leibt_fourier_modcut (χ : 𝔼 → ℂ) {N : ℝ} (hN : 0 < N) (a ξ : 𝔼) :
    𝓕 (fun y : 𝔼 => leibt_e a y * χ (N⁻¹ • y)) ξ = ((N ^ d : ℝ) : ℂ) * 𝓕 χ (N • (ξ - a)) := by
  rw [Real.fourier_eq', Real.fourier_eq']
  have h1 : ∀ y : 𝔼, Complex.exp (((-2 * Real.pi * ⟪y, ξ⟫ : ℝ) : ℂ) * Complex.I) • (leibt_e a y * χ (N⁻¹ • y)) =
      (fun z : 𝔼 => Complex.exp (((-2 * Real.pi * ⟪z, N • (ξ - a)⟫ : ℝ) : ℂ) * Complex.I) • χ z) (N⁻¹ • y) := by
    intro y
    simp only [smul_eq_mul]
    unfold leibt_e
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    · rw [inner_smul_left, inner_smul_right, inner_sub_right]
      simp only [conj_trivial, real_inner_comm]
      have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
      push_cast
      field_simp
      ring
  simp_rw [h1]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume (fun z : 𝔼 => Complex.exp (((-2 * Real.pi * ⟪z, N • (ξ - a)⟫ : ℝ) : ℂ) * Complex.I) • χ z) hN.le]
  rw [finrank_euclideanSpace_fin]
  simp [Complex.real_smul]


lemma leibt_cov (m ψ : 𝔼 → ℂ) {N : ℝ} (hN : 0 < N) (a x : 𝔼) :
    ∫ ξ : 𝔼, leibt_e x ξ * (m ξ * (((N ^ d : ℝ) : ℂ) * ψ (N • (ξ - a)))) =
      leibt_e x a * ∫ ζ : 𝔼, leibt_e (N⁻¹ • x) ζ * (m (a + N⁻¹ • ζ) * ψ ζ) := by
  set h : 𝔼 → ℂ := fun ξ => leibt_e x ξ * (m ξ * (((N ^ d : ℝ) : ℂ) * ψ (N • (ξ - a)))) with hh
  have h1 : ∫ ξ, h ξ = ∫ z, h (a + z) := (integral_add_left_eq_self (μ := (volume : Measure 𝔼)) h a).symm
  have h2 := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure 𝔼) (fun z : 𝔼 => h (a + z)) hN.le
  rw [finrank_euclideanSpace_fin] at h2
  have hNd : (0 : ℝ) < N ^ d := by positivity
  have h3 : ∫ z, h (a + z) = ((N ^ d : ℝ)⁻¹ : ℝ) • ∫ ζ : 𝔼, h (a + N⁻¹ • ζ) := by
    rw [h2, smul_smul, inv_mul_cancel₀ hNd.ne', one_smul]
  rw [h1, h3]
  have h4 : ∀ ζ : 𝔼, h (a + N⁻¹ • ζ) = ((N ^ d : ℝ) : ℂ) * (leibt_e x a * (leibt_e (N⁻¹ • x) ζ * (m (a + N⁻¹ • ζ) * ψ ζ))) := by
    intro ζ
    simp only [hh]
    have e1 : N • (a + N⁻¹ • ζ - a) = ζ := by
      rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hN.ne', one_smul]
    rw [e1]
    unfold leibt_e
    have e2 : Complex.exp (((2 * Real.pi * ⟪x, a + N⁻¹ • ζ⟫ : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((2 * Real.pi * ⟪x, a⟫ : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((2 * Real.pi * ⟪N⁻¹ • x, ζ⟫ : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      rw [inner_add_right, inner_smul_left, inner_smul_right]
      simp only [conj_trivial]
      push_cast
      ring
    rw [e2]
    ring
  simp_rw [h4]
  rw [integral_const_mul, integral_const_mul, ← integral_const_mul]
  simp only [Complex.real_smul]
  push_cast
  have hN' : (N : ℂ) ^ d ≠ 0 := by exact_mod_cast hNd.ne'
  field_simp

end HRS.Commutator.TorusNote
