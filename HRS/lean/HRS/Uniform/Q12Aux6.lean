import HRS.Uniform.Q12Aux5

/-!
# Q12, part 6: heat-filtered coercivity with the exact correction `oNΛ`
-/

noncomputable section

open MeasureTheory Filter Topology Set
open HRS HRS.CoercAux

namespace HRS.Uniform.Q12

variable {d : ℕ}

lemma q12_continuous_heatS {φ : Torus d → ℝ} (hc : Continuous φ) (L : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (heatS L ε φ) := by
  unfold heatS
  refine continuous_finsetSum _ fun j _ => ?_
  exact continuous_const.mul (heatP_continuous hc (by positivity))

theorem q12_filtered_core (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀ K : ℝ, 0 ≤ C₀ ∧ 0 ≤ K ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∀ L : ℕ, 1 ≤ L → ∀ N : ℕ, 2 ≤ N →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
        0 ≤ rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N ∧
        ∀ φ : Torus d → ℝ, Torus.IsCk ((2 * L : ℕ) : WithTop ℕ∞) φ →
          HasFiniteHomSobolev (((d : ℝ) - s) / 2) φ →
          ∀ A : ℝ, 0 ≤ A →
          (∀ x, |((Torus.laplacian : (Torus d → ℝ) → Torus d → ℝ)^[L] φ) x| ≤ A) →
            |∫ x, φ x ∂(empirical X) - ∫ x, φ x ∂(withDensityReal ρ)| ≤
              2 ^ L * K * homSobolev (((d : ℝ) - s) / 2) φ *
                  Real.sqrt (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N) +
                2 * (smearScale d N Λ ^ 2) ^ L * A := by
  obtain ⟨C₀, hC₀, hE⟩ := coercivity_energy hd hs0 hsd
  obtain ⟨Cl, hCl0, hCl⟩ := q12_fourier_heatS hd hs0 hsd
  refine ⟨C₀, Real.sqrt (2 * Cl), hC₀, Real.sqrt_nonneg _, ?_⟩
  intro Λ hΛ L hL N hN ρ hρ hρΛ X hX
  have hN1 : 1 ≤ N := by omega
  have hΛ0 : 0 < Λ := by linarith
  obtain ⟨hE0, hE1⟩ := hE Λ hΛ N hN ρ hρ hρΛ X hX
  set lam := smearScale d N Λ with hlam
  have hlam0 : 0 < lam := smearScale_pos (d := d) hN1 hΛ0
  have hε : 0 < lam ^ 2 := by positivity
  set S := rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N with hS
  have hS0 : 0 ≤ S := by linarith
  refine ⟨hS0, fun φ hφ hhom A hA0 hA => ?_⟩
  haveI := isProb_withDensityReal hρ
  haveI := empirical_isProbabilityMeasure (d := d) (by omega : 0 < N) X
  set μ := withDensityReal ρ with hμ
  have hc : Continuous φ := q12_continuous_of_isCk (hφ.of_le (by
    exact_mod_cast (by omega : 2 ≤ 2 * L)))
  have hcS := q12_continuous_heatS hc L hε
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  have hsup : ∀ x, |φ x - heatS (n + 1) (lam ^ 2) φ x| ≤ (lam ^ 2) ^ (n + 1) * A := fun x =>
    q12_sup_bound hd n hφ (q12_heatGen_iter_bound (n + 1) hφ hA) hε x
  have h1 := abs_integral_sub_le (Pm := empirical X) hc hcS hsup
  have h2 := abs_integral_sub_le (Pm := μ) hc hcS hsup
  have h3 := hCl hε (by omega : 0 < N) X μ hc hhom (n + 1)
  have h4 : Real.sqrt (Cl * Esq d s (lam ^ 2) X μ) ≤ Real.sqrt (2 * Cl) * Real.sqrt S := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    nlinarith
  have hhom0 : 0 ≤ Real.sqrt (homSobolevSq (((d : ℝ) - s) / 2) φ) := Real.sqrt_nonneg _
  have h5 : 2 ^ (n + 1) * (Real.sqrt (homSobolevSq (((d : ℝ) - s) / 2) φ) *
      Real.sqrt (Cl * Esq d s (lam ^ 2) X μ)) ≤
      2 ^ (n + 1) * (Real.sqrt (homSobolevSq (((d : ℝ) - s) / 2) φ) *
        (Real.sqrt (2 * Cl) * Real.sqrt S)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hhom0) (by positivity)
  have hdec : ∫ x, φ x ∂(empirical X) - ∫ x, φ x ∂μ =
      (∫ x, φ x ∂(empirical X) - ∫ x, heatS (n + 1) (lam ^ 2) φ x ∂(empirical X)) -
        (∫ x, φ x ∂μ - ∫ x, heatS (n + 1) (lam ^ 2) φ x ∂μ) +
        (∫ x, heatS (n + 1) (lam ^ 2) φ x ∂(empirical X) - ∫ x, heatS (n + 1) (lam ^ 2) φ x ∂μ) := by
    ring
  rw [hdec]
  have hhomS : homSobolev (((d : ℝ) - s) / 2) φ =
      Real.sqrt (homSobolevSq (((d : ℝ) - s) / 2) φ) := rfl
  rw [hhomS]
  have hAbs := (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add h1 h2)) (h3.trans h5))
  refine hAbs.trans (le_of_eq ?_)
  ring

end HRS.Uniform.Q12
