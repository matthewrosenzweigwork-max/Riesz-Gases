import HRS.Kernel.D1

/-!
# The response equation for `d ≥ 1` (work package KERN-02, `d = 1` extension)

The proofs of `exists_unique_response` and `susceptibilityCov_bounds` use only that the kernel
`g = periodicRiesz d s` is integrable and has real nonnegative Fourier coefficients
`ĝ(k) = rieszCoeff d s k` (`exists_unique_response_of_kernel`,
`susceptibilityCov_bounds_of_kernel`).  For `d = 1` these inputs are
`integral_periodicRiesz_d1` and `periodicRiesz_fourierCoeff_d1`, so the same statements hold
for `1 ≤ d`.  (The source states the equilibrium operators only under the standing hypothesis
`d ≥ 2`; this file records that the argument does not need it.)
-/

noncomputable section

open MeasureTheory

namespace HRS

section ResponseD1

variable {d : ℕ} {s : ℝ}

theorem rieszCoeff_nonneg_one_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (k : Lattice d) :
    0 ≤ rieszCoeff d s k := by
  by_cases hk : k = 0
  · simp [rieszCoeff, hk]
  · have h1 := one_le_enorm k hk
    have h2 := KernelD1Aux.rieszConst_pos_d1 hd hs0 hsd
    unfold rieszCoeff
    simp only [hk, ite_false]
    refine (mul_pos h2 (Real.rpow_pos_of_pos ?_ _)).le
    have : (0 : ℝ) < Lattice.enorm k := lt_of_lt_of_le one_pos h1
    positivity

theorem integrable_periodicRiesz_one_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    Integrable (periodicRiesz d s) := by
  rcases Nat.eq_or_lt_of_le hd with rfl | h2
  · exact (integral_periodicRiesz_d1 hs0 (by simpa using hsd)).1
  · exact (integral_periodicRiesz (by omega) hs0 hsd).1

theorem periodicRiesz_fourierCoeff_one_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (k : Lattice d) :
    Torus.funFourierCoeff (fun x => (periodicRiesz d s x : ℂ)) k = rieszCoeff d s k := by
  rcases Nat.eq_or_lt_of_le hd with rfl | h2
  · exact periodicRiesz_fourierCoeff_d1 hs0 (by simpa using hsd) k
  · exact periodicRiesz_fourierCoeff (by omega) hs0 hsd k

/-- `exists_unique_response` for `1 ≤ d`. -/
theorem exists_unique_response_one_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (ρ : Torus d → ℝ) (hρ : IsProbDensity ρ) (Λ : ℝ) (hΛ : ∀ x, ρ x ≤ Λ)
    (β : ℝ) (hβ : 0 ≤ β) (ψ : Torus d → ℝ) (hψ : MemLp ψ 2 (withDensityReal ρ)) :
    ∃ h, IsResponse (periodicRiesz d s) (withDensityReal ρ) β ψ h ∧
      ∀ h', IsResponse (periodicRiesz d s) (withDensityReal ρ) β ψ h' →
        h' =ᵐ[withDensityReal ρ] h :=
  exists_unique_response_of_kernel (integrable_periodicRiesz_one_le hd hs0 hsd) _
    (rieszCoeff_nonneg_one_le hd hs0 hsd) (periodicRiesz_fourierCoeff_one_le hd hs0 hsd)
    ρ hρ Λ hΛ β hβ ψ hψ

/-- `susceptibilityCov_bounds` for `1 ≤ d`. -/
theorem susceptibilityCov_bounds_one_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (ρ : Torus d → ℝ) (hρ : IsProbDensity ρ) (Λ : ℝ) (hΛ : ∀ x, ρ x ≤ Λ)
    (β : ℝ) (hβ : 0 ≤ β) :
    ∃ c C : ℝ, 0 < c ∧ ∀ φ : Torus d → ℝ, MemLp φ 2 (withDensityReal ρ) →
      c * l2Inner (withDensityReal ρ) (projMean (withDensityReal ρ) φ)
          (projMean (withDensityReal ρ) φ) ≤
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β φ φ ∧
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β φ φ ≤
        C * l2Inner (withDensityReal ρ) (projMean (withDensityReal ρ) φ)
          (projMean (withDensityReal ρ) φ) :=
  susceptibilityCov_bounds_of_kernel (integrable_periodicRiesz_one_le hd hs0 hsd) _
    (rieszCoeff_nonneg_one_le hd hs0 hsd) (periodicRiesz_fourierCoeff_one_le hd hs0 hsd)
    ρ hρ Λ hΛ β hβ

end ResponseD1

end HRS
