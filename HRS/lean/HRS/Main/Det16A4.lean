import HRS.Energy.G336C1Final
import HRS.PDE.MeanFieldKernelD1
import HRS.Duality.PairingExpansion

/-!
# Example A.16, lemma L2: the corrected energy at `N = 1` is bounded above

For `N = 1` the modulated energy is `-(g*ρ)(x) + ½ ∬ g ρ ρ` (the off-diagonal sum is empty).  Since
`g = periodicRiesz` is integrable and bounded below, this is bounded above by `B + ½ Λ ‖g‖₁`, uniformly in
the configuration and in the probability density `ρ ≤ Λ`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Main.Det16

variable {d : ℕ}

theorem det16_rieszEnergy_N1_le (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (Λ : ℝ) (hΛ : 0 ≤ Λ) :
    ∃ B : ℝ, ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d 1, rieszEnergy d s X (withDensityReal ρ) ≤ B := by
  obtain ⟨B0, hB0⟩ := periodicRiesz_ge_of_one_le hd hs0 hsd
  have hgi : Integrable (periodicRiesz d s) := CoercAux.integrable_periodicRiesz_one hd hs0 hsd
  set B : ℝ := |B0| with hB
  have hBg : ∀ z, -B ≤ periodicRiesz d s z := fun z => by
    have := hB0 z
    have := le_abs_self B0
    linarith
  have hB0' : 0 ≤ B := abs_nonneg _
  set M : ℝ := Λ * ∫ z, |periodicRiesz d s z| with hM
  have hM0 : 0 ≤ M := mul_nonneg hΛ (integral_nonneg fun z => abs_nonneg _)
  refine ⟨B + M / 2, fun ρ hρ hρΛ X => ?_⟩
  haveI hprob : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  -- the row integrals
  have hlow : ∀ x : Torus d, -B ≤ ∫ y, periodicRiesz d s (x - y) ∂(withDensityReal ρ) := by
    intro x
    by_cases hint : Integrable (fun y => periodicRiesz d s (x - y)) (withDensityReal ρ)
    · have := integral_mono (integrable_const (-B)) hint (fun y => hBg (x - y))
      simpa using this
    · rw [integral_undef hint]; linarith
  have hup : ∀ x : Torus d, ∫ y, periodicRiesz d s (x - y) ∂(withDensityReal ρ) ≤ M := by
    intro x
    have hW : Integrable (fun y => |periodicRiesz d s (x - y)|) (volume : Measure (Torus d)) :=
      hgi.abs.comp_sub_left x
    calc ∫ y, periodicRiesz d s (x - y) ∂(withDensityReal ρ)
        ≤ ∫ y, |periodicRiesz d s (x - y)| ∂(withDensityReal ρ) := by
          refine (le_abs_self _).trans ?_
          simpa [Real.norm_eq_abs] using
            norm_integral_le_integral_norm (μ := withDensityReal ρ)
              (fun y => periodicRiesz d s (x - y))
      _ ≤ Λ * ∫ y, |periodicRiesz d s (x - y)| :=
          HRS.Duality.integral_withDensityReal_le hρΛ hΛ (fun y => abs_nonneg _) hW
      _ = M := by rw [hM, integral_sub_left_eq_self (fun z => |periodicRiesz d s z|) volume x]
  have hout : ∫ x, ∫ y, periodicRiesz d s (x - y) ∂(withDensityReal ρ) ∂(withDensityReal ρ) ≤ M := by
    by_cases hint : Integrable (fun x => ∫ y, periodicRiesz d s (x - y) ∂(withDensityReal ρ))
        (withDensityReal ρ)
    · have := integral_mono hint (integrable_const M) hup
      simpa using this
    · rw [integral_undef hint]; exact hM0
  have hF : rieszEnergy d s X (withDensityReal ρ) =
      - (∫ y, periodicRiesz d s (X 0 - y) ∂(withDensityReal ρ)) +
        (1 / 2) * ∫ x, ∫ y, periodicRiesz d s (x - y) ∂(withDensityReal ρ) ∂(withDensityReal ρ) := by
    unfold rieszEnergy modulatedEnergyKernel modulatedEnergy
    simp [Fin.sum_univ_one]
  rw [hF]
  have := hlow (X 0)
  linarith

theorem det16_energy_N1_bdd (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (C₀ Λ : ℝ) (hΛ : 0 ≤ Λ) :
    ∃ B : ℝ, ∀ (D : DynData d), D.s = s → ∀ (ρ : ℝ → Torus d → ℝ) (t : ℝ),
      IsProbDensity (ρ t) → (∀ x, ρ t x ≤ Λ) → ∀ X : Config d 1,
      correctedEnergy D C₀ Λ ρ X t ≤ B := by
  obtain ⟨B, hB⟩ := det16_rieszEnergy_N1_le hd hs0 hsd Λ hΛ
  refine ⟨B + oNΛ d s C₀ Λ 1, fun D hDs ρ t hρ hρΛ X => ?_⟩
  unfold correctedEnergy
  rw [hDs]
  linarith [hB (ρ t) hρ hρΛ X]

end HRS.Main.Det16
