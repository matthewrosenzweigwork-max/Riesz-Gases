import HRS.Sections.Q66AuxH
import HRS.Equilibrium.PreparationAux

/-!
# Packet Q66: Stein identity under `Q_{N,β}(μ)`, part 2 (density representation, bounds)
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Q66

open HRS.Q84d HRS.PDE HRS.PDE.MFAux HRS.PDE.MFSchauder

variable {d : ℕ} {s : ℝ} {N : ℕ}

/-- The one-body potential `V_ρ = -g * ρ`. -/
def q66_Vrho (d : ℕ) (s : ℝ) (ρ : Torus d → ℝ) : Torus d → ℝ :=
  fun x => -convFun (periodicRiesz d s) ρ x

theorem q66_Vrho_isCk1 (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) : Torus.IsCk 1 (q66_Vrho d s ρ) := by
  have F : MFInputs.MFKernelFacts d s := MFInputs.mfKernelFacts_of_two hd s hs0 hsd
  have h1 : Torus.IsCk 1 (convFun (periodicRiesz d s) ρ) :=
    convFun_isCk_one F.integrable (q66_isCk_of_smooth hρ.smooth 1)
  unfold Torus.IsCk at h1 ⊢
  exact h1.neg

theorem q66_Vrho_continuous (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) : Continuous (q66_Vrho d s ρ) :=
  Torus.continuous_of_continuous_lift (q66_Vrho_isCk1 hd hs0 hsd hρ).continuous

/-- `N F_N(X, μ) = H_{V_ρ}(X) + (N/2) ∬ g dμ dμ`. -/
theorem q66_Wen_eq {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (X : Config d N) :
    PreparationAux.Wen (periodicRiesz d s) N (withDensityReal ρ) X =
      canonicalHamiltonian (periodicRiesz d s) (q66_Vrho d s ρ) X +
        ((N : ℝ) / 2) * ∫ x, ∫ y, periodicRiesz d s (x - y) ∂(withDensityReal ρ) ∂(withDensityReal ρ) := by
  unfold PreparationAux.Wen
  rw [energy_identity (periodicRiesz d s) (fun x => periodicRiesz_neg x) ρ hρ.density.measurable
    (fun x => (hρ.pos x).le) X]
  unfold canonicalHamiltonian q66_Vrho
  simp only [Finset.sum_neg_distrib]
  ring

theorem q66_integral_Q {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (hg : Measurable (periodicRiesz d s))
    (β : ℝ) (f : Config d N → ℝ) :
    ∫ X, f X ∂(modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) =
      (PreparationAux.Zf (Measure.pi fun _ : Fin N => withDensityReal ρ)
        (PreparationAux.Wen (periodicRiesz d s) N (withDensityReal ρ)) β)⁻¹ *
      ∫ X, (∏ i, ρ (X i)) *
        (Real.exp (-β * PreparationAux.Wen (periodicRiesz d s) N (withDensityReal ρ) X) * f X) := by
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  rw [PreparationAux.integral_modulatedGibbs β hg f]
  congr 1
  rw [pi_withDensityReal_eq ρ hρ.density.measurable]
  have hRm : Measurable (fun X : Config d N => ∏ i, ENNReal.ofReal (ρ (X i))) :=
    Finset.measurable_prod _ fun i _ =>
      ENNReal.measurable_ofReal.comp (hρ.density.measurable.comp (measurable_pi_apply i))
  rw [integral_withDensity_eq_integral_toReal_smul hRm
    (Filter.Eventually.of_forall fun X => ENNReal.prod_lt_top fun i _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_prod]
  congr 1
  exact Finset.prod_congr rfl fun i _ => ENNReal.toReal_ofReal (hρ.pos _).le

end HRS.Q66

end
