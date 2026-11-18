import HRS.ME.BiasE
import HRS.ME.CritCenteredPathProved
import HRS.Sections.Q41Aux14

/-!
# Chunk E, row 2.10 (fixed-`β` closure): `critical_bias_constants` for fixed `β`

`critical_bias_constants_fixed` is the frozen `HRS.Main.critical_bias_constants` with `β ∈ [β₋, β₊]` moved
to the outside (constants depend on `β`, chosen before `ρ_β`, `u`, `N`, the realization and `Z`); this is the
statement the TeX proves (TeX L5709-5750).

Proof.  `η_N^{u+·} = ζ_N^{u+·} + h_N` almost surely (`windowFluc_ae_eq`), with the constant path
`h_N = √N (m_N - μ_β)`.  The centered path rate `critical_centered_path_proved` bounds
`W_p(Law ζ, Law Z)` and `d_k(Law ζ, Law Z)` by `C N^{-1/2}`; the expansion of the marginal
(`critical_marginal_expansion_fixed`) bounds `‖h_N - r_N b‖` by `C √(log N)/√N`; and the abstract
cores `core_wasserstein`, `core_smooth` (translation of a random path by a deterministic one) give clauses 1
and 2.  Clause 3 is `smoothConstant_pos_of_aemeasurable`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.Bias

variable {d : ℕ}

open HRS HRS.Main

/-- A thermal density of a smooth potential is a smooth positive density. -/
theorem smoothPos_of_thermal (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    {V : Torus d → ℝ} (hV : Torus.IsSmooth V) {ρ : Torus d → ℝ}
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) : SmoothPosDensity ρ := by
  obtain ⟨hpos, hsm⟩ := Q41.q41_thermal_regular hd hs0 hsd hβ hV hρ
  exact ⟨hρ.1, hsm, hpos⟩

/-- Two thermal densities of a smooth potential coincide. -/
theorem thermal_unique_of_smooth (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    {V : Torus d → ℝ} (hV : Torus.IsSmooth V) {ρ ρ' : Torus d → ℝ}
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ)
    (hρ' : IsThermalDensity (periodicRiesz d s) V β ρ') : ρ = ρ' := by
  obtain ⟨hp, hsm⟩ := Q41.q41_thermal_regular hd hs0 hsd hβ hV hρ
  obtain ⟨hp', hsm'⟩ := Q41.q41_thermal_regular hd hs0 hsd hβ hV hρ'
  have hc : Continuous ρ := PoleCavityAux.continuous_of_smoothPos ⟨hρ.1, hsm, hp⟩
  have hc' : Continuous ρ' := PoleCavityAux.continuous_of_smoothPos ⟨hρ'.1, hsm', hp'⟩
  exact (PDE.MFThermal.thermal_unique hd s hs0 hsd β hβ V ρ ρ' hρ hc hp hρ' hc' hp').symm

/-- The canonical Gibbs law at the thermal density is the modulated Gibbs law (critical case). -/
theorem canonical_eq_modulated_thermal (hd : 2 ≤ d) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d)
    {V : Torus d → ℝ} (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
    (hρ : IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) V β ρ) (N : ℕ) :
    canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β =
      modulatedGibbs (periodicRiesz d ((d : ℝ) / 2)) N β (withDensityReal ρ) := by
  have hρs := smoothPos_of_thermal hd hs0 hsd hβ hV hρ
  obtain ⟨Λ, hΛ0, hΛ⟩ := PoleCavityAux.exists_density_bound hρs
  refine canonicalGibbs_eq_modulatedGibbs (periodicRiesz d ((d : ℝ) / 2)) V β ρ hρ
    (fun x => periodicRiesz_neg x) ?_
  intro x
  exact (CoercAux.J_bounds (by omega : 1 ≤ d) hs0 hsd one_pos hρs.density hΛ0.le hΛ x).1

end HRS.ME.Bias
