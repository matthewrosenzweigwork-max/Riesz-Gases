import HRS.Main.ThermLin2As2
import HRS.Main.ThermLinAux5

/-!
# THERMLIN2, packet As, part 3: `thermlin_gaussian_comparison`

The statement of `HRS.Main.thermlin_gaussian_comparison` (ThermLinAux5) is that of `tl2_assembly`; this file proves it
from `tl2_assembly_proof` and ties the statement to the frozen one.  It inherits the black-box use of the plan statement
`tl2_zero_start_comparison` (E1) from `tl2_assembly_proof` (to be swapped by the orchestrator at integration).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Main

variable {d : ℕ}

/-- The Gaussian comparison `Y` versus the stationary field `Z_β` (TeX L6969-7011): for the prepared linear process
`Y` with initial law `ν` on the horizon `a + T` and the stationary Gaussian field `Z`,
`W_1^{𝒳_{m,T}}(law Y^{a+·}, law Z^{0+·}) ≤ C e^{-ca}(1 + ‖ν‖_{L¹(E_m)})` and
`W_2^{𝒳_{m,T}}(law Y^{a+·}, law Z^{0+·}) ≤ C e^{-ca}(1 + ‖ν‖_{L²(E_m)})`, with `C, c` independent of `a ≥ 0`, `ν`, `Y`, `Z`. -/
theorem thermlin_gaussian_comparison_proof (S : PreparedData d) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ)
    (hT : 0 < T) (ρβ : Torus d → ℝ) (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ a : ℝ, 0 ≤ a → ∀ (ν : Measure (NegSobolev d m)) [IsProbabilityMeasure ν]
        {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Y₀ : Ω' → NegSobolev d m) (Y : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a + T) ν P' Y₀ Y →
      ∀ {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
        (Z : ℝ → Ω'' → NegSobolev d m),
        IsStationaryGaussianField P'' S.s S.β S.hs0 S.hsd S.hβ S.V ρβ m Z →
        wassersteinE 1 (law P' (windowPath m T a Y)) (law P'' (windowPath m T 0 Z)) ≤
          ENNReal.ofReal (C * Real.exp (-c * a)) * (1 + ∫⁻ y, ‖y‖ₑ ∂ν) ∧
        wassersteinE 2 (law P' (windowPath m T a Y)) (law P'' (windowPath m T 0 Z)) ≤
          ENNReal.ofReal (C * Real.exp (-c * a)) *
            (1 + (∫⁻ y, ‖y‖ₑ ^ (2 : ℝ) ∂ν) ^ ((1 : ℝ) / 2)) :=
  HRS.ThermLin.Plan2.tl2_assembly_proof S m hm T hT ρβ hρβ

example := (@thermlin_gaussian_comparison_proof : type_of% @thermlin_gaussian_comparison)

end Main

end HRS
