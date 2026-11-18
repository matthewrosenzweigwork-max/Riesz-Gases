import HRS.MC.E214A3
import HRS.Uniform.Q48bAux1
import HRS.Sections.Q41Aux14
import HRS.PDE.MeanFieldThermalUnique

/-!
# Packet E214I: the stationary prepared datum (P0b, P3 of `docs/MC_E214_SCOPE.md`)

Given `S : PreparedData d` and a thermal density `ρβ` for `(periodicRiesz d S.s, S.V, S.β)`, the stationary datum
`stationaryPrepared S ρβ hρβ` has the same `s, V, β`, initial density `ρβ`, constant mean-field trajectory `ρβ`.
`PreparedData` has no `β₀` field, so the preparation parameter is only in `EdgeworthHyp`; the stationary datum satisfies
`EdgeworthHyp Ss S.β m` (preparation at the equilibrium temperature `β₀ = β`).
-/

noncomputable section

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213Plan

namespace HRS.MC.E214I

variable {d : ℕ}

/-- Thermal densities of a prepared datum are smooth and positive. -/
theorem thermal_smoothPos (S : PreparedData d) {ρβ : Torus d → ℝ}
    (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) : SmoothPosDensity ρβ := by
  obtain ⟨hpos, hsm⟩ := Q41.q41_thermal_regular S.hd S.hs0 S.hsd S.hβ S.hV hρβ
  exact ⟨hρβ.1, hsm, hpos⟩

/-- The stationary prepared datum: same `s, V, β`, initial density and (constant) trajectory `ρβ`. -/
def stationaryPrepared (S : PreparedData d) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) : PreparedData d where
  s := S.s
  hs0 := S.hs0
  hsd := S.hsd
  hd := S.hd
  β := S.β
  hβ := S.hβ
  V := S.V
  hV := S.hV
  ρ0 := ρβ
  hρ0 := thermal_smoothPos S hρβ
  ρ := fun _ => ρβ
  hρ_init := rfl
  hρ := fun K _ => ⟨fun _ => PDE.coeffOf ρβ,
    HRS.Uniform.Q48b.q48b_isMFSolutionHK (by have := S.hd; omega) S.s S.hs0 S.hsd S.β S.hβ S.V S.hV ρβ hρβ
      (thermal_smoothPos S hρβ).smooth (thermal_smoothPos S hρβ).pos K,
    HRS.Uniform.Q48b.q48b_mfPath_const ρβ (thermal_smoothPos S hρβ).smooth⟩

section proj

variable (S : PreparedData d) (ρβ : Torus d → ℝ)
  (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ)

@[simp] theorem stationaryPrepared_s : (stationaryPrepared S ρβ hρβ).s = S.s := rfl
@[simp] theorem stationaryPrepared_β : (stationaryPrepared S ρβ hρβ).β = S.β := rfl
@[simp] theorem stationaryPrepared_V : (stationaryPrepared S ρβ hρβ).V = S.V := rfl
@[simp] theorem stationaryPrepared_ρ0 : (stationaryPrepared S ρβ hρβ).ρ0 = ρβ := rfl
@[simp] theorem stationaryPrepared_ρ (t : ℝ) : (stationaryPrepared S ρβ hρβ).ρ t = ρβ := rfl
@[simp] theorem stationaryPrepared_dyn : (stationaryPrepared S ρβ hρβ).dyn = S.dyn := rfl

end proj

/-- The Edgeworth hypotheses transfer to the stationary datum with `β₀ := S.β` (same `m`). -/
theorem stationaryPrepared_hE (S : PreparedData d) {β₀ m : ℝ} (hE : EdgeworthHyp S β₀ m)
    (ρβ : Torus d → ℝ) (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) :
    EdgeworthHyp (stationaryPrepared S ρβ hρβ) S.β m where
  s_lt := hE.s_lt
  m_gt := hE.m_gt
  β₀_nonneg := S.hβ.le
  β₀_pos := Or.inl S.hβ

section regime

variable (S : PreparedData d) {β₀ m : ℝ} (hE : EdgeworthHyp S β₀ m)
  (ρβ : Torus d → ℝ) (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ)

/-- The regime of the stationary datum (preparation temperature `S.β`). -/
abbrev stationaryRegime : Regime d :=
  regime (stationaryPrepared S ρβ hρβ) S.β (stationaryPrepared_hE S hE ρβ hρβ)

theorem stationaryRegime_ρ (t : ℝ) : (stationaryRegime S hE ρβ hρβ).ρ t = ρβ := rfl
theorem stationaryRegime_ρ_const : (stationaryRegime S hE ρβ hρβ).ρ = fun _ => ρβ := rfl
theorem stationaryRegime_ρ₀ : (stationaryRegime S hE ρβ hρβ).ρ₀ = ρβ := rfl
theorem stationaryRegime_β : (stationaryRegime S hE ρβ hρβ).β = S.β := rfl
theorem stationaryRegime_β₀ : (stationaryRegime S hE ρβ hρβ).β₀ = S.β := rfl
theorem stationaryRegime_D : (stationaryRegime S hE ρβ hρβ).D = S.dyn := rfl
/-- The dynamics of the stationary regime coincide with those of the prepared regime. -/
theorem stationaryRegime_D_eq :
    (stationaryRegime S hE ρβ hρβ).D = (regime S β₀ hE).D := rfl

include hρβ in
/-- Uniqueness of the thermal density: any thermal density of `(S.s, S.V, S.β)` is `ρβ` (so the stationary
regime's `ρβ` is the given one). -/
theorem thermal_eq_of_regime (ρ' : Torus d → ℝ)
    (hρ' : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρ') : ρ' = ρβ := by
  obtain ⟨hp, hs⟩ := Q41.q41_thermal_regular S.hd S.hs0 S.hsd S.hβ S.hV hρβ
  obtain ⟨hp', hs'⟩ := Q41.q41_thermal_regular S.hd S.hs0 S.hsd S.hβ S.hV hρ'
  exact PDE.MFThermal.thermal_unique S.hd S.s S.hs0 S.hsd S.β S.hβ S.V ρβ ρ' hρβ
    (HRS.StaticLimitAux.continuous_of_smooth hs) hp hρ' (HRS.StaticLimitAux.continuous_of_smooth hs') hp'

end regime

end HRS.MC.E214I

end
