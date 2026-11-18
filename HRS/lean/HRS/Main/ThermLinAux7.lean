import HRS.Main.Headline
import HRS.Main.T25Aux1
import HRS.Sections.Q40bAux2
import HRS.Sections.Q41Aux14

/-!
# THERMLIN, part 7: regularity of the thermal density and relaxation `ρ^t → ρβ` (lemmas A1, A2 of `ThermLinAux6`)
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.ThermLin

variable {d : ℕ}

/-- A1: a thermal density of `(S.V, S.β)` is smooth and positive (so it is the unique smooth positive equilibrium,
`PDE.MFThermal.thermal_unique`). -/
theorem thermlin_thermal_smooth_pos (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) :
    Torus.IsSmooth ρβ ∧ ∀ x, 0 < ρβ x := by
  have hVc : Continuous S.V := HRS.StaticLimitAux.continuous_of_smooth S.hV
  obtain ⟨hpos, hcont⟩ := HRS.Q41.q41_thermal_pos_cont S.hd S.hs0 S.hsd S.hβ hVc h
  exact ⟨HRS.PDE.MFThermalAssembly.thermal_isSmooth_all (by have := S.hd; omega) S.s S.hs0 S.hsd S.V S.hV
    S.β S.hβ ρβ h hcont hpos, hpos⟩

/-- A1': uniqueness of the smooth positive thermal density. -/
theorem thermlin_thermal_unique (S : HRS.Main.PreparedData d) {ρβ ρβ' : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ)
    (h' : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ') : ρβ' = ρβ := by
  obtain ⟨hs, hp⟩ := thermlin_thermal_smooth_pos S h
  obtain ⟨hs', hp'⟩ := thermlin_thermal_smooth_pos S h'
  exact HRS.PDE.MFThermal.thermal_unique S.hd S.s S.hs0 S.hsd S.β S.hβ S.V ρβ ρβ' h
    (HRS.StaticLimitAux.continuous_of_smooth hs) hp h' (HRS.StaticLimitAux.continuous_of_smooth hs') hp'

/-- A2 (Prop. 5.1, `O:eq:finite-decay`, TeX L5781-5784): `‖ρ^t - ρβ‖_{H^r} ≤ C e^{-ct}`, for the coefficient solution of
the prepared data `S` (some `K > max(r, d/2+6)`). -/
theorem thermlin_rho_decay (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (r : ℝ) (hr : 0 ≤ r) :
    ∃ (K : ℕ) (ρc : ℝ → PDE.Coeff d) (C c : ℝ), 0 < C ∧ 0 < c ∧
      PDE.IsMFSolutionHK d S.s S.V S.β⁻¹ (K : ℝ) S.ρ0 ρc ∧ PDE.mfPath ρc = S.ρ ∧
      ∀ t : ℝ, 0 ≤ t → PDE.MemHs r (ρc t - PDE.coeffOf ρβ) ∧
        PDE.hsNorm r (ρc t - PDE.coeffOf ρβ) ≤ C * Real.exp (-c * t) := by
  obtain ⟨hsm, hpos⟩ := thermlin_thermal_smooth_pos S h
  have hd2 : 2 ≤ d := S.hd
  obtain ⟨K, hK⟩ : ∃ K : ℕ, max r ((d : ℝ) / 2 + 6) < K := exists_nat_gt _
  have hK6 : (d : ℝ) / 2 + 6 < K := lt_of_le_of_lt (le_max_right _ _) hK
  have hKr : r < K := lt_of_le_of_lt (le_max_left _ _) hK
  obtain ⟨ρc, hρc, hρ⟩ := S.hρ K hK6
  have htr := HRS.T25.t25_traj S
  have H := Q40b.q40b_finiteRegHyp htr hK6
  obtain ⟨C, c, hC, hc, hdec⟩ := PDE.finite_reg_decay (by omega) S.s S.β S.β K S.V S.ρ0 H r hr hKr
  refine ⟨K, ρc, C, c, hC, hc, hρc, hρ, fun t ht => ?_⟩
  exact hdec S.β ⟨le_rfl, le_rfl⟩ ρc hρc ρβ h (HRS.StaticLimitAux.continuous_of_smooth hsm) hpos
    (HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hsm K) t ht

end HRS.ThermLin
