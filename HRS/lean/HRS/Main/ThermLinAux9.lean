import HRS.Main.ThermLinAux7
import HRS.PDE.MeanFieldAdjointWiring

/-!
# THERMLIN, part 9: the coefficient-level Dyson/Duhamel identity for the data `S` (first step of N1)

`PDE.MFAdjoint.duhamel_coeff` instantiated for the prepared data `S` and the thermal density `ρβ`: all its hypotheses
(`AdjointData` along `S.ρ`, `AdjointData` for the frozen path `ρβ`, `0 < β⁻¹`) are discharged from `S`.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.ThermLin

variable {d : ℕ}

open HRS.PDE HRS.PDE.MFAdjoint in
/-- N1a: `U^{u,t}φ`-coefficients equal the frozen part plus the Duhamel integral (TeX `P:eq:Gaussian-difference`
on tests), for natural `j > d/2+4`, `0 < t`, `τ ∈ [0,t]` (`τ = t - u`). -/
theorem thermlin_dyson_coeff (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (j : ℕ) (hj : (d : ℝ) / 2 + 4 < j) :
    ∀ (φc : Coeff d), MemHs (j : ℝ) φc → ∀ t : ℝ, 0 < t → ∀ τ ∈ Set.Icc (0 : ℝ) t, ∀ k : Lattice d,
      propagatorCoeff S.dyn S.ρ j t φc τ k = frozenCoeff S.dyn ρβ (j - 2) φc τ k +
        ∫ σ in (0 : ℝ)..τ, frozenCoeff S.dyn ρβ (j - 2)
          (forwardGen S.dyn (S.ρ (t - σ)) (propagatorCoeff S.dyn S.ρ j t φc σ) -
            forwardGen S.dyn ρβ (propagatorCoeff S.dyn S.ρ j t φc σ)) (τ - σ) k := by
  obtain ⟨hsm, hpos⟩ := thermlin_thermal_smooth_pos S h
  have hd2 : 2 ≤ d := S.hd
  have htr := HRS.T25.t25_traj S
  obtain ⟨K, hK⟩ : ∃ K : ℕ, 2 * j + 4 * d + 20 ≤ K := ⟨2 * j + 4 * d + 20, le_rfl⟩
  have hK6 : (d : ℝ) / 2 + 6 < K := by
    have : ((2 * j + 4 * d + 20 : ℕ) : ℝ) ≤ K := by exact_mod_cast hK
    push_cast at this
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨ρc, hρc, hρ⟩ := S.hρ K hK6
  have H := Q40b.q40b_finiteRegHyp htr hK6
  obtain ⟨R, Λ, Λ₀, c₀, Cd, κ, hc₀, hκ, hall⟩ :=
    finiteReg_hypotheses (by omega) S.s S.β S.β K S.V S.ρ0 H j hj hK
  obtain ⟨HF, hAD, -⟩ := hall S.β ⟨le_rfl, le_rfl⟩ ρc hρc ρβ h
    (HRS.StaticLimitAux.continuous_of_smooth hsm) hpos
  intro φc hφ t ht τ hτ k
  have hAt := hAD t ht
  have h3 := ClassicalPart.three_le_mStar d
  have hj3 : 3 ≤ j := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    have : (4 : ℝ) < j := by linarith
    have : 4 < j := by exact_mod_cast this
    omega
  have hAβ := adjointData_frozen_level j (HF.mono (by omega : j + 3 ≤ j + mStar d + 2)) 0 t ht
  have := duhamel_coeff (by omega) S.s S.hs0 S.hsd j hj3 R (frozenRegime d S.s c₀) 1 Λ (Torus.cbNorm (j + 3) S.V)
    1 Λ₀ Λ₀ (mfData d S.s S.hs0 S.hsd S.V S.β S.hβ) S.β⁻¹ 0 t (mfPath ρc) ρβ hAt hAβ
    (inv_pos.2 S.hβ) φc hφ ⟨ht, le_rfl⟩ k hτ
  rw [hρ] at this
  exact this

end HRS.ThermLin
