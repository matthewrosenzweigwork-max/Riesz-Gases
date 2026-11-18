import HRS.MS.S113X2A3e

/-!
# S11.3 X2 part A3f: initial-time statements (absolute continuity and power moments of the localized initial ratios)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2

open HRS HRS.Whole

variable {d N : ℕ}

/-- At time `0` the killed law is dominated by `P∘X₀⁻¹`, hence absolutely continuous with respect to anything that
dominates the initial law. -/
theorem s113a_killedLaw_zero_ac {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s q β : ℝ}
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : MovParticleSetup P d s q β N X₀ W X) (D : Set (EucConfig d N))
    (chi : EucConfig d N → ℝ) (hchi1 : ∀ z, chi z ≤ 1) {Q : Measure (EucConfig d N)}
    (hinit : P.map X₀ ≪ Q) :
    s113a_killedLaw P D X₀ X chi 0 ≪ Q ∧ s113a_killedLaw P D X₀ X chi 0 ≤ P.map X₀ := by
  have hsol := hX.sol 0
  have h1 : P.map (X 0) = P.map X₀ := Measure.map_congr hsol.init
  have hle := s113a_killedLaw_le P D X₀ X chi hchi1 0 (hsol.adapted 0)
  rw [h1] at hle
  exact ⟨(Measure.absolutelyContinuous_of_le hle).trans hinit, hle⟩

/-- The `p`-th power moment of the localized ratio is dominated by that of the full ratio. -/
theorem s113a_power_moment_le {μ ν Q : Measure (EucConfig d N)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [SigmaFinite Q] (hle : ν ≤ μ) {p : ℝ} (hp : 0 ≤ p) :
    ∫⁻ x, ENNReal.ofReal ((ν.rnDeriv Q x).toReal ^ p) ∂Q ≤ ∫⁻ x, ENNReal.ofReal ((μ.rnDeriv Q x).toReal ^ p) ∂Q := by
  refine lintegral_mono_ae ?_
  filter_upwards [s113a_rnDeriv_mono (Q := Q) hle, Measure.rnDeriv_lt_top μ Q] with x h1 h2
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow ENNReal.toReal_nonneg (ENNReal.toReal_mono h2.ne h1) hp)

end HRS.MS.S113X2

end
