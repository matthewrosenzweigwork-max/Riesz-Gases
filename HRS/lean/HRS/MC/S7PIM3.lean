import HRS.MC.S7FCF5EA

/-!
# Packet piM, M3: `s7_PIM_zeta_path_proof` (namespace `HRS.MC.Sec7.S7PIM`)

The statement is copied verbatim from `HRS/MC/S7PIPlan.lean` (`HRS.MC.Sec7.PIPlan.s7_PIM_zeta_path`); the tie is in
`HRS/MC/S7PIMTie.lean`.  The a.s. continuity of `t ↦ ζ_N^t` is `s7fcw12_zetaAt_continuousOn` (FC-E) on `[0,T]`, and the
measurability of the window is `S7FCF5E_aemeasurable_zetaWin` for the start `a = 0`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIM

open HRS HRS.Sec7 HRS.MC.Sec7

variable {d : ℕ}

section Prob

variable (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) (N : ℕ) (hN : 1 ≤ N)
  {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
  (hreal : PreparedRealization R.D P
    (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X)

include hm hT hN hreal

theorem s7_PIM_zeta_path_proof :
    (∀ᵐ ω ∂P, Continuous fun t : Set.Icc (0 : ℝ) T => zetaAt m P X t ω) ∧
    AEMeasurable (zetaWin m T 0 P X) P := by
  have hS := hreal.solution T
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hm2 : (d : ℝ) < 2 * m := by linarith
  have hN0 : 0 < N := hN
  refine ⟨?_, HRS.MC.Sec7.S7FCF5E.S7FCF5E_aemeasurable_zetaWin m T 0 hT hm2 P X hS.adapted hS.cont hN0⟩
  filter_upwards [hS.cont] with ω hω
  have h := HRS.MC.Sec7.S7FCW12.s7fcw12_zetaAt_continuousOn m hm2 P X hS.adapted hS.cont hN0 ω
    (fun i => (hω i).comp continuous_real_toNNReal) (Set.Icc (0 : ℝ) T)
  exact h.restrict

end Prob

end HRS.MC.Sec7.S7PIM

end
