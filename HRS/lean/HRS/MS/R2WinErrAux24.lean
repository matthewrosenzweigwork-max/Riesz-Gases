import HRS.MS.R2WinErrAux23
import HRS.MS.R2WinErrTie

/-!
# S10.4 input `hdyn` for the stationary trajectory (assembly)

`s104_hdyn_stat`: `S104RealInput d s a β T (fun _ => ρβ) N P X b C₀` for a realization `hreal : IsR2Realization` and a thermal equilibrium `ρβ`
(the stationary trajectory `ρ = fun _ => ρβ`), from `s104_hevol_stat` and `s104_M0_stat/M1_stat/M2_stat` (`hreal.filtered` gives the
progressive measurability of `X`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinErr

open HRS HRS.Whole HRS.MS.S53

variable {d : ℕ}

theorem s104_hdyn_stat (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {T : ℝ} (hT : 0 ≤ T) {ρβ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρβ) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hreal : IsR2Realization d s a β P X₀ W X) {b : ℝ} (hb : 0 ≤ b) (C₀ : ℝ) :
    S104RealInput d s a β T (fun _ => ρβ) N P X b C₀ := by
  obtain ⟨ℱ, W', hfilt⟩ := hreal.filtered
  have hprog := hfilt.progressive
  have hT0 : 0 ≤ b + T := by linarith
  have hprob : HRS.Whole.IsProbDensity ρβ := hρ.2.1
  have hρeq : ρβ = thermalDensity d s a β := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ
  obtain ⟨Mρ, ctx⟩ := s53_ctx_of_schwartz hd hs0 hsd (hρeq ▸ HRS.MS.S21.s21_schwartz_thermal hd hs0 hsd ha hβ)
  have hNpos : 0 < N := by omega
  have horb := fun α : MultiIndex d => s104_stat_orbit hd hs0 hsd ha hβ hρ α hT0
  choose G0 G1 G2 hG using horb
  refine ⟨fun ζ α r t0 t hr0 hrt0 ht0t htT => ?_, fun α => ?_, fun α => ?_, fun α => ?_⟩
  · exact s104_hevol_stat hd hs0 hsd ha hβ hρ α hNpos (hG α) ctx X ζ hr0 hrt0 ht0t htT
  · exact s104_M0_stat hd hs0 hsd ha hβ hρ α hT0 P ℱ X hprog (hG α) hprob hb (by linarith)
  · exact s104_M1_stat hd hs0 hsd ha hβ hρ α hT0 P ℱ X hprog (hG α) hprob hb (by linarith)
  · exact s104_M2_stat hd hs0 hsd ha hβ hρ α hT0 P ℱ X hprog (hG α) hprob hb (by linarith)

end HRS.MS.R2WinErr
