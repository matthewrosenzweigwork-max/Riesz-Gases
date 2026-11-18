import HRS.MC.E214PD
import HRS.MC.E214I
import HRS.MC.E214G6

/-!
# Packet E214L, part 1: `exists_statDatum`, `exists_pairGD`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214L

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E214Plan

variable {d : ℕ}

section PairEstimates

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m}

theorem exists_statDatum_proof (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) : Nonempty (StatDatum S β₀ m hE) := by
  have h := HRS.MC.E214I.thermal_eq_of_regime S ρβ hρβ _ (regime S β₀ hE).thermal.1
  refine ⟨⟨HRS.MC.E214I.stationaryPrepared S ρβ hρβ, HRS.MC.E214I.stationaryPrepared_hE S hE ρβ hρβ,
    rfl, ?_, ?_⟩⟩
  · rw [HRS.MC.E214I.stationaryRegime_ρ_const S hE ρβ hρβ, h]
  · rw [HRS.MC.E214I.stationaryRegime_ρ₀ S hE ρβ hρβ, h]

theorem exists_pairGD_proof (sd : StatDatum S β₀ m hE) : Nonempty (PairGD sd) := by
  set R := regime S β₀ hE with hR
  obtain ⟨Ω, mΩ, P, hP, Y₀, Ys₀, η, ηs, hpair, hps⟩ :=
    HRS.MC.E214G.p4_pair_proof R (rLvl d) rfl
  choose Ωn mΩn Pn hPn X₀n Wn Xn hreal using HRS.MC.E213U4.u4_exists_realizations R
  set Rs := regime sd.Ss S.β sd.hEs with hRs
  choose Ωs mΩs Ps hPs X₀s Ws Xs hreals using HRS.MC.E213U4.u4_exists_realizations Rs
  have hη : IsGaussianLimitField R.D R.ρ (withDensityReal R.ρ₀) R.β₀ (rLvl d) P η :=
    ⟨Y₀, hpair.1, hpair.2.2.2.1⟩
  have hηs : IsGaussianLimitField Rs.D Rs.ρ (withDensityReal Rs.ρ₀) Rs.β₀ (rLvl d) P ηs := by
    refine ⟨Ys₀, ?_, ?_⟩
    · have h2 := hpair.2.1
      rw [← sd.hD, ← sd.hρ₀] at h2
      exact h2
    · have h5 := hpair.2.2.2.2.1
      intro T
      have h5T := h5 T
      rw [← sd.hD, ← sd.hρ] at h5T
      exact h5T
  obtain ⟨-, B, hBm, hBw, hBL⟩ :=
    HRS.MC.Sec7.S7UCZ.s7_UC_uniform_chaos_proof R (rLvl d) rfl Pn X₀n Wn Xn hreal P η hη
  obtain ⟨-, Bs, hBsm, hBsw, hBsL⟩ :=
    HRS.MC.Sec7.S7UCZ.s7_UC_uniform_chaos_proof Rs (rLvl d) rfl Ps X₀s Ws Xs hreals P ηs hηs
  refine ⟨{ Ω := Ω, mΩ := mΩ, P := P, pP := hP, Y₀ := Y₀, Ys₀ := Ys₀, η := η, ηs := ηs, B := B, Bs := Bs,
            pair := hpair, limit_s := hηs, B_meas := hBm, B_wick := hBw, B_L2 := ?_,
            Bs_meas := hBsm, Bs_wick := hBsw, Bs_L2 := ?_, path_sup := ?_ }⟩
  · intro Rw hRw a ha
    exact (hBL Rw hRw 1 le_rfl).1 a ha
  · intro Rw hRw a ha
    exact (hBsL Rw hRw 1 le_rfl).1 a ha
  · intro T hT p hp
    exact hps hT hp

end PairEstimates

end HRS.MC.E214L

end
