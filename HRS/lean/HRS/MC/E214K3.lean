import HRS.MC.E214K2
import HRS.MC.E213Final

/-!
# Packet E214K, part 3: `vprop_compare_Er_proof` (P2a, drift form of M3)
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214K

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final

variable {d : ℕ}

/-- The standing facts about the stationary density of the regime. -/
theorem regime_thermal (S : PreparedData d) (β₀ : ℝ) {m : ℝ} (hE : EdgeworthHyp S β₀ m) :
    IsThermalDensity (periodicRiesz d S.s) S.V S.β (regime S β₀ hE).ρβ :=
  (regime S β₀ hE).thermal.1

theorem rLvl_even_nat (d : ℕ) : ∃ j : ℕ, Even j ∧ (d : ℝ) / 2 + 4 < j ∧ rLvl d = (j : ℝ) := by
  refine ⟨2 * (d + 3), even_two_mul _, ?_, ?_⟩
  · push_cast
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  · unfold rLvl; push_cast; ring

/-- **P2a, drift form of M3.** -/
theorem vprop_compare_Er_proof {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} :
    ∃ C c κ : ℝ, 0 < C ∧ 0 < c ∧ 0 < κ ∧ ∀ u t : ℝ, 0 ≤ u → u ≤ t → ∀ F : NegSobolev d (rLvl d),
      ‖Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m t u (NegSobolev.embed m F) -
          Vprop (regime S β₀ hE).D (fun _ => (regime S β₀ hE).ρβ) m t u (NegSobolev.embed m F)‖ ≤
        C * Real.exp (-c * (t - u)) * Real.exp (-κ * u) * ‖F‖ := by
  have hth := regime_thermal S β₀ hE
  obtain ⟨j, hj, hjd, hjr⟩ := rLvl_even_nat d
  obtain ⟨C, c, κ, hC, hc, hκ, hcmp⟩ := compare_level_at S hth (rLvl d) j hj hjd hjr
  obtain ⟨VR, Wc, hVR, hWc⟩ := exists_dual S hth (rLvl d)
  refine ⟨C, c, κ, hC, hc, hκ, fun u t hu hut F => ?_⟩
  have hrm : rLvl d ≤ m := rLvl_le hE
  have h1 := vprop_embed hrm S.dyn S.ρ VR hVR hu hut F
  have h2 := vprop_embed hrm S.dyn (fun _ => (regime S β₀ hE).ρβ) Wc hWc hu hut F
  show ‖Vprop S.dyn S.ρ m t u (NegSobolev.embed m F) -
      Vprop S.dyn (fun _ => (regime S β₀ hE).ρβ) m t u (NegSobolev.embed m F)‖ ≤ _
  rw [h1, h2, ← HRS.MD.EQGaussLift.eqgl_embed_sub hrm]
  refine (NegSobolev.norm_embed_le m hrm _).trans ?_
  have h3 := hcmp u t hu hut VR Wc hVR hWc
  calc ‖VR t u F - Wc t u F‖ = ‖(VR t u - Wc t u) F‖ := by rw [sub_apply]
    _ ≤ ‖VR t u - Wc t u‖ * ‖F‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)

end HRS.MC.E214K

end
