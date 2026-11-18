import HRS.MC.S7FCF5JB
import HRS.MC.S7FCF5E
import HRS.MC.S7FCF5Defs

/-!
# Packet fcf5n: proof of F6c (`fcf5_F6c_B_moments`), the assembly of F6b and G1

`fcf5_F6c_B_moments_proof`: the statement of `HRS.MC.Sec7.FCF5Plan.fcf5_F6c_B_moments` (copied verbatim, checked in
`HRS/MC/S7FCF5NTie.lean`), proved from

* `HRS.MC.Sec7.S7FCF5J.fcf5_F6b_toL2_moment_proof` (the uniform `L^q` bound, lintegral form), and
* `HRS.MC.Sec7.S7FCF5E.fcf5_G1_pair_aemeasurable_proof` (`AEMeasurable` of the particle pair for every `a ≥ 0`).

`Integrable` = `AEStronglyMeasurable` (from G1 and `measurable_snd`) + finite lintegral (F6b); the Bochner integral is the
`toReal` of the lintegral, bounded by `max C0 0`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCF5N

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.FCF5Plan

variable {d : ℕ}

theorem fcf5_F6c_B_moments_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T) (q : ℝ)
    (hq : 1 ≤ q) :
    ∃ C : ℝ, ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        PreparedRealization R.D P (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀))
          X₀ W X →
        Integrable (fun ω => ‖(pairN r T a R.D.s R.ρ P X ω).2‖ ^ q) P ∧
          ∫ ω, ‖(pairN r T a R.D.s R.ρ P X ω).2‖ ^ q ∂P ≤ C := by
  have hq0 : (0 : ℝ) ≤ q := by linarith
  obtain ⟨C0, hC0⟩ := HRS.MC.Sec7.S7FCF5J.fcf5_F6b_toL2_moment_proof R r hr T hT q hq
  refine ⟨max C0 0, ?_⟩
  intro a ha N hN Ω _ P _ X₀ W X hprep
  have hN1 : 1 ≤ N := by omega
  have hreal : FCPrepared R P X₀ W X := hprep
  -- measurability of the integrand (G1 and `measurable_snd`)
  have hmeas : AEMeasurable (fun ω => ‖(pairN r T a R.D.s R.ρ P X ω).2‖ ^ q) P :=
    ((HRS.MC.Sec7.S7FCF5E.fcf5_G1_pair_aemeasurable_proof R r hr T hT P hN1 X₀ W X hreal a ha).snd.norm).pow_const q
  have hnn : 0 ≤ᵐ[P] fun ω => ‖(pairN r T a R.D.s R.ρ P X ω).2‖ ^ q :=
    Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (norm_nonneg _) _
  -- the lintegral of the nonnegative real integrand is the F6b lintegral
  have hl : ∫⁻ ω, ENNReal.ofReal (‖(pairN r T a R.D.s R.ρ P X ω).2‖ ^ q) ∂P ≤ ENNReal.ofReal C0 := by
    refine le_trans (le_of_eq ?_) (hC0 a ha N hN P X₀ W X hreal)
    apply lintegral_congr
    intro ω
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq0]
  have hfin : HasFiniteIntegral (fun ω => ‖(pairN r T a R.D.s R.ρ P X ω).2‖ ^ q) P := by
    rw [hasFiniteIntegral_iff_ofReal hnn]
    exact lt_of_le_of_lt hl ENNReal.ofReal_lt_top
  refine ⟨⟨hmeas.aestronglyMeasurable, hfin⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas.aestronglyMeasurable]
  apply ENNReal.toReal_le_of_le_ofReal (le_max_right _ _)
  exact le_trans hl (ENNReal.ofReal_le_ofReal (le_max_left _ _))

end HRS.MC.Sec7.S7FCF5N

end
