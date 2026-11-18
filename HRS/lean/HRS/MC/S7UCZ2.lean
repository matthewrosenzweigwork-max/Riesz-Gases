import HRS.MC.S7UCZ
import HRS.MC.S7UCAC
import HRS.MC.S7UCU

/-!
# Packet ucZ (part 2): the assembly `s7_UC_uniform_chaos` (verbatim `HRS.Sec7.uniform_chaos`)

Conjunct 1 is `s7_UC_D_unif_proof` at `T := Rw`; for conjunct 2, `B` comes from `s7_UC_C_field_proof`, the first three
components of `UCField` give joint measurability, the Wick property and the `MemLp` on every window, and the `Tendsto` is
`s7_UC_Wq_every_B_proof` at `T := Rw`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7UCZ

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.S7FCH4
open HRS.MC.Sec7.UCPlan

variable {d : ℕ}

theorem s7_UC_uniform_chaos_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6)
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → Config d N)
    (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hreal : ∀ N, 1 ≤ N → PreparedRealization R.D (P N)
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) (X₀ N) (W N) (X N))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η : ℝ → Ω' → NegSobolev d r)
    (hη : IsGaussianLimitField R.D R.ρ (withDensityReal R.ρ₀) R.β₀ r P' η) :
    (∀ Rw : ℝ, 0 < Rw → ∀ p : ℝ, 1 ≤ p →
      Tendsto (fun N : ℕ => ⨆ a : {a : ℝ // 0 ≤ a},
          wassersteinE p (law (P N) (zetaWin r Rw a.1 (P N) (X N))) (law P' (procWin r Rw a.1 η)))
        atTop (𝓝 0)) ∧
    ∃ B : ℝ → Ω' → NegSobolev d r, Measurable (Function.uncurry B) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Ici (0 : ℝ))),
        IsWickQuadraticField R.D.s P' (fun ω => η t ω) (withDensityReal (R.ρ t)) (B t)) ∧
      ∀ Rw : ℝ, 0 < Rw → ∀ p : ℝ, 1 ≤ p →
        (∀ a : ℝ, 0 ≤ a → ∀ᵐ ω ∂P', MemLp (fun t => B (a + t) ω) 2 (volume.restrict (Set.Icc (0 : ℝ) Rw))) ∧
        Tendsto (fun N : ℕ => ⨆ a : {a : ℝ // 0 ≤ a},
            wassersteinE p (law (P N) (pairN r Rw a.1 R.D.s R.ρ (P N) (X N)))
              (law P' (pairLim r Rw a.1 η B))) atTop (𝓝 0) := by
  refine ⟨fun Rw hRw p hp => HRS.MC.Sec7.S7UCU.s7_UC_D_unif_proof R r hr Rw hRw P X₀ W X hreal P' η hη p hp, ?_⟩
  obtain ⟨B, hB⟩ := HRS.MC.Sec7.S7UCA.s7_UC_C_field_proof R r hr P' η hη
  refine ⟨B, hB.1, hB.2.1, fun Rw hRw p hp => ⟨fun a ha => hB.2.2 Rw hRw a ha, ?_⟩⟩
  exact s7_UC_Wq_every_B_proof R r hr Rw hRw P X₀ W X hreal P' η hη B hB p hp

end HRS.MC.Sec7.S7UCZ

end
