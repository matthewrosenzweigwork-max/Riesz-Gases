import HRS.MC.S7FCHA4
import HRS.MC.S7FCW15

/-!
# S7FCZ: relocated proof of `field_chaos` (Proposition 7.6)

`field_chaos_proof` has the statement of `HRS.Sec7.field_chaos` (`HRS/Sections/Sec7Fields.lean`) verbatim; the tie is in
`HRS/MC/S7FCZTie.lean`.  Route: the field `B` of FC-C (`s7_FC_C_limit_field_proof`, from C4: jointly measurable, a.s.
`L²_t`, Wick-centred quadratic field of `η^t` for a.e. `t ∈ [0,T]`) and then the assembly FC-H for this `B`
(`s7_FC_H_every_B_proof`: weak convergence and `W_q` convergence for every `q ≥ 1`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCZ

variable {d : ℕ}

section Fields

variable (R : Regime d)

/-- Proof of `HRS.Sec7.field_chaos` (statement verbatim). -/
theorem field_chaos_proof (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T)
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → Config d N)
    (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hreal : ∀ N, 1 ≤ N → PreparedRealization R.D (P N)
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) (X₀ N) (W N) (X N))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η : ℝ → Ω' → NegSobolev d r)
    (hη : IsGaussianLimitField R.D R.ρ (withDensityReal R.ρ₀) R.β₀ r P' η) :
    ∃ B : ℝ → Ω' → NegSobolev d r, Measurable (Function.uncurry B) ∧
      (∀ᵐ ω ∂P', MemLp (fun t => B t ω) 2 (volume.restrict (Set.Icc (0 : ℝ) T))) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
        IsWickQuadraticField R.D.s P' (fun ω => η t ω) (withDensityReal (R.ρ t)) (B t)) ∧
      (∀ G : PathSpace d r T × L2Path d r T → ℝ, Continuous G → (∃ M, ∀ z, |G z| ≤ M) →
        Tendsto (fun N : ℕ => ∫ ω, G (pairN r T 0 R.D.s R.ρ (P N) (X N) ω) ∂(P N)) atTop
          (𝓝 (∫ ω, G (pairLim r T 0 η B ω) ∂P'))) ∧
      (∀ q : ℝ, 1 ≤ q →
        Tendsto (fun N : ℕ => wassersteinE q (law (P N) (pairN r T 0 R.D.s R.ρ (P N) (X N)))
            (law P' (pairLim r T 0 η B))) atTop (𝓝 0)) := by
  obtain ⟨B, hBm, hBL2, hBW⟩ := HRS.MC.Sec7.S7FCW15.s7_FC_C_limit_field_proof R r hr T hT P' η hη
  exact ⟨B, hBm, hBL2, hBW, HRS.MC.Sec7.S7FCH.s7_FC_H_every_B_proof R r hr T hT P X₀ W X hreal P' η hη B hBm
    hBL2 hBW⟩

end Fields

end HRS.MC.Sec7.S7FCZ

end
