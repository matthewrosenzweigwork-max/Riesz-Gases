import HRS.MS.R2InterpAux60

/-!
# S10.2 (worker S102), part 61 (packet F10): the conclusion of the path interpolation for a cylindrical functional `Φ ∘ P_L`

Inputs about the particle system (to be provided by the moment/Itô packets F5, M1-M3): the Itô-process representation of the observations
(`S102ItoRep`), the a.s. drift structure and the covariance paths, and measurability of the integrated densities.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators MatrixOrder Matrix

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIF6 HRS.MC.Sec7.S7PIG6

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}

/-- The Itô-process representation of the observations of the predicted path (packet F5). -/
def S102ItoRep (C : WholeCoeff d) (m T sQ : ℝ) (μ : Measure (Euc d)) (hT : 0 < T) (L : ℕ) {N : ℕ} {Ω : Type}
    {mΩ : MeasurableSpace Ω} (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig d N) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) : Prop :=
  ∃ (bd : ℝ → Ω → EuclideanSpace ℝ (Fin (s102_q d L)))
    (Φc : ℝ → Ω → (Fin N × Fin d) → EuclideanSpace ℝ (Fin (s102_q d L))),
    IsProgressiveLocL1 P ℱ bd ∧ IsProgressiveLocL2E P ℱ Φc ∧
    (∀ t : ℝ, Measurable[ℱ t] (fun ζ => s102_obs (s102_tauk hT L) (s102_alk L) (s102_y0 C m T P X ζ))) ∧
    (∀ u ζ i, 0 ≤ u → bd u ζ i = -(Real.sqrt N)⁻¹ *
      s102_hh C m (s102_tauk hT L) (s102_alk L) (fun v => r2QuadField sQ μ P X v ζ) i u) ∧
    (∀ u ζ k i, 0 ≤ u → Φc u ζ k i = s102_Phic C m hT L X u ζ k i) ∧
    ∀ᵐ ζ ∂P, ∀ u ∈ Icc (0 : ℝ) T, s102_obs (s102_tauk hT L) (s102_alk L) (s102_Y C m T P X ζ u) =
      itoProcess P ℱ W' (fun ζ => s102_obs (s102_tauk hT L) (s102_alk L) (s102_y0 C m T P X ζ)) bd Φc u ζ

end HRS.MS.R2Interp

end
