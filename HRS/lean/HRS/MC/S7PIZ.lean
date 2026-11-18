import HRS.MC.S7PIG6
import HRS.MC.S7PIF10F
import HRS.Sections.Q17Aux8

/-!
# Row 7.11, final assembly: `path_Ito_proof` (namespace `HRS.MC.Sec7.S7PIZ`)

Statement copied verbatim from `HRS.Sec7.path_Ito` (`HRS/Sections/Sec7Fields.lean:390`).  Proof as in
`HRS.MC.Sec7.PIPlan.s7_path_Ito_assembly`: `projection_strong_proof` supplies the polynomial projections `Pj`; the projected
identity `s7_PI_F_projected_identity_assembly_proof` (F11) holds for every `Pj L`; `s7_PI_G_remove_projection_proof` (G6) passes
to the limit `L → ∞`.  This module imports no sorried module; the tie to `HRS.Sec7.path_Ito` is in `HRS/MC/S7PIZTie.lean`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIZ

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

theorem path_Ito_proof (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (γ : ℝ → Measure (PathSpace d m T))
    (hγ : ∀ u ∈ Set.Icc (0 : ℝ) T, IsFutureGaussian R.D R.ρ m T u (γ u))
    (N : ℕ) (hN : 1 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hreal : PreparedRealization R.D P
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X)
    (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) :
    ∃ A J : Ω → ℝ, Integrable A P ∧ Integrable J P ∧
      (∀ᵐ ω ∂P, IsRS T (fun τ a b =>
        fderiv ℝ (heatFn γ Φ τ) (predicted R.D R.ρ (zetaWin m T 0 P X ω) τ)
          (driftInc R.D R.ρ m T
            (fun u => quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X u ω) a b)) (A ω)) ∧
      (∀ᵐ ω ∂P, IsRS T (fun τ a b =>
        jPair R.D R.ρ m T (fun u => etaE m (X u.toNNReal ω) (withDensityReal (R.ρ u))) (Set.Ioc a b)
          (iteratedFDeriv ℝ 2 (heatFn γ Φ τ) (predicted R.D R.ρ (zetaWin m T 0 P X ω) τ))) (J ω)) ∧
      ∫ ω, Φ (zetaWin m T 0 P X ω) ∂P =
        ∫ ω, heatFn γ Φ 0 (initProp R.D R.ρ m T (zetaAt m P X 0 ω)) ∂P -
          (Real.sqrt N)⁻¹ * ∫ ω, A ω ∂P + (1 / (2 * Real.sqrt N)) * ∫ ω, J ω ∂P := by
  obtain ⟨Pj, hPj, hP1, hconv, hTconv⟩ := projection_strong_proof (d := d) m T hT
  exact HRS.MC.Sec7.S7PIG6.s7_PI_G_remove_projection_proof R m hm T hT γ hγ N hN P X₀ W X hreal Pj hPj hP1 hconv hTconv Φ hΦ
    (fun L => HRS.MC.Sec7.S7PIF10.s7_PI_F_projected_identity_assembly_proof R m hm T hT γ hγ N hN P X₀ W X hreal Pj hPj Φ hΦ L)

end HRS.MC.Sec7.S7PIZ

end
