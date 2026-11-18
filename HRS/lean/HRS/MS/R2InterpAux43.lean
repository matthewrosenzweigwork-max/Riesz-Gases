import HRS.MS.R2InterpAux42
import HRS.MC.S7PIG6A

/-!
# S10.2 (worker S102), part 43 (packet G6, vocabulary): the conclusion of the path interpolation for `Φ ∘ P`
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d : ℕ}

/-- The field `ζ_N^u = √N(μ_N^u - Eμ_N^u)` as a functional on test functions. -/
def s102_zf {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω) :
    ℝ → (Euc d → ℝ) → ℝ :=
  fun u f => Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical (X u.toNNReal ζ)) f -
    HRS.Whole.pair (HRS.Whole.meanEmpirical (P.map (X u.toNNReal))) f)

/-- The field `η_N^u = √N(μ_N^u - μ)` as a functional on test functions. -/
def s102_etaf {N : ℕ} {Ω : Type} (μ : Measure (Euc d)) (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω) :
    ℝ → (Euc d → ℝ) → ℝ :=
  fun u f => Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical (X u.toNNReal ζ)) f - HRS.Whole.pair μ f)

/-- The predicted path `Y_u = 𝖳_u ζ_N`. -/
def s102_Y (C : WholeCoeff d) (m T : ℝ) {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω) : ℝ → OscPath d m T :=
  fun τ => r2Predicted C (zetaPathW m T 0 P X ζ) (s102_zf P X ζ) τ

/-- The initial propagation `𝖨ζ_N^0`. -/
def s102_y0 (C : WholeCoeff d) (m T : ℝ) {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω) : OscPath d m T :=
  r2InitProp C m T (fun f => Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical (X 0 ζ)) f -
    HRS.Whole.pair (HRS.Whole.meanEmpirical (P.map (X 0))) f))

/-- The CONCLUSION of `r2_path_interpolation` for the functional `Φ ∘ P` (`P = id` gives the frozen conclusion). -/
def S102Concl (C : WholeCoeff d) (m T s : ℝ) (μ : Measure (Euc d)) (γ : ℝ → Measure (OscPath d m T))
    {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig d N)
    (Φ : OscPath d m T → ℝ) (Pj : OscPath d m T →L[ℝ] OscPath d m T) : Prop :=
  ∃ A J : Ω → ℝ, Integrable A P ∧ Integrable J P ∧
    (∀ᵐ ζ ∂P, IsR2RS T (fun τ a b => fderiv ℝ (r2HeatFn γ (fun w => Φ (Pj w)) τ) (s102_Y C m T P X ζ τ)
      (r2DriftInc C m T (fun u => r2QuadField s μ P X u ζ) a b)) (A ζ)) ∧
    (∀ᵐ ζ ∂P, IsR2RS T (fun τ a b => r2JPair C m T (s102_etaf μ X ζ) (Set.Ioc a b)
      (iteratedFDeriv ℝ 2 (r2HeatFn γ (fun w => Φ (Pj w)) τ) (s102_Y C m T P X ζ τ))) (J ζ)) ∧
    ∫ ζ, Φ (Pj (zetaPathW m T 0 P X ζ)) ∂P =
      ∫ ζ, r2HeatFn γ (fun w => Φ (Pj w)) 0 (s102_y0 C m T P X ζ) ∂P -
        (Real.sqrt N)⁻¹ * ∫ ζ, A ζ ∂P + (1 / (2 * Real.sqrt N)) * ∫ ζ, J ζ ∂P

end HRS.MS.R2Interp

end
