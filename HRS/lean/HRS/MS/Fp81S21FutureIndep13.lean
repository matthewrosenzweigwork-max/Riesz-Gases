import HRS.MS.Fp81S21FutureIndep6
import HRS.MS.R2InterpAux5

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS.MS.R26T3

/-- Finite observations of the retained source have exactly the Gaussian
Gram law, including singular covariance matrices. -/
theorem fp81s21_source_finite_law {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : E → Ω → ℝ)
    (hWm : ∀ h, Measurable (W h))
    (hcomb : ∀ (n : ℕ) (c : Fin n → ℝ) (f : Fin n → E),
      P.map (fun ω => ∑ i, c i * W (f i) ω) =
        gaussianReal 0 (Real.toNNReal (‖∑ i, c i • f i‖ ^ 2)))
    (hcov : ∀ h h', ∫ ω, W h ω * W h' ω ∂P = inner ℝ h h')
    (n : ℕ) (f : Fin n → E) :
    P.map (fun ω => (WithLp.toLp 2 fun i => W (f i) ω : EuclideanSpace ℝ (Fin n))) =
      multivariateGaussian 0 (Matrix.of fun i j => inner ℝ (f i) (f j)) := by
  let Z : Ω → (Fin n → ℝ) := fun ω i => W (f i) ω
  have hZm : Measurable Z := measurable_pi_iff.2 fun i => hWm (f i)
  have hZg : HRS.IsCenteredGaussian (P.map Z) :=
    s21g2_s11a_gauss_of_laws hZm.aemeasurable fun c => ⟨_, hcomb n c f⟩
  letI : IsGaussian (P.map Z) := hZg.1
  let O : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap
  have hS : ∀ i j, (Matrix.of fun i j => inner ℝ (f i) (f j)) i j =
      ∫ z, O z i * O z j ∂(P.map Z) := by
    intro i j
    rw [integral_map hZm.aemeasurable]
    · simpa [O, Z] using (hcov (f i) (f j)).symm
    · exact (((EuclideanSpace.proj i).continuous.comp O.continuous).mul
      ((EuclideanSpace.proj j).continuous.comp O.continuous)).aestronglyMeasurable
  have hlaw := (HRS.MC.Sec7.S7PIS3.S7PIS3_map_eq hZg.2 O _ hS).2
  rw [Measure.map_map O.continuous.measurable hZm] at hlaw
  simpa [O, Z, Function.comp_def] using hlaw

#print axioms fp81s21_source_finite_law

end HRS.Fp81.S21
end
