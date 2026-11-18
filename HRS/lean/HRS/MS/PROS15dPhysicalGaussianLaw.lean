import HRS.MS.PROS15dPhysicalFirstChaos
import HRS.MS.LcKolmAux2

/-!
# R26-T3.S15d: the exact centered Gaussian law of every physical observable

The frozen ProductGaussian field makes every physical spatial L2 observable
a centered Gaussian variable, without restricting to compactly supported
smooth tests or spectral eigenfunctions.
-/

set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem s15d_physical_centered_gaussian_law
    {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    (I : ProductGaussian μ)
    (f : HRS.Euc d → ℝ) (hf : MemLp f 2 μ) :
    ∃ v : ℝ≥0, I.P.map (I.η f) = gaussianReal 0 v := by
  letI := I.mΩ
  letI := I.prob
  let X : I.Ω → (Fin 1 → ℝ) := fun ω _ => I.η f ω
  have hXm : AEMeasurable X I.P :=
    AEMeasurable.of_eval (fun _ => (I.meas f hf).aemeasurable)
  have hG : HRS.IsCenteredGaussian (I.P.map X) := by
    simpa only [HRS.law, X] using
      I.gaussian 1 (fun _ : Fin 1 => f) (fun _ => hf)
  let A : (Fin 1 → ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0
  have hA : (I.P.map X).map A = I.P.map (I.η f) := by
    rw [AEMeasurable.map_map_of_aemeasurable A.continuous.measurable.aemeasurable hXm]
    rfl
  have hCL : HasGaussianLaw (I.η f) I.P := by
    have hP : HasGaussianLaw X I.P := ⟨hXm, hG.1⟩
    have h := hP.map_fun A
    simpa only [A, X, ContinuousLinearMap.proj_apply] using h
  have hzero : ∫ x : ℝ, x ∂(I.P.map (I.η f)) = 0 := by
    calc
      ∫ x : ℝ, x ∂(I.P.map (I.η f)) =
          ∫ x : ℝ, x ∂((I.P.map X).map A) := by rw [hA]
      _ = ∫ x : Fin 1 → ℝ, A x ∂(I.P.map X) := by
        exact integral_map A.continuous.measurable.aemeasurable aestronglyMeasurable_id
      _ = 0 := hG.2 A
  have hmean : ∫ ω, I.η f ω ∂I.P = 0 := by
    have hm := integral_map (μ := I.P) (φ := I.η f) (f := fun x : ℝ => x)
      (I.meas f hf).aemeasurable aestronglyMeasurable_id
    exact hm.symm.trans hzero
  refine ⟨Var[I.η f; I.P].toNNReal, ?_⟩
  calc
    I.P.map (I.η f) = gaussianReal (∫ ω, I.η f ω ∂I.P) Var[I.η f; I.P].toNNReal :=
      hCL.map_eq_gaussianReal
    _ = gaussianReal 0 _ := by rw [hmean]

end HRS.MS.R26T3
