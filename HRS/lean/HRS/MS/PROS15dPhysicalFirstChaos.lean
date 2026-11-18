import HRS.MS.PROS15dActualGaussian
import HRS.MS.PROS15dTiltTransfer
import HRS.MS.S21T4ProdF

/-!
# R26-T3.S15d: arbitrary physical first-chaos observables are L4 Gaussian

The frozen ProductGaussian field supplies finite-dimensional centered Gaussian
laws for all L2 spatial tests. Consequently each physical first-chaos variable
has all finite moments under the original Gaussian law. Combined with the
second-exponential moment of a prospective Wick tilt, this yields L2
integrability under the tilted law for every spatial L2 test (not only spectral
tests).
-/

set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

theorem s15d_physical_first_chaos_L4
    {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    (I : ProductGaussian μ)
    (f : HRS.Euc d → ℝ) (hf : MemLp f 2 μ) :
    MemLp (I.η f) 4 I.P := by
  letI := I.mΩ
  letI := I.prob
  let X : I.Ω → (Fin 1 → ℝ) := fun ω _ => I.η f ω
  have hXm : AEMeasurable X I.P :=
    AEMeasurable.of_eval (fun _ => (I.meas f hf).aemeasurable)
  have hG : HRS.IsCenteredGaussian (HRS.law I.P X) := by
    simpa only [X] using
      I.gaussian 1 (fun _ : Fin 1 => f) (fun _ => hf)
  have hGL : HasGaussianLaw X I.P := ⟨hXm, hG.1⟩
  have hcoord : HasGaussianLaw (I.η f) I.P := by
    have h := hGL.map_fun (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 1 => ℝ) 0)
    simpa only [X, ContinuousLinearMap.proj_apply] using h
  exact hcoord.memLp (by norm_num)

theorem s15d_physical_first_chaos_tilt_L2
    {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    (I : ProductGaussian μ)
    (f : HRS.Euc d → ℝ) (hf : MemLp f 2 μ)
    (V : I.Ω → ℝ) (hV : AEMeasurable V I.P)
    (hExp1 : Integrable (fun ω => Real.exp (-V ω)) I.P)
    (hExp2 : Integrable (fun ω => Real.exp (-(2 * V ω))) I.P) :
    MemLp (I.η f) 2 (r26t3_tilt I.P V) := by
  letI := I.mΩ
  letI := I.prob
  exact s15d_L4_to_tilted_L2 hV hExp1 hExp2
    (s15d_physical_first_chaos_L4 I f hf)

end HRS.MS.R26T3
