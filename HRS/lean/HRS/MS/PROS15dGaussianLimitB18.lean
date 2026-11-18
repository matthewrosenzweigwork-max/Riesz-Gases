import HRS.MS.S111BDAux2
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# R26-T3.S15d: Gaussianity survives finite-dimensional L² approximation

This removes a topology/regularity gap in the arbitrary-test extension:
the limit need not have a separately assumed Gaussian law. The conclusion
concerns the actual law under the same fixed probability measure.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MS.R26T3

theorem s15d_centered_gaussian_in_measure_limit
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [CompleteSpace B] [MeasurableSpace B] [BorelSpace B]
    [SecondCountableTopology B]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℕ → Ω → B) (Y : Ω → B)
    (hXm : ∀ n, AEStronglyMeasurable (X n) P)
    (hX : ∀ n, HRS.IsCenteredGaussian (P.map (X n)))
    (hconv : TendstoInMeasure P X atTop Y) :
    HRS.IsCenteredGaussian (P.map Y) := by
  obtain ⟨ns, _, hlim⟩ := hconv.exists_seq_tendsto_ae
  exact HRS.MS.S111BD.s111_centered_gaussian_ae_limit P
    (fun n => X (ns n)) Y
    (fun n => (hXm (ns n)).aemeasurable)
    (hconv.aemeasurable (fun n => (hXm n).aemeasurable)) (fun n => hX (ns n)) hlim

theorem s15d_centered_gaussian_L2_limit
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [CompleteSpace B] [MeasurableSpace B] [BorelSpace B]
    [SecondCountableTopology B]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℕ → Ω → B) (Y : Ω → B)
    (hXm : ∀ n, AEStronglyMeasurable (X n) P)
    (hX : ∀ n, HRS.IsCenteredGaussian (P.map (X n)))
    (hL2 : Tendsto (fun n => eLpNorm (X n - Y) 2 P) atTop (𝓝 0)) :
    HRS.IsCenteredGaussian (P.map Y) := by
  exact s15d_centered_gaussian_in_measure_limit P X Y hXm hX
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hL2)

#print axioms s15d_centered_gaussian_in_measure_limit
#print axioms s15d_centered_gaussian_L2_limit

end HRS.MS.R26T3
