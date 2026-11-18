import HRS.MS.R2InterpAux56
import HRS.MS.R2InterpAux8
import HRS.MC.S7PIF6D
import HRS.MC.S7PIF6B
import HRS.Stochastic.Ito

/-!
# S10.2 (worker S102), part 57 (packet F6, drift identification): the Itô drift of the extension on a piece is `-N^{-1/2} cylA + (2√N)^{-1} cylJ`
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators MatrixOrder Matrix

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIF6

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}

theorem s102_drift_pt (hT : 0 < T) (L : ℕ) (u0 : ℝ) (N : ℕ)
    (G : EuclideanSpace ℝ (Fin (s102_q d L)) → ℝ)
    (f : ℝ → EuclideanSpace ℝ (Fin (s102_q d L)) → ℝ)
    (hfeq : f u0 = gaussHeat (s102_obsCov C m (s102_tauk hT L) (s102_alk L)) G u0)
    (hfd : ∀ c, derivWithin (fun s' => f s' c) (Icc 0 T) u0 =
      -(1 / 2) * ∑ i, ∑ j, s102_rateM C m hT L u0 i j *
        iteratedFDeriv ℝ 2 (gaussHeat (s102_obsCov C m (s102_tauk hT L) (s102_alk L)) G u0) c
          ![EuclideanSpace.single i 1, EuclideanSpace.single j 1])
    {Ω' : Type} {mΩ : MeasurableSpace Ω'} {ι : Type} [Fintype ι]
    (Z : ℝ → Ω' → EuclideanSpace ℝ (Fin (s102_q d L))) (ω : Ω')
    (bd : ℝ → Ω' → EuclideanSpace ℝ (Fin (s102_q d L)))
    (Φc : ℝ → Ω' → ι → EuclideanSpace ℝ (Fin (s102_q d L)))
    (bfield eta : ℝ → (Euc d → ℝ) → ℝ)
    (hbd : ∀ i, bd u0 ω i = -(Real.sqrt N)⁻¹ * s102_hh C m (s102_tauk hT L) (s102_alk L) bfield i u0)
    (hbr : ∀ i j, ∑ k, Φc u0 ω k i * Φc u0 ω k j = s102_rateM C m hT L u0 i j +
      (Real.sqrt N)⁻¹ * (2 * C.ν * s102_hh2 C m (s102_tauk hT L) (s102_alk L) eta i j u0)) :
    itoDrift T f Z bd Φc u0 ω =
      -(Real.sqrt N)⁻¹ * ∑ i, fderiv ℝ (gaussHeat (s102_obsCov C m (s102_tauk hT L) (s102_alk L)) G u0) (Z u0 ω)
          (EuclideanSpace.single i 1) * s102_hh C m (s102_tauk hT L) (s102_alk L) bfield i u0 +
      (1 / (2 * Real.sqrt N)) * ∑ i, ∑ j, iteratedFDeriv ℝ 2
          (gaussHeat (s102_obsCov C m (s102_tauk hT L) (s102_alk L)) G u0) (Z u0 ω)
          ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] *
        (2 * C.ν * s102_hh2 C m (s102_tauk hT L) (s102_alk L) eta i j u0) := by
  unfold itoDrift
  rw [hfd (Z u0 ω), hfeq]
  have h := S7PIF6_drift_alg (gaussHeat (s102_obsCov C m (s102_tauk hT L) (s102_alk L)) G u0) (Z u0 ω)
    (fun i j => s102_rateM C m hT L u0 i j)
    (fun i j => (Real.sqrt N)⁻¹ * (2 * C.ν * s102_hh2 C m (s102_tauk hT L) (s102_alk L) eta i j u0))
    (fun k => Φc u0 ω k) (bd u0 ω)
    (-(1 / 2) * ∑ i, ∑ j, s102_rateM C m hT L u0 i j *
        iteratedFDeriv ℝ 2 (gaussHeat (s102_obsCov C m (s102_tauk hT L) (s102_alk L)) G u0) (Z u0 ω)
          ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]) rfl hbr
  rw [h]
  have e1 : ∑ i, bd u0 ω i * fderiv ℝ (gaussHeat (s102_obsCov C m (s102_tauk hT L) (s102_alk L)) G u0) (Z u0 ω)
      (EuclideanSpace.single i 1) = -(Real.sqrt N)⁻¹ * ∑ i, fderiv ℝ (gaussHeat (s102_obsCov C m
        (s102_tauk hT L) (s102_alk L)) G u0) (Z u0 ω) (EuclideanSpace.single i 1) *
        s102_hh C m (s102_tauk hT L) (s102_alk L) bfield i u0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hbd i]; ring
  rw [e1]
  have e2 : (1 / 2 : ℝ) * ∑ i, ∑ j, iteratedFDeriv ℝ 2 (gaussHeat (s102_obsCov C m (s102_tauk hT L) (s102_alk L)) G u0)
      (Z u0 ω) ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] *
        ((Real.sqrt N)⁻¹ * (2 * C.ν * s102_hh2 C m (s102_tauk hT L) (s102_alk L) eta i j u0)) =
      (1 / (2 * Real.sqrt N)) * ∑ i, ∑ j, iteratedFDeriv ℝ 2 (gaussHeat (s102_obsCov C m (s102_tauk hT L)
        (s102_alk L)) G u0) (Z u0 ω) ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] *
        (2 * C.ν * s102_hh2 C m (s102_tauk hT L) (s102_alk L) eta i j u0) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [one_div, one_div, mul_inv]
    ring
  rw [e2]

end HRS.MS.R2Interp

end
