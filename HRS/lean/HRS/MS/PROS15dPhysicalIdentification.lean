import HRS.MS.PROS15dCanonicalIdentification
import HRS.MS.PROS15dPhysicalBasis
import HRS.MS.CanThmAux1

/-!
# S15d: physical Wick quadratic coincides with the canonical S13 quadratic

This theorem uses exactly the physical trajectory assumptions of the frozen
S15d contract, rather than assuming the existence of a smooth test basis.
It does not yet identify the canonical quadratic with the spectral
Hilbert-Schmidt series or prove the susceptibility formula.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS.Whole

theorem s15d_physical_wick_identifies_riesz_quadratic
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ)
    (I : ProductGaussian (r26t3_mu R 0))
    (Qg : I.Ω → ℝ)
    (hW : ∀ a, IsR2ZeroMeanONB (r26t3_mu R 0) a →
      IsR2WickChaos I.P (r26t3_mu R 0) a (fun j => I.η (a j))
        (r2CenterKernel (r26t3_mu R 0)
          (fun x y => rieszKernel p.d p.s (x - y))) (fun ω => 2 * Qg ω)) :
    ∃ Q : I.Ω → ℝ,
      HasActualProductQuadraticLimit I
        (fun x y => rieszKernel p.d p.s (x - y)) Q ∧
      Qg =ᵐ[I.P] Q := by
  letI : IsProbabilityMeasure (r26t3_mu R 0) :=
    s21h2_mu_prob hδ hδh R
  have hL2 := (r26t3_interaction_hs hδ hδh R).1
  have hSym : ∀ x y : Euc p.d,
      rieszKernel p.d p.s (x - y) = rieszKernel p.d p.s (y - x) := by
    intro x y
    simpa only [neg_sub] using
      (HRS.MS.Can2.can2_rieszKernel_neg p.s (y - x))
  exact s15d_physical_wick_identifies_actual
    I (fun x y => rieszKernel p.d p.s (x - y))
    hL2 hSym Qg
    (s15d_physical_test_basis_exists hδ hδh R) hW

end HRS.MS.R26T3
