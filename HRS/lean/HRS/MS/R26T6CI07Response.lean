import HRS.MS.R26T6CI07Pos
import HRS.MS.R26T6CI05

/-!
# S11.1 I07: positive-Riesz screened response in L3
A local bounded-density estimate, ready for uniform thermal assembly.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
namespace HRS.MS.R26T6C
open HRS HRS.Whole HRS.Whole.Q34 HRS.MS.S111X2
variable {d : ℕ}

theorem r26t6c_positive_riesz_response_L3
    (hd : 2 ≤ d) (s M : ℝ) (hs : 0 < s) (h2s : 2*s < d)
    (rho : Euc d → ℝ) (hrho : HRS.Whole.IsProbDensity rho)
    (hM : ∀ x, rho x ≤ M)
    [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)]
    (K : Lp ℝ 2 (HRS.Whole.withDensityReal rho) →L[ℝ]
      Lp ℝ 2 (HRS.Whole.withDensityReal rho)) (Mg : ℝ)
    (hK : HRS.MS.S111X2.KRep (HRS.Whole.rieszKernel d s)
      (HRS.Whole.withDensityReal rho) K Mg)
    (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (f : Euc d → ℝ)
    (hf : MemLp f 3 (HRS.Whole.withDensityReal rho)) :
    let mu := HRS.Whole.withDensityReal rho
    MemLp (HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) mu gamma f) 3 mu ∧
    eLpNorm (HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) mu gamma f) 3 mu ≤
      ENNReal.ofReal (1 + gamma *
        (2 * Real.sqrt (M * sphereArea d / ((d : ℝ) - 2*s) + 1))) *
          eLpNorm (HRS.Whole.projMean mu f) 3 mu := by
  let mu := HRS.Whole.withDensityReal rho
  letI : IsProbabilityMeasure mu := Q34.isProbabilityMeasure_nu hrho
  let R : ℝ := Real.sqrt (M * sphereArea d / ((d : ℝ) - 2*s) + 1)
  have hR : 0 ≤ 2 * R := by
    exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have h23 : ∀ f : Euc d → ℝ, MemLp f 2 mu →
      MemLp (HRS.Whole.Kop (HRS.Whole.rieszKernel d s) mu f) 3 mu ∧
      eLpNorm (HRS.Whole.Kop (HRS.Whole.rieszKernel d s) mu f) 3 mu ≤
        ENNReal.ofReal (2 * R) * eLpNorm f 2 mu := by
    intro f hf
    simpa only [mu, R] using
      r26t6c_positive_riesz_Kop_L2_L3 hd s M hs h2s rho hrho hM f hf
  exact r26t6c_response_L3 mu (HRS.Whole.rieszKernel d s)
    K Mg (2 * R) hR hK h23 gamma hgamma f hf

end HRS.MS.R26T6C
