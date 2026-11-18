import HRS.MS.PROS15dPhysicalFintypeIndep

/-!
# R26-T3.S15d: actual infinite independent Gaussian coordinates

An arbitrary countable orthogonal family of spatial L2 tests in the
ProductGaussian model has genuinely mutually independent first-chaos
coordinates. This extends the smooth test basis result to the possibly
nonsmooth spectral Hilbert-Schmidt eigenfunctions.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem s15d_physical_infinite_indep_orthogonal
    {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    (I : ProductGaussian μ)
    (e : ℕ → HRS.Euc d → ℝ)
    (he : ∀ i, MemLp (e i) 2 μ)
    (hOrtho : ∀ i j, ∫ x, HRS.Whole.projMean μ (e i) x *
        HRS.Whole.projMean μ (e j) x ∂μ = if i = j then 1 else 0) :
    iIndepFun (fun i => I.η (e i)) I.P := by
  classical
  refine iIndepFun_iff_finset.mpr ?_
  intro s
  have hs := s15d_physical_fintype_indep_orthogonal I
    (fun i : s => e i.1) (fun i => he i.1) (by
      intro i j
      simpa only [Subtype.ext_iff] using hOrtho i.1 j.1)
  exact hs

end HRS.MS.R26T3
