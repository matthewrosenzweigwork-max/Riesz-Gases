import HRS.MS.PROS15dPhysicalFiniteIndep

/-!
# R26-T3.S15d: arbitrary finite-index orthogonal Gaussian physical field

Reindexes the exact Fin n result to arbitrary finite index types, allowing
finite-subset restrictions of an infinite family.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem s15d_physical_fintype_indep_orthogonal
    {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    (I : ProductGaussian μ)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → HRS.Euc d → ℝ) (he : ∀ i, MemLp (e i) 2 μ)
    (hOrtho : ∀ i j, ∫ x, HRS.Whole.projMean μ (e i) x *
        HRS.Whole.projMean μ (e j) x ∂μ = if i = j then 1 else 0) :
    iIndepFun (fun i => I.η (e i)) I.P := by
  classical
  let E : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hFin := s15d_physical_finite_indep_orthogonal I
    (Fintype.card ι) (fun i : Fin (Fintype.card ι) => e (E.symm i))
    (fun i => he (E.symm i)) (by
      intro i j
      simpa only [E.symm_apply_eq, E.apply_symm_apply] using hOrtho (E.symm i) (E.symm j))
  have hPre := hFin.precomp (g := E) E.injective
  simpa only [Function.comp_def, E.symm_apply_apply] using hPre

end HRS.MS.R26T3
