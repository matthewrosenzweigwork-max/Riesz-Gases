import HRS.MS.S21T4ProdAS
import Mathlib.Probability.CramerWold

/-! A varying-source-space Cramér-Wold theorem for empirical particle CLTs. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.MS.R26T3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)]
    {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)]
    {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : (N : ℕ) → Ω N → E} {Z : Ω' → E}

/-- Cramér-Wold with varying particle configuration spaces and varying
reference product measures. Unlike the fixed-source Mathlib formulation,
this covers the actual family μ^{⊗N} without replacing it by infinitePi μ. -/
theorem s21t4_varying_cramer_wold
    (hX : ∀ N, AEMeasurable (X N) (P N)) (hZ : AEMeasurable Z P')
    (hproj : ∀ t : E,
      TendstoInDistribution (fun N ω => ⟪X N ω, t⟫) atTop
        (fun ω => ⟪Z ω, t⟫) P P') :
    TendstoInDistribution X atTop Z P P' := by
  refine .of_tendsto_charFun hX hZ fun t => ?_
  rw [charFun_map_eq_charFun_map_inner_one hZ]
  refine (hproj t).tendsto_charFun 1 |>.congr fun N => ?_
  rw [charFun_map_eq_charFun_map_inner_one (hX N)]

end HRS.MS.R26T3
