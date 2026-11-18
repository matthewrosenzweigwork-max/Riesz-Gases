import HRS.MS.R26T8AO06f

/-!
# S8.2 T8A O06 (part g): the literal propagator objects are the age objects
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_o06_prop_conv (d N : ℕ) (a beta m M C Cf c : ℝ) (rho : Euc d → ℝ)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ) (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) (alpha : MultiIndex d) (r b : ℝ) (hr0 : 0 ≤ r) (hrb : r ≤ b) :
    r26t8a_correctedQ (N := N) a beta Psi (propagatorW (critCoeff d a beta rho) r b (oscTestFun m alpha)) =
      r26t8a_QAge a beta m rho Psi alpha 0 (b - r) ∧
    scalarForcing (N := N) a beta rho (propagatorW (critCoeff d a beta rho) r b (oscTestFun m alpha)) =
      scalarForcing a beta rho (r26t8a_ageTest a beta m rho alpha 0 (b - r)) ∧
    r26t8a_correctedD (N := N) a beta rho Psi (propagatorW (critCoeff d a beta rho) r b (oscTestFun m alpha)) =
      r26t8a_DAge a beta m rho Psi alpha 0 (b - r) ∧
    r26t8a_correctedQ (N := N) a beta Psi (HRS.Whole.projGeneratorW (critCoeff d a beta rho)
        (HRS.Whole.withDensityReal rho) 0 (propagatorW (critCoeff d a beta rho) r b (oscTestFun m alpha))) =
      r26t8a_QAge a beta m rho Psi alpha 1 (b - r) := by
  rw [horb.shift alpha r b hr0 hrb]
  set g := propagatorW (critCoeff d a beta rho) 0 (b - r) (oscTestFun m alpha) with hg
  have hTB := horb.bound alpha (b - r) (sub_nonneg.2 hrb) 0 (by norm_num)
  have hsplit : g = fun x => r26t8a_ageTest a beta m rho alpha 0 (b - r) x +
      HRS.Whole.pair (HRS.Whole.withDensityReal rho) g := by
    funext x
    show g x = (HRS.Whole.projMean (HRS.Whole.withDensityReal rho) g) x + _
    unfold HRS.Whole.projMean; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsplit]
    exact r26t8a_o06_Q_const N hPsi hTB _
  · rw [hsplit]
    exact r26t8a_o06_SF_const a beta rho _ _
  · rw [hsplit]
    exact r26t8a_o06_D_const hPsi hTB _
  · have e : HRS.Whole.projGeneratorW (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) 0
        (fun x => r26t8a_ageTest a beta m rho alpha 0 (b - r) x + HRS.Whole.pair (HRS.Whole.withDensityReal rho) g) =
        HRS.Whole.projGeneratorW (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) 0
          (r26t8a_ageTest a beta m rho alpha 0 (b - r)) :=
      r26t8a_o06_projGen_const _ _ hTB.1 _
    rw [hsplit, e]
    rfl

end HRS.MS.R26T8A

end
