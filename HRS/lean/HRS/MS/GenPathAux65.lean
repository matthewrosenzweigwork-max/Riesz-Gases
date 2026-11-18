import HRS.MS.GenPathAux64

/-!
# S5.6 packet P10e: the a.e. measurability of the initial functional

The a.e. measurability of the initial functional (`hη` of `s56_general_paths_core`) follows from the independence clause of `IsLinearFluctuationSolutionW` and the
measurability of `Y` (`s56_aem_of_indep_sum`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole

variable {d : ℕ}

theorem s56_hη (b : WholeBounds d) (S : WholeSetup b) (N : ℕ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (η₀ : Ω → (Euc d → ℝ) → ℝ) (Y : ℝ → Ω → OscDual d b.m)
    (hY : IsLinearFluctuationSolutionW P (S.coeff N) b.m (S.q N) b.T (fun ζ f => S.A N * η₀ ζ f) Y)
    (t : Set.Icc (0 : ℝ) b.T) (α : MultiIndex d) :
    AEMeasurable (fun ζ => S.A N * η₀ ζ (propagatorW (S.coeff N) 0 t (oscTestFun b.m α))) P := by
  obtain ⟨hind, -⟩ := hY.gaussian_part 1 (fun _ => (t : ℝ)) (fun _ => oscTestFun b.m α) (fun _ => t.2)
    (fun _ => s56_isOscTest b.m α)
  simp only [OscDual.eval_oscTestFun] at hind
  have hind' := hind.comp (φ := fun v : EuclideanSpace ℝ (Fin 1) => v 0)
    (ψ := fun h : (Euc d → ℝ) → ℝ => h (propagatorW (S.coeff N) 0 t (oscTestFun b.m α)))
    (by fun_prop) (@measurable_pi_apply (Euc d → ℝ) (fun _ => ℝ) _
      (propagatorW (S.coeff N) 0 t (oscTestFun b.m α)))
  refine s56_aem_of_indep_sum P _ _ hind' ?_
  have hm : Measurable fun ω => (Y (t : ℝ) ω).coord α :=
    (s56_continuous_coord b.m α).measurable.comp (hY.meas _)
  convert hm using 2 with ω
  simp

end HRS.MS.GenPath
