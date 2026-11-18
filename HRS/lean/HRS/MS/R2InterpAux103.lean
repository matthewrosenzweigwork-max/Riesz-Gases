import HRS.MS.R2InterpAux102
import HRS.MC.S7FCW12A

/-!
# S10.2 (worker S10R), part 103 (packet M3e): measurability of `B_m`-valued maps from coordinates, and of paths from evaluations
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d : ℕ} {m : ℝ}

/-- A map into `B_m` with measurable coordinates (and square-summable coordinate sequences) is measurable. -/
theorem s102_measurable_lp {Ω : Type*} [MeasurableSpace Ω] (a : Ω → MultiIndex d → ℝ) (hm : ∀ ω, Memℓp (a ω) 2)
    (hc : ∀ α, Measurable fun ω => a ω α) :
    Measurable fun ω => (show OscDual d m from (⟨a ω, hm ω⟩ : lp (fun _ : MultiIndex d => ℝ) 2)) := by
  refine HRS.MC.Sec7.S7FCW12.s7fcw12_measurable_of_edist _ fun x => ?_
  have hsum : ∀ ω, Summable fun α : MultiIndex d => (a ω α - OscDual.coord x α) ^ 2 := by
    intro ω
    have h1 : Memℓp (fun α => a ω α - OscDual.coord x α) 2 := (hm ω).sub (lp.memℓp (show lp (fun _ : MultiIndex d => ℝ) 2 from x))
    exact (memℓp_two_iff.1 h1)
  have hnorm : ∀ ω, edist (show OscDual d m from (⟨a ω, hm ω⟩ : lp (fun _ : MultiIndex d => ℝ) 2)) x =
      ENNReal.ofReal (Real.sqrt (∑' α : MultiIndex d, (a ω α - OscDual.coord x α) ^ 2)) := by
    intro ω
    rw [edist_dist, dist_eq_norm, OscDual.norm_eq_coord]
    congr 3
  simp_rw [hnorm]
  have hmeas : Measurable fun ω => ∑' α : MultiIndex d, ENNReal.ofReal ((a ω α - OscDual.coord x α) ^ 2) :=
    Measurable.ennreal_tsum fun α => ENNReal.measurable_ofReal.comp (((hc α).sub_const _).pow_const 2)
  have : ∀ ω, ∑' α : MultiIndex d, (a ω α - OscDual.coord x α) ^ 2 =
      (∑' α : MultiIndex d, ENNReal.ofReal ((a ω α - OscDual.coord x α) ^ 2)).toReal := by
    intro ω
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun α => sq_nonneg _) (hsum ω), ENNReal.toReal_ofReal
      (tsum_nonneg fun α => sq_nonneg _)]
  simp_rw [this]
  exact ENNReal.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp (ENNReal.measurable_toReal.comp hmeas))

end HRS.MS.R2Interp

end
