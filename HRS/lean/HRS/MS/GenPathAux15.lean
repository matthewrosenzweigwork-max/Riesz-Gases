import HRS.MS.GenPathAux14

/-!
# S5.6: small fact for the final assembly

* `s56_secondMoment_pos`: a probability density on `ℝ^d`, `d ≥ 1`, with integrable second moment has positive second moment
  (so the hypothesis `ofReal ⟨|x|²,ρ_N^t⟩ ≤ ofReal M₂` of `general_paths` forces `M₂ > 0`, and `1 + M₂ > 0` in the localisation rate);
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS.Whole HRS.Whole.AppendixA HRS.MP.RdRem

variable {d : ℕ}

theorem s56_secondMoment_pos (hd : 1 ≤ d) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    (hint : Integrable (fun x => ‖x‖ ^ 2 * ρ x)) :
    0 < secondMomentOf (HRS.Whole.withDensityReal ρ) := by
  unfold secondMomentOf HRS.Whole.pair
  rw [mrr_integral_withDensityReal ρ hρ.measurable hρ.nonneg]
  have hnn : ∀ x, 0 ≤ ρ x * ‖x‖ ^ 2 := fun x => mul_nonneg (hρ.nonneg x) (sq_nonneg _)
  have hint' : Integrable (fun x => ρ x * ‖x‖ ^ 2) := by
    refine hint.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring
  refine lt_of_le_of_ne (integral_nonneg hnn) fun h0 => ?_
  have hz := (integral_eq_zero_iff_of_nonneg hnn hint').1 h0.symm
  have hnull : ∀ᵐ x : Euc d ∂volume, x ≠ 0 := by
    have : (volume : Measure (Euc d)) {0} = 0 := by
      haveI : Nontrivial (Euc d) := by
        haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
        infer_instance
      exact measure_singleton 0
    exact measure_eq_zero_iff_ae_notMem.1 this |>.mono fun x hx => hx
  have hρ0 : ρ =ᵐ[volume] 0 := by
    filter_upwards [hz, hnull] with x hx hx0
    have : ‖x‖ ^ 2 ≠ 0 := by positivity
    simpa [this] using hx
  have h1 : ∫ x, ρ x = 0 := by
    rw [integral_congr_ae hρ0]; simp
  linarith [hρ.integral_one]

end HRS.MS.GenPath
