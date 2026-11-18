import HRS.MS.R2InterpAux109

/-!
# S10.2 (worker S10R), part 110: the expectation of the empirical polynomial moment is the moment of the mean empirical measure
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d : ℕ}

theorem s102_empMoment {N : ℕ} (hN : 0 < N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → EucConfig d N) (hY : Measurable Y) {a : Euc d → ℝ} (ham : Measurable a) (ha0 : ∀ x, 0 ≤ a x)
    (hint : Integrable a (HRS.Whole.meanEmpirical (P.map Y))) :
    Integrable (fun ζ => (N : ℝ)⁻¹ * ∑ k, a (Y ζ k)) P ∧
      ∫ ζ, (N : ℝ)⁻¹ * ∑ k, a (Y ζ k) ∂P = ∫ x, a x ∂(HRS.Whole.meanEmpirical (P.map Y)) := by
  have hN' : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hN.ne'
  have hcoord : ∀ k : Fin N, Integrable (fun ζ => a (Y ζ k)) P := by
    intro k
    have hle : (P.map Y).map (fun X : EucConfig d N => X k) ≤ (N : ℝ≥0∞) • HRS.Whole.meanEmpirical (P.map Y) := by
      rw [HRS.MS.S21.s21_meanEmpirical_eq_sum, smul_smul, ENNReal.mul_inv_cancel hN' (by simp), one_smul]
      calc (P.map Y).map (fun X : EucConfig d N => X k) ≤ ∑ i : Fin N, (P.map Y).map (fun X : EucConfig d N => X i) :=
            Finset.single_le_sum (f := fun i : Fin N => (P.map Y).map (fun X : EucConfig d N => X i))
              (fun i _ => bot_le) (Finset.mem_univ k)
        _ = _ := rfl
    have h1 : Integrable a ((P.map Y).map (fun X : EucConfig d N => X k)) :=
      (hint.smul_measure (by simp)).mono_measure hle
    have h2 := (integrable_map_measure ham.aestronglyMeasurable (measurable_pi_apply k).aemeasurable).1 h1
    exact (integrable_map_measure (ham.comp (measurable_pi_apply k)).aestronglyMeasurable hY.aemeasurable).1 h2
  have hmean : ∫ x, a x ∂(HRS.Whole.meanEmpirical (P.map Y)) = (N : ℝ)⁻¹ * ∑ k, ∫ ζ, a (Y ζ k) ∂P := by
    haveI : IsProbabilityMeasure (P.map Y) := ⟨by rw [Measure.map_apply hY MeasurableSet.univ]; simp⟩
    rw [HRS.MS.S21.s21_meanEmpirical_eq_sum, integral_smul_measure, integral_finsetSum_measure]
    · congr 1
      · simp [ENNReal.toReal_inv]
      · refine Finset.sum_congr rfl fun i _ => ?_
        have e1 := integral_map (μ := P.map Y) (φ := fun X : EucConfig d N => X i) (f := a)
          (measurable_pi_apply i).aemeasurable ham.aestronglyMeasurable
        have e2 := integral_map (μ := P) (φ := Y) (f := fun x : EucConfig d N => a (x i))
          hY.aemeasurable (ham.comp (measurable_pi_apply i)).aestronglyMeasurable
        rw [e1]
        exact e2
    · intro i _
      have : Integrable (fun ζ => a (Y ζ i)) P := hcoord i
      have h2 : Integrable (fun X : EucConfig d N => a (X i)) (P.map Y) :=
        (integrable_map_measure (ham.comp (measurable_pi_apply i)).aestronglyMeasurable hY.aemeasurable).2 this
      exact (integrable_map_measure ham.aestronglyMeasurable (measurable_pi_apply i).aemeasurable).2 h2
  refine ⟨(integrable_finsetSum _ fun k _ => hcoord k).const_mul _, ?_⟩
  rw [hmean, integral_const_mul, integral_finset_sum _ fun k _ => hcoord k]

end HRS.MS.R2Interp

end
