import HRS.Commutator.Torus.TEXTAux4

/-!
# T-EXT-A helpers, part 5: a measurable version of an `ℝ^d` kernel with everywhere bounds
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

/-- Replace an a.e.-strongly measurable kernel by a measurable one that agrees a.e. and satisfies the
(everywhere) bounds with the same constants. -/
lemma text_meas_version {γ : ℝ} {Kt : Euc d → ℝ} (hint : Integrable Kt) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hnear : ∀ x : Euc d, x ≠ 0 → ‖x‖ ≤ 1 → |Kt x| ≤ C₀ * ‖x‖ ^ (γ - d))
    (Cm : ℕ → ℝ) (hCm : ∀ m, 0 ≤ Cm m)
    (hfar : ∀ (m : ℕ) (x : Euc d), 1 ≤ ‖x‖ → |Kt x| ≤ Cm m * ‖x‖ ^ (-(m : ℝ))) :
    ∃ K' : Euc d → ℝ, Measurable K' ∧ (∀ᵐ x ∂volume, K' x = Kt x) ∧
      (∀ x : Euc d, x ≠ 0 → ‖x‖ ≤ 1 → |K' x| ≤ C₀ * ‖x‖ ^ (γ - d)) ∧
      (∀ (m : ℕ) (x : Euc d), 1 ≤ ‖x‖ → |K' x| ≤ Cm m * ‖x‖ ^ (-(m : ℝ))) := by
  classical
  set K'' := hint.1.mk Kt with hK''
  have hae : Kt =ᵐ[volume] K'' := hint.1.ae_eq_mk
  have hm : Measurable K'' := hint.1.stronglyMeasurable_mk.measurable
  let P : Euc d → Prop := fun x =>
    (x ≠ 0 → ‖x‖ ≤ 1 → |K'' x| ≤ C₀ * ‖x‖ ^ (γ - d)) ∧
      ∀ m : ℕ, 1 ≤ ‖x‖ → |K'' x| ≤ Cm m * ‖x‖ ^ (-(m : ℝ))
  have hPmeas : MeasurableSet {x | P x} := by
    have h1 : MeasurableSet {x : Euc d | x ≠ 0 → ‖x‖ ≤ 1 → |K'' x| ≤ C₀ * ‖x‖ ^ (γ - d)} := by
      have : {x : Euc d | x ≠ 0 → ‖x‖ ≤ 1 → |K'' x| ≤ C₀ * ‖x‖ ^ (γ - d)} =
          {x : Euc d | x = 0}ᶜᶜ ∪ ({x : Euc d | ‖x‖ ≤ 1}ᶜ ∪ {x : Euc d | |K'' x| ≤ C₀ * ‖x‖ ^ (γ - d)}) := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff, not_not]
        tauto
      rw [this]
      refine (MeasurableSet.compl (MeasurableSet.compl (measurableSet_eq_fun measurable_id measurable_const))).union
        ((MeasurableSet.compl (measurableSet_le (by fun_prop) measurable_const)).union
          (measurableSet_le hm.abs (by fun_prop)))
    have h2 : MeasurableSet {x : Euc d | ∀ m : ℕ, 1 ≤ ‖x‖ → |K'' x| ≤ Cm m * ‖x‖ ^ (-(m : ℝ))} := by
      have : {x : Euc d | ∀ m : ℕ, 1 ≤ ‖x‖ → |K'' x| ≤ Cm m * ‖x‖ ^ (-(m : ℝ))} =
          ⋂ m : ℕ, ({x : Euc d | 1 ≤ ‖x‖}ᶜ ∪ {x : Euc d | |K'' x| ≤ Cm m * ‖x‖ ^ (-(m : ℝ))}) := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff, not_le]
        constructor
        · intro h m; by_cases h1 : 1 ≤ ‖x‖
          · right; exact h m h1
          · left; exact not_le.1 h1
        · intro h m h1
          rcases h m with h2 | h2
          · exact absurd h1 (not_le.2 h2)
          · exact h2
      rw [this]
      refine MeasurableSet.iInter fun m => ?_
      exact (MeasurableSet.compl (measurableSet_le measurable_const (by fun_prop))).union
        (measurableSet_le hm.abs (by fun_prop))
    exact h1.inter h2
  refine ⟨fun x => if P x then K'' x else 0, ?_, ?_, ?_, ?_⟩
  · exact Measurable.ite hPmeas hm measurable_const
  · filter_upwards [hae] with x hx
    have hP : P x := by
      refine ⟨fun h0 h1 => ?_, fun m h1 => ?_⟩
      · rw [← hx]; exact hnear x h0 h1
      · rw [← hx]; exact hfar m x h1
    simp only [hP, if_true, hx]
  · intro x hx0 hx1
    by_cases hP : P x
    · simp only [hP, if_true]; exact hP.1 hx0 hx1
    · simp only [hP, if_false, abs_zero]; positivity
  · intro m x hx1
    by_cases hP : P x
    · simp only [hP, if_true]; exact hP.2 m hx1
    · simp only [hP, if_false, abs_zero]; exact mul_nonneg (hCm m) (by positivity)

end HRS.Commutator.TorusNote
