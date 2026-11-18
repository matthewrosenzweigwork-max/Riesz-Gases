import HRS.MS.SA12K12

/-!
# S.A.12 C1, `PerData` ingredients for the mollified density and potential
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MS.ToriCoefA HRS.MS.ToriCoefB HRS.MS.ToriConv

variable {d : ℕ}

/-- All the density facts of the mollified periodization. -/
theorem sa12k_moll_facts (L : ℝ) (hL : 7 ≤ L) {δ : ℝ} {η : Euc d → ℝ} (hη : SA12KMoll δ η)
    (hδ : δ ≤ 1) {f : Euc d → ℝ} (hv : ∀ y : Euc d, L / 3 ≤ ‖y‖ → f y = 0)
    (hfnn : ∀ y, 0 ≤ f y) (hfint : ∫ y, f y = 1) {m : ℕ} {Bd Bc : ℝ}
    (hμcd : ContDiff ℝ ((m + 3 : ℕ) : WithTop ℕ∞) (perL L f))
    (hμbd : ∀ j ≤ m + 3, ∀ y : Euc d, ‖iteratedFDeriv ℝ j (perL L f) y‖ ≤ Bd)
    (hfw : ∀ j ≤ m + 3, ∀ w : Euc d, ‖iteratedFDeriv ℝ j f w‖ ≤ Bd * tca_g w)
    (hcube : ∀ j ≤ m + 3, ∀ x : Euc d,
      ∫ z in tcb_Q d L, ‖iteratedFDeriv ℝ j (perL L f) (x - z)‖ ≤ Bc) :
    (∀ (x : Euc d) (k : Fin d → ℤ),
        sa12k_moll η (perL L f) (x + L • latticePt k) = sa12k_moll η (perL L f) x) ∧
      ContDiff ℝ ∞ (sa12k_moll η (perL L f)) ∧
      (∀ x, 0 ≤ sa12k_moll η (perL L f) x) ∧
      ∫ x in periodBox d L, sa12k_moll η (perL L f) x = 1 ∧
      (∀ j ≤ m + 3, ∀ y : Euc d, ‖iteratedFDeriv ℝ j (sa12k_moll η (perL L f)) y‖ ≤ Bd) ∧
      (∀ j ≤ m + 3, ∀ x : Euc d, ∃ k : Fin d → ℤ,
        jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) *
          ‖iteratedFDeriv ℝ j (sa12k_moll η (perL L f)) x‖ ≤ (2 : ℝ) ^ ((d : ℝ) + 3) * Bd) ∧
      (∀ j ≤ m + 3, ∀ x : Euc d,
        ∫ z in tcb_Q d L, ‖iteratedFDeriv ℝ j (sa12k_moll η (perL L f)) (x - z)‖ ≤ Bc) := by
  have hL0 : 0 < L := by linarith
  have hμc : Continuous (perL L f) := hμcd.continuous
  have hnn : ∀ y, 0 ≤ perL L f y := fun y => sa12k_perL_nonneg L hfnn y
  have hbd0 : ∀ y, |perL L f y| ≤ Bd := fun y => by
    have := hμbd 0 (by omega) y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hbdnn : 0 ≤ Bd := (abs_nonneg _).trans (hbd0 0)
  have hper := sa12k_perL_periodic L f
  have hmass : ∫ x in periodBox d L, perL L f x = 1 := by
    rw [sa12k_perL_integral L hL0 hv, hfint]
  refine ⟨sa12k_moll_periodic η L hper, sa12k_moll_contDiff hη hμc,
    fun x => sa12k_moll_nonneg hη hnn x, ?_, ?_, ?_, ?_⟩
  · rw [sa12k_moll_box_integral hη L hL0 hμc hbd0 hper, hmass]
  · intro j hj y
    have h1 := sa12k_moll_iter hη hμcd hμbd j hj
    rw [congrFun h1 y]
    exact sa12k_moll_norm_le hη (hμcd.continuous_iteratedFDeriv (by exact_mod_cast hj))
      (fun y' => hμbd j hj y') y
  · exact sa12k_moll_decay L hL hη hδ hv hμcd hfw hμbd
  · intro j hj x
    have h1 := sa12k_moll_iter hη hμcd hμbd j hj
    have e : (fun z => ‖iteratedFDeriv ℝ j (sa12k_moll η (perL L f)) (x - z)‖) =
        fun z => ‖sa12k_moll η (iteratedFDeriv ℝ j (perL L f)) (x - z)‖ := by
      funext z; rw [congrFun h1 (x - z)]
    show ∫ z in tcb_Q d L, ‖iteratedFDeriv ℝ j (sa12k_moll η (perL L f)) (x - z)‖ ≤ Bc
    rw [e]
    refine sa12k_set_moll_le hη (hμcd.continuous_iteratedFDeriv (by exact_mod_cast hj))
      (fun y' => hμbd j hj y') (tcb_measurableSet_Q L) (tcb_measure_Q_lt_top L) x
      (E := Bc) (fun u hu => ?_)
    exact hcube j hj (x - u)

end HRS.MH.AdjointRd.Phase2SA12Construction
