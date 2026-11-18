import HRS.MS.SA12X5D4A

/-!
# S.A.12 X5 D4B: linearity of `perL`, linearity of `tca_S` in `W`, and the linear facts of the mollified periodization
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MS.ToriCoefA HRS.MS.ToriCoefB HRS.MS.ToriConv HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x5_perL_sub (L : ℝ) (hL : 0 < L) {f g : Euc d → ℝ}
    (hf : ∀ y : Euc d, L / 3 ≤ ‖y‖ → f y = 0) (hg : ∀ y : Euc d, L / 3 ≤ ‖y‖ → g y = 0) (x : Euc d) :
    perL L (fun y => f y - g y) x = perL L f x - perL L g x := by
  obtain ⟨z, hz⟩ := tca_exists_U L hL x
  have hfg : ∀ y : Euc d, L / 3 ≤ ‖y‖ → (fun y => f y - g y) y = 0 := fun y hy => by
    simp only [hf y hy, hg y hy, sub_zero]
  rw [tca_perL_eq_on L hL _ hfg z x hz, tca_perL_eq_on L hL f hf z x hz, tca_perL_eq_on L hL g hg z x hz]

theorem sa12x5_S_mul (Kz : ℕ → ℝ) (W : ℝ) (j : ℕ) : tca_S d Kz W j = W * tca_S d Kz 1 j := by
  unfold tca_S
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The linear half of `sa12k_moll_facts` (no sign, no mass), with the bounds on the jets up to order `n`. -/
theorem sa12x5_moll_linear_facts (L : ℝ) (hL : 7 ≤ L) {δ : ℝ} {η : Euc d → ℝ} (hη : SA12KMoll δ η)
    (hδ : δ ≤ 1) {f : Euc d → ℝ} (hv : ∀ y : Euc d, L / 3 ≤ ‖y‖ → f y = 0) {n : ℕ} {B : ℝ}
    (hμcd : ContDiff ℝ (n : WithTop ℕ∞) (perL L f))
    (hfB : ∀ j ≤ n, ∀ w : Euc d, ‖iteratedFDeriv ℝ j f w‖ ≤ B * tca_g w)
    (hμbd : ∀ j ≤ n, ∀ y : Euc d, ‖iteratedFDeriv ℝ j (perL L f) y‖ ≤ B) :
    (∀ (x : Euc d) (k : Fin d → ℤ),
        sa12k_moll η (perL L f) (x + L • latticePt k) = sa12k_moll η (perL L f) x) ∧
      ContDiff ℝ ∞ (sa12k_moll η (perL L f)) ∧
      (∀ j ≤ n, ∀ y : Euc d, ‖iteratedFDeriv ℝ j (sa12k_moll η (perL L f)) y‖ ≤ B) ∧
      (∀ j ≤ n, ∀ x : Euc d, ∃ k : Fin d → ℤ,
        jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) *
          ‖iteratedFDeriv ℝ j (sa12k_moll η (perL L f)) x‖ ≤ (2 : ℝ) ^ ((d : ℝ) + 3) * B) ∧
      (∀ j ≤ n, ∀ x : Euc d,
        ∫ z in tcb_Q d L, ‖iteratedFDeriv ℝ j (sa12k_moll η (perL L f)) (x - z)‖ ≤
          2 ^ d * B * ∫ w : Euc d, tca_g w) := by
  have hL0 : 0 < L := by linarith
  have hμc : Continuous (perL L f) := hμcd.continuous
  have hper := sa12k_perL_periodic L f
  refine ⟨sa12k_moll_periodic η L hper, sa12k_moll_contDiff hη hμc, ?_, ?_, ?_⟩
  · intro j hj y
    have h1 := sa12k_moll_iter hη hμcd hμbd j hj
    rw [congrFun h1 y]
    exact sa12k_moll_norm_le hη (hμcd.continuous_iteratedFDeriv (by exact_mod_cast hj))
      (fun y' => hμbd j hj y') y
  · exact sa12k_moll_decay L hL hη hδ hv hμcd hfB hμbd
  · intro j hj x
    have h1 := sa12k_moll_iter hη hμcd hμbd j hj
    have e : (fun z => ‖iteratedFDeriv ℝ j (sa12k_moll η (perL L f)) (x - z)‖) =
        fun z => ‖sa12k_moll η (iteratedFDeriv ℝ j (perL L f)) (x - z)‖ := by
      funext z; rw [congrFun h1 (x - z)]
    show ∫ z in tcb_Q d L, ‖iteratedFDeriv ℝ j (sa12k_moll η (perL L f)) (x - z)‖ ≤ _
    rw [e]
    refine sa12k_set_moll_le hη (hμcd.continuous_iteratedFDeriv (by exact_mod_cast hj))
      (fun y' => hμbd j hj y') (tcb_measurableSet_Q L) (tcb_measure_Q_lt_top L) x
      (E := 2 ^ d * B * ∫ w : Euc d, tca_g w) (fun u hu => ?_)
    exact tcb_cube_l1 hL0 f hv j B (hfB j hj) (x - u)

end HRS.MH.AdjointRd.Phase2SA12X5
