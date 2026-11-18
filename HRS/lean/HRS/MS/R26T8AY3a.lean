import HRS.MS.R26T8AZ5c

/-!
# S8.2 T8A Y3a: locality and additivity of the mixed jets
`r26t8a_Y3a_jet_congr`: `mixedJet p q f X z` only depends on `f` on `{x ≠ y, |x-y| < 1}` (for `0 < |z| < 1/2`).
`r26t8a_Y3a_jet_add`: `mixedJet p q (f + g) = mixedJet p q f + mixedJet p q g` for `C^{p+q}` functions off the diagonal.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_Y3a_jet_congr {f g : Euc d → Euc d → ℝ} (p q : ℕ) (X z : Euc d)
    (h : ∀ x y : Euc d, x ≠ y → ‖x - y‖ < 1 → f x y = g x y) (hz : z ≠ 0) (hz1 : ‖z‖ < 1 / 2) :
    mixedJet p q f X z = mixedJet p q g X z := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  show r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair f Yw.1 Yw.2) X z =
    r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair g Yw.1 Yw.2) X z
  refine r26t8a_nest_congr_ball p q _ _ (ρ := ‖z‖ / 2) (by positivity) X z (fun Y w hw => ?_)
  have h1 : ‖z‖ - ‖w‖ ≤ ‖z - w‖ := norm_sub_norm_le z w
  rw [norm_sub_rev] at h1
  have h2 := norm_le_norm_add_norm_sub' w z
  have hw0 : w ≠ 0 := by
    intro h0; rw [h0, zero_sub, norm_neg] at hw; linarith
  have e : (Y + (1 / 2 : ℝ) • w) - (Y - (1 / 2 : ℝ) • w) = w := by module
  unfold midPair
  refine h _ _ ?_ ?_
  · intro hxy; apply hw0; rw [← e, hxy, sub_self]
  · rw [e]; linarith

theorem r26t8a_Y3a_jet_add {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {n : ℕ} {f g : Euc d → Euc d → ℝ}
    (hf : ContDiffOn ℝ n (Function.uncurry f) {p : Euc d × Euc d | p.1 ≠ p.2})
    (hg : ContDiffOn ℝ n (Function.uncurry g) {p : Euc d × Euc d | p.1 ≠ p.2})
    (p q : ℕ) (hpq : p + q ≤ n) (X z : Euc d) (hz : z ≠ 0) :
    mixedJet p q (fun x y => f x y + g x y) X z = mixedJet p q f X z + mixedJet p q g X z := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  set R : ℝ := 2 * ‖z‖ with hR
  have hRpos : 0 < R := by rw [hR]; positivity
  have hΨf : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞)
      (fun Yw : Euc d × Euc d => r26t8a_psiCut chi R Yw.2 * midPair f Yw.1 Yw.2) :=
    (r26t8a_gtilde_contDiff hchi hRpos hf).of_le (by exact_mod_cast hpq)
  have hΨg : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞)
      (fun Yw : Euc d × Euc d => r26t8a_psiCut chi R Yw.2 * midPair g Yw.1 Yw.2) :=
    (r26t8a_gtilde_contDiff hchi hRpos hg).of_le (by exact_mod_cast hpq)
  have hρ : 0 < ‖z‖ / 2 := by positivity
  have e1 : mixedJet p q (fun x y => f x y + g x y) X z =
      r26t8a_nest p q (fun Yw : Euc d × Euc d => r26t8a_psiCut chi R Yw.2 * midPair f Yw.1 Yw.2 +
        r26t8a_psiCut chi R Yw.2 * midPair g Yw.1 Yw.2) X z := by
    show r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair (fun x y => f x y + g x y) Yw.1 Yw.2) X z = _
    refine r26t8a_nest_congr_ball p q _ _ hρ X z (fun Y w hw => ?_)
    have h1 : ‖z‖ - ‖w‖ ≤ ‖z - w‖ := norm_sub_norm_le z w
    rw [norm_sub_rev] at h1
    have : R / 4 ≤ ‖w‖ := by rw [hR]; linarith
    simp only [r26t8a_psiCut_one hchi hRpos this, one_mul, midPair]
  rw [e1, r26t8a_nest_add p q z X hΨf hΨg, r26t8a_nest_gtilde hchi hRpos p q X z (by rw [hR]; linarith),
    r26t8a_nest_gtilde hchi hRpos p q X z (by rw [hR]; linarith)]

end HRS.MS.R26T8A
