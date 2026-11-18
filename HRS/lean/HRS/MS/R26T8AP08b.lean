import HRS.MS.R26T8AP08a
import HRS.MS.R26T8AP11lb
import HRS.MS.R26T8AP01b

/-!
# S8.2 T8A P08 (part b): `Conormal` is invariant under swapping the two variables
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_f24_conormal_swap {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {k b : ℕ} {M σ A : ℝ}
    {F : Euc d → Euc d → ℝ} (hF : Conormal k b M σ A F) : Conormal k b M σ A (fun x y => F y x) := by
  refine ⟨?_, fun p q hpq X z hz => ?_⟩
  · have hsw : ContDiff ℝ (k : WithTop ℕ∞) (fun w : Euc d × Euc d => (w.2, w.1)) := contDiff_snd.prodMk contDiff_fst
    have hm : Set.MapsTo (fun w : Euc d × Euc d => (w.2, w.1)) {w : Euc d × Euc d | w.1 ≠ w.2}
        {w : Euc d × Euc d | w.1 ≠ w.2} := fun w hw => fun h => hw h.symm
    exact hF.1.comp hsw.contDiffOn hm
  · have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 2 * ‖z‖ := ⟨_, rfl⟩
    have hR : 0 < R := by rw [hRdef]; positivity
    have hl : R / 4 < ‖-z‖ := by rw [norm_neg, hRdef]; linarith
    set Ψ : Euc d × Euc d → ℝ := fun Yw => r26t8a_psiCut chi R Yw.2 * midPair F Yw.1 Yw.2 with hΨdef
    have hΨ : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) Ψ :=
      (r26t8a_gtilde_contDiff hchi hR hF.1).of_le (by exact_mod_cast hpq)
    have hcong : r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair (fun x y => F y x) Yw.1 Yw.2) X z =
        r26t8a_nest p q (fun Yw : Euc d × Euc d => Ψ (Yw.1, -Yw.2)) X z := by
      refine r26t8a_nest_congr_ball p q _ _ (ρ := ‖z‖ / 2) (by positivity) X z (fun Y w hw => ?_)
      have h1 : ‖z‖ - ‖w‖ ≤ ‖z - w‖ := norm_sub_norm_le z w
      rw [norm_sub_rev] at h1
      have h2 : R / 4 ≤ ‖-w‖ := by rw [norm_neg, hRdef]; linarith
      simp only [hΨdef, r26t8a_psiCut_one hchi hR h2, one_mul, midPair]
      congr 1 <;> module
    have hmj : mixedJet p q (fun x y => F y x) X z =
        r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair (fun x y => F y x) Yw.1 Yw.2) X z := rfl
    rw [hmj, hcong]
    refine (r26t8a_f24_nest_negw p q hΨ X z).trans ?_
    rw [r26t8a_nest_gtilde hchi hR (F := F) p q X (-z) hl]
    have hb := hF.2 p q hpq X (-z) (neg_ne_zero.2 hz)
    rw [norm_neg] at hb
    have hpw : HRS.MS.Phase2S82.pairWeight M (X + (1 / 2 : ℝ) • -z) (X - (1 / 2 : ℝ) • -z) =
        HRS.MS.Phase2S82.pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := by
      unfold HRS.MS.Phase2S82.pairWeight
      have e1 : X + (1 / 2 : ℝ) • -z = X - (1 / 2 : ℝ) • z := by module
      have e2 : X - (1 / 2 : ℝ) • -z = X + (1 / 2 : ℝ) • z := by module
      rw [e1, e2, mul_comm]
    rw [hpw] at hb
    exact hb

end HRS.MS.R26T8A
