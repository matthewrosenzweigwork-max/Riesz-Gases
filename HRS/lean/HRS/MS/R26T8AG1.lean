import HRS.MS.R26T8AQ4
import HRS.MS.R26T8AP11lb

/-!
# S8.2 sigma<0 assembly (G), step 1: linearity and extensionality of `Conormal`
`r26t8a_conormal_add`: sums of conormal functions are conormal (nested jets are linear off the diagonal, via the cutoff `psiCut`).
`r26t8a_conormal_congr`: `Conormal` only depends on the values off the diagonal.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_conormal_congr {k b : ℕ} {M σ A : ℝ} {f g : Euc d → Euc d → ℝ}
    (h : ∀ x y : Euc d, x ≠ y → f x y = g x y) (hf : Conormal k b M σ A f) : Conormal k b M σ A g := by
  refine And.intro (hf.1.congr fun p hp => (h p.1 p.2 hp).symm) fun p q hpq X z hz => ?_
  have : mixedJet p q g X z = mixedJet p q f X z := by
    show r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair g Yw.1 Yw.2) X z =
      r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair f Yw.1 Yw.2) X z
    refine r26t8a_nest_congr p q _ _ (fun Y w hw => ?_) X z hz
    unfold midPair
    refine (h _ _ ?_).symm
    intro hxy
    apply hw
    have e : (Y + (1 / 2 : ℝ) • w) - (Y - (1 / 2 : ℝ) • w) = w := by module
    rw [← e, hxy, sub_self]
  rw [this]
  exact hf.2 p q hpq X z hz

theorem r26t8a_conormal_add {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {k b : ℕ} {M σ A A' : ℝ}
    {f g : Euc d → Euc d → ℝ} (hf : Conormal k b M σ A f) (hg : Conormal k b M σ A' g) :
    Conormal k b M σ (A + A') (fun x y => f x y + g x y) := by
  refine And.intro (hf.1.add hg.1) fun p q hpq X z hz => ?_
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  set R : ℝ := 2 * ‖z‖ with hR
  have hRpos : 0 < R := by rw [hR]; positivity
  have hΨf : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞)
      (fun Yw : Euc d × Euc d => r26t8a_psiCut chi R Yw.2 * midPair f Yw.1 Yw.2) :=
    (r26t8a_gtilde_contDiff hchi hRpos hf.1).of_le (by exact_mod_cast hpq)
  have hΨg : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞)
      (fun Yw : Euc d × Euc d => r26t8a_psiCut chi R Yw.2 * midPair g Yw.1 Yw.2) :=
    (r26t8a_gtilde_contDiff hchi hRpos hg.1).of_le (by exact_mod_cast hpq)
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
  refine (norm_add_le _ _).trans ?_
  have h1 := hf.2 p q hpq X z hz
  have h2 := hg.2 p q hpq X z hz
  refine (add_le_add h1 h2).trans (le_of_eq ?_)
  ring

end HRS.MS.R26T8A
