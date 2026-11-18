import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.S67NlBD57A

/-!
# S6.7 nonlinear, packet S6.7nl.57B: step-independent iterated mean-value bound for any subset

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4842-4851 (finiteness
prerequisite), row `S:W:lem:r2mov-global-adjoint` (nonlinear part). Owned definitions: none.
Induction on the list of selected steps (outermost step first): the fold commutes with `fderiv`
(the derivative of a finite difference is the finite difference of the derivative), so the
norm mean-value inequality (`Convex.norm_image_sub_le_of_norm_fderiv_le`, no completeness needed)
applied to the inner fold, whose derivative is the fold of `fderiv u`, reduces the bound to the
same statement for `fderiv u : Euc d -> (Euc d ->L F)` with one step fewer.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

universe u

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

section Fold

variable {N : ℕ} (h : Fin N → ℝ) (e : Fin N → Euc d)

lemma s67bd57b_foldr_contDiff {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : WithTop ℕ∞} (l : List (Fin N)) (w : Euc d → F) (hw : ContDiff ℝ n w) :
    ContDiff ℝ n (l.foldr (fun i v => s67bd_diff (h i) (e i) v) w) := by
  induction l with
  | nil => simpa using hw
  | cons a l ih =>
    rw [List.foldr_cons]
    exact s67bd_diff_contDiff ih _ _

lemma s67bd57b_foldr_fderiv {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (l : List (Fin N)) (w : Euc d → F) (hw : ContDiff ℝ 1 w) :
    fderiv ℝ (l.foldr (fun i v => s67bd_diff (h i) (e i) v) w) =
      l.foldr (fun i v => s67bd_diff (h i) (e i) v) (fderiv ℝ w) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.foldr_cons, List.foldr_cons, ← ih]
    funext x
    rw [s67bd_diff_fderiv
      ((s67bd57b_foldr_contDiff h e l w hw).differentiable (by norm_num)) (h a) (e a) x]
    rfl

lemma s67bd57b_main (hh : ∀ i, h i ≠ 0) (he : ∀ i, ‖e i‖ = 1) (A : ℝ) :
    ∀ (l : List (Fin N)) {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] (w : Euc d → F),
      ContDiff ℝ (l.length : WithTop ℕ∞) w → (∀ x, ‖iteratedFDeriv ℝ l.length w x‖ ≤ A) →
      ∀ x, ‖l.foldr (fun i v => s67bd_diff (h i) (e i) v) w x‖ ≤ A := by
  intro l
  induction l with
  | nil =>
    intro F _ _ w _ hb x
    simpa [norm_iteratedFDeriv_zero] using hb x
  | cons a l ih =>
    intro F _ _ w hw hb x
    rw [List.foldr_cons]
    have hw1 : ContDiff ℝ 1 w := hw.of_le (by
      rw [List.length_cons]; exact_mod_cast Nat.le_add_left 1 l.length)
    have hfd : ContDiff ℝ (l.length : WithTop ℕ∞) (fderiv ℝ w) := by
      refine hw.fderiv_right (m := (l.length : WithTop ℕ∞)) ?_
      rw [List.length_cons]; push_cast; exact le_rfl
    have hbd : ∀ y, ‖iteratedFDeriv ℝ l.length (fderiv ℝ w) y‖ ≤ A := by
      intro y
      rw [norm_iteratedFDeriv_fderiv]
      simpa using hb y
    have hih := ih (fderiv ℝ w) hfd hbd
    set g := l.foldr (fun i v => s67bd_diff (h i) (e i) v) w with hg
    have hgc : ContDiff ℝ 1 g := s67bd57b_foldr_contDiff h e l w hw1
    have hfg : ∀ y, ‖fderiv ℝ g y‖ ≤ A := by
      intro y
      rw [hg, s67bd57b_foldr_fderiv h e l w hw1]
      exact hih y
    have hA : 0 ≤ A := (norm_nonneg _).trans (hfg 0)
    have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (f := g) (s := Set.univ)
      (fun y _ => (hgc.differentiable (by norm_num)) y) (fun y _ => hfg y) convex_univ
      (Set.mem_univ x) (Set.mem_univ (x + h a • e a))
    unfold s67bd_diff
    rw [norm_smul, norm_inv, Real.norm_eq_abs]
    have hn : ‖x + h a • e a - x‖ = |h a| := by
      rw [add_sub_cancel_left, norm_smul, he a, mul_one, Real.norm_eq_abs]
    rw [hn] at hmv
    have hpos : 0 < |h a| := abs_pos.2 (hh a)
    calc |h a|⁻¹ * ‖g (x + h a • e a) - g x‖ ≤ |h a|⁻¹ * (A * |h a|) :=
          mul_le_mul_of_nonneg_left hmv (inv_nonneg.2 hpos.le)
      _ = A := by field_simp

end Fold

lemma s67bd57b_card {N : ℕ} (S : Finset (Fin N)) :
    ((List.ofFn (fun i : Fin N => i)).filter (fun i => decide (i ∈ S))).length = S.card := by
  have hnd : ((List.ofFn (fun i : Fin N => i)).filter (fun i => decide (i ∈ S))).Nodup :=
    (List.nodup_ofFn.2 Function.injective_id).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext i
  simp

theorem s67bd_subset_mean_value {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (d n : ℕ) (h : Fin n → ℝ) (e : Fin n → Euc d)
    (hh : ∀ i, h i ≠ 0) (he : ∀ i, ‖e i‖ = 1) (S : Finset (Fin n))
    (u : Euc d → F) (hu : ContDiff ℝ (S.card : WithTop ℕ∞) u)
    (A : ℝ) (hA : 0 ≤ A) (hjet : ∀ x, ‖iteratedFDeriv ℝ S.card u x‖ ≤ A) :
    ∀ x, ‖s67bd_subsetDiff n h e S u x‖ ≤ A := by
  have hL := s67bd57b_card S
  exact s67bd57b_main h e hh he A _ u (by rw [hL]; exact hu) (by rw [hL]; exact hjet)

end HRS.MS.BreakdownS67
