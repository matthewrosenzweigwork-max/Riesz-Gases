import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.S67NlBD55

/-!
# S6.7 nonlinear, packet S6.7nl.56: mixed-difference PDE and finite fixed-step top gradient

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4844-4851 (finiteness
prerequisite), row `S:W:lem:r2mov-global-adjoint` (nonlinear part). Owned definitions:
`s67bd_mixedDiff`, `s67bd_commutator`.
Induction on the number of steps (the foldr peels the first step): each stage applies
`s67bd_difference_pde` to the previous stage, and the resulting residual is identified with the
literal commutator by the discrete product rule for the drift term. The gradient bound is the
inherited `C^2` bound of the final data at order one.
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

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

def s67bd_mixedDiff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (h : Fin n → ℝ) (e : Fin n → Euc d) (u : Euc d → F) : Euc d → F :=
  (List.ofFn (fun i => (h i, e i))).foldr (fun p v => s67bd_diff p.1 p.2 v) u

def s67bd_commutator (q : ℝ) (n : ℕ) (h : Fin n → ℝ) (e : Fin n → Euc d)
    (B : Euc d → Euc d) (J u : Euc d → ℝ) (x : Euc d) : ℝ :=
  s67bd_mixedDiff n h e
    (fun y => inner ℝ ((-q) • y + B y) (gradient u y) + J y) x -
    inner ℝ ((-q) • x + B x) (gradient (s67bd_mixedDiff n h e u) x)

lemma s67bd_mixedDiff_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : Fin 0 → ℝ) (e : Fin 0 → Euc d) (u : Euc d → F) : s67bd_mixedDiff 0 h e u = u := by
  simp [s67bd_mixedDiff]

lemma s67bd_mixedDiff_succ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (h : Fin (n + 1) → ℝ) (e : Fin (n + 1) → Euc d) (u : Euc d → F) :
    s67bd_mixedDiff (n + 1) h e u =
      s67bd_diff (h 0) (e 0) (s67bd_mixedDiff n (fun i => h i.succ) (fun i => e i.succ) u) := by
  simp [s67bd_mixedDiff, List.ofFn_succ]

lemma s67bd_diff_sub (h : ℝ) (e : Euc d) (M F : Euc d → ℝ) (x : Euc d) :
    s67bd_diff h e (fun y => M y - F y) x = s67bd_diff h e M x - s67bd_diff h e F x := by
  unfold s67bd_diff
  simp only [smul_eq_mul]
  ring

lemma s67bd_diff_drift {w : Euc d → ℝ} (hw : Differentiable ℝ w) (q h : ℝ) (hh : h ≠ 0)
    (e : Euc d) (B : Euc d → Euc d) (x : Euc d) :
    s67bd_diff h e (fun y => inner ℝ ((-q) • y + B y) (gradient w y)) x =
      inner ℝ ((-q) • x + B x) (gradient (s67bd_diff h e w) x) +
      inner ℝ (s67bd_diff h e B x) (gradient w (x + h • e)) -
      q * inner ℝ e (gradient w (x + h • e)) := by
  rw [s67bd_diff_gradient hw]
  simp only [s67bd_diff, inner_add_left, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, inner_neg_left, RCLike.conj_to_real, smul_eq_mul, smul_add, smul_sub,
    inner_add_right]
  field_simp
  ring

lemma s67bd_gradient_norm56 (f : Euc d → ℝ) (y : Euc d) :
    ‖gradient f y‖ = ‖fderiv ℝ f y‖ := by
  unfold gradient
  exact LinearIsometryEquiv.norm_map _ _

lemma s67bd_PD_congr_J {ν q T : ℝ} {u a : ℝ → Euc d → ℝ} {B : ℝ → Euc d → Euc d}
    {J J' : ℝ → Euc d → ℝ} (hP : s67bd_ParabolicData ν q T u a B J)
    (hJ : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, J t x = J' t x) : s67bd_ParabolicData ν q T u a B J' where
  c2 := hP.c2
  bdd_c2 := hP.bdd_c2
  cont_c2 := hP.cont_c2
  acont := hP.acont
  agrow := hP.agrow
  Bcont := hP.Bcont
  Jcont := hP.Jcont.congr (fun p hp => (hJ p.1 hp.1 p.2).symm)
  hint := hP.hint
  equation := fun t ht x => by rw [← hJ t ht x]; exact hP.equation t ht x

theorem s67bd_mixed_difference_pde (ν q T : ℝ)
    (u a : ℝ → Euc d → ℝ) (B : ℝ → Euc d → Euc d) (J : ℝ → Euc d → ℝ)
    (hu : s67bd_ParabolicData ν q T u a B J)
    (n : ℕ) (h : Fin n → ℝ) (e : Fin n → Euc d)
    (hh : ∀ i, h i ≠ 0) (he : ∀ i, ‖e i‖ = 1) :
    s67bd_ParabolicData ν q T (fun t => s67bd_mixedDiff n h e (u t))
      (fun t => s67bd_mixedDiff n h e (a t)) B
      (fun t => s67bd_commutator q n h e (B t) (J t) (u t)) ∧
    ∃ A : ℝ, ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      ‖gradient (s67bd_mixedDiff n h e (u t)) x‖ ≤ A := by
  have main : ∀ (n : ℕ) (h : Fin n → ℝ) (e : Fin n → Euc d), (∀ i, h i ≠ 0) → (∀ i, ‖e i‖ = 1) →
      s67bd_ParabolicData ν q T (fun t => s67bd_mixedDiff n h e (u t))
        (fun t => s67bd_mixedDiff n h e (a t)) B
        (fun t => s67bd_commutator q n h e (B t) (J t) (u t)) := by
    intro n
    induction n with
    | zero =>
      intro h e _ _
      have e0 : (fun t => s67bd_mixedDiff 0 h e (u t)) = u := by
        funext t; exact s67bd_mixedDiff_zero h e (u t)
      have e1 : (fun t => s67bd_mixedDiff 0 h e (a t)) = a := by
        funext t; exact s67bd_mixedDiff_zero h e (a t)
      rw [e0, e1]
      refine s67bd_PD_congr_J hu (fun t _ x => ?_)
      unfold s67bd_commutator
      rw [s67bd_mixedDiff_zero, s67bd_mixedDiff_zero]
      ring
    | succ n ih =>
      intro h e hh he
      have hprev := ih (fun i => h i.succ) (fun i => e i.succ) (fun i => hh _) (fun i => he _)
      have hstep := s67bd_difference_pde ν q T _ _ B _ hprev (h 0) (hh 0) (e 0) (he 0)
      have e0 : (fun t => s67bd_mixedDiff (n + 1) h e (u t)) = fun t => s67bd_diff (h 0) (e 0)
          (s67bd_mixedDiff n (fun i => h i.succ) (fun i => e i.succ) (u t)) := by
        funext t; exact s67bd_mixedDiff_succ n h e (u t)
      have e1 : (fun t => s67bd_mixedDiff (n + 1) h e (a t)) = fun t => s67bd_diff (h 0) (e 0)
          (s67bd_mixedDiff n (fun i => h i.succ) (fun i => e i.succ) (a t)) := by
        funext t; exact s67bd_mixedDiff_succ n h e (a t)
      rw [e0, e1]
      refine s67bd_PD_congr_J hstep (fun t ht x => ?_)
      have hd : Differentiable ℝ (s67bd_mixedDiff n (fun i => h i.succ) (fun i => e i.succ) (u t)) :=
        ((hprev.c2 t ht).differentiable (by norm_num))
      have hprod := s67bd_diff_drift hd q (h 0) (hh 0) (e 0) (B t) x
      set Mn := s67bd_mixedDiff n (fun i => h i.succ) (fun i => e i.succ)
        (fun y => inner ℝ ((-q) • y + B t y) (gradient (u t) y) + J t y) with hMn
      set Fn : Euc d → ℝ := fun y => inner ℝ ((-q) • y + B t y)
        (gradient (s67bd_mixedDiff n (fun i => h i.succ) (fun i => e i.succ) (u t)) y) with hFn
      have hC : s67bd_commutator q n (fun i => h i.succ) (fun i => e i.succ) (B t) (J t) (u t) =
          fun y => Mn y - Fn y := rfl
      have hsub := s67bd_diff_sub (h 0) (e 0) Mn Fn x
      show s67bd_diff (h 0) (e 0)
          (s67bd_commutator q n (fun i => h i.succ) (fun i => e i.succ) (B t) (J t) (u t)) x +
          inner ℝ (s67bd_diff (h 0) (e 0) (B t) x)
            (gradient (s67bd_mixedDiff n (fun i => h i.succ) (fun i => e i.succ) (u t))
              (x + h 0 • e 0)) -
          q * inner ℝ (e 0) (gradient (s67bd_mixedDiff n (fun i => h i.succ) (fun i => e i.succ)
            (u t)) (x + h 0 • e 0)) = s67bd_commutator q (n + 1) h e (B t) (J t) (u t) x
      rw [hC, hsub]
      unfold s67bd_commutator
      rw [s67bd_mixedDiff_succ, s67bd_mixedDiff_succ]
      have hprod' : s67bd_diff (h 0) (e 0) Fn x = _ := hprod
      simp only [hMn, hFn] at hprod' ⊢
      linarith
  refine ⟨main n h e hh he, ?_⟩
  obtain ⟨K, hK⟩ := (main n h e hh he).bdd_c2
  refine ⟨K, fun t ht x => ?_⟩
  rw [s67bd_gradient_norm56, ← norm_iteratedFDeriv_one (𝕜 := ℝ)]
  exact hK t ht 1 (by norm_num) x

end HRS.MS.BreakdownS67
