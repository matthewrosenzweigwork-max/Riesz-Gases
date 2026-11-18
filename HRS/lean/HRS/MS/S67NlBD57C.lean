import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.S67NlBD55
import HRS.MS.S67NlBD56
import HRS.MS.S67NlBD57A

/-!
# S6.7 nonlinear, packet S6.7nl.57C: commutation of actual gradients and mixed/subset differences

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_` (local helpers `s67bd57c_`). TeX
S:4842-4851, nonlinear part of `S:W:lem:r2mov-global-adjoint`. No owned definitions.
Route: a single difference step commutes with the gradient (`s67bd_diff_gradient`, which needs only
differentiability and is proved in `HRS.MS.S67NlBD55`); the finite fold is handled by induction on
the list of steps, with the regularity of the inner function supplied at each stage by
`ContDiff` preservation under differences. The full fold uses the list `List.ofFn`, the subset fold
a filtered sublist of length at most `n`, so `u ∈ C^(n+1)` suffices for both.
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

theorem s67bd57c_foldr_contDiff {ι : Type*} (ρ : ι → ℝ) (ε : ι → Euc d) (L : List ι)
    (k : WithTop ℕ∞) (u : Euc d → ℝ) (hu : ContDiff ℝ k u) :
    ContDiff ℝ k (L.foldr (fun j v => s67bd_diff (ρ j) (ε j) v) u) := by
  induction L with
  | nil => simpa using hu
  | cons j L ih => rw [List.foldr_cons]; exact s67bd_diff_contDiff ih (ρ j) (ε j)

theorem s67bd57c_foldr_gradient {ι : Type*} (ρ : ι → ℝ) (ε : ι → Euc d) (L : List ι) :
    ∀ (u : Euc d → ℝ), ContDiff ℝ ((L.length + 1 : ℕ) : WithTop ℕ∞) u → ∀ x : Euc d,
      gradient (L.foldr (fun j v => s67bd_diff (ρ j) (ε j) v) u) x =
        L.foldr (fun j v => s67bd_diff (ρ j) (ε j) v) (fun y => gradient u y) x := by
  induction L with
  | nil => intro u _ x; simp
  | cons j L ih =>
    intro u hu x
    have hu' : ContDiff ℝ ((L.length + 1 + 1 : ℕ) : WithTop ℕ∞) u := by
      simpa [List.length_cons] using hu
    have hWc := s67bd57c_foldr_contDiff ρ ε L _ u hu'
    have hWd : Differentiable ℝ (L.foldr (fun j v => s67bd_diff (ρ j) (ε j) v) u) :=
      hWc.differentiable (by simp)
    have hu'' : ContDiff ℝ ((L.length + 1 : ℕ) : WithTop ℕ∞) u :=
      hu'.of_le (by exact_mod_cast Nat.le_succ _)
    have hfun : (fun y => gradient (L.foldr (fun j v => s67bd_diff (ρ j) (ε j) v) u) y) =
        L.foldr (fun j v => s67bd_diff (ρ j) (ε j) v) (fun y => gradient u y) :=
      funext (ih u hu'')
    simp only [List.foldr_cons]
    rw [s67bd_diff_gradient hWd (ρ j) (ε j) x]
    have h1 : gradient (L.foldr (fun j v => s67bd_diff (ρ j) (ε j) v) u) (x + ρ j • ε j) =
        (L.foldr (fun j v => s67bd_diff (ρ j) (ε j) v) (fun y => gradient u y)) (x + ρ j • ε j) :=
      congrFun hfun _
    have h2 : gradient (L.foldr (fun j v => s67bd_diff (ρ j) (ε j) v) u) x =
        (L.foldr (fun j v => s67bd_diff (ρ j) (ε j) v) (fun y => gradient u y)) x :=
      congrFun hfun _
    rw [h1, h2]
    rfl

theorem s67bd_mixed_gradient (d n : ℕ) (h : Fin n → ℝ) (e : Fin n → Euc d)
    (hh : ∀ i, h i ≠ 0) (u : Euc d → ℝ)
    (hu : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) u) :
    (∀ x, gradient (s67bd_mixedDiff n h e u) x =
      s67bd_mixedDiff n h e (fun y => gradient u y) x) ∧
    ∀ (S : Finset (Fin n)) (x : Euc d), gradient (s67bd_subsetDiff n h e S u) x =
      s67bd_subsetDiff n h e S (fun y => gradient u y) x := by
  constructor
  · intro x
    unfold s67bd_mixedDiff
    refine s67bd57c_foldr_gradient (ι := ℝ × Euc d) Prod.fst Prod.snd
      (List.ofFn fun i => (h i, e i)) u ?_ x
    rw [List.length_ofFn]
    exact hu
  · intro S x
    unfold s67bd_subsetDiff
    have hlen : ((List.ofFn fun i : Fin n => i).filter fun i => decide (i ∈ S)).length ≤ n :=
      (List.length_filter_le _ _).trans (by simp)
    refine s67bd57c_foldr_gradient (ι := Fin n) h e _ u ?_ x
    exact hu.of_le (by exact_mod_cast Nat.add_le_add_right hlen 1)

end HRS.MS.BreakdownS67
