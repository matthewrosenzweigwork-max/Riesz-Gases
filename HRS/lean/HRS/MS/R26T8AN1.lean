import HRS.MS.R26T8AP07q
import HRS.MS.R26T8APot3

/-!
# S8.2 local Newton layer, smooth part (N), step 1: nested jets of a convolution with the signed Newton kernel
`r26t8a_N1_conv_contDiff`: `(Y,w) |-> ∫ K(u) S(Y, w-u) du` is `C^n` for a locally integrable `K`.
`r26t8a_N1_conv_nest`: for the Newton kernel `K` (changes sign for `d = 2`), `‖nest p q (conv K S) X z‖ <= B ∫_{ball ρ} |K|`, by the
splitting `K = K^+ - K^-` and the nonnegative-kernel bound `r26t8a_near_conv`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric Convolution
open scoped ContDiff
open HRS HRS.Whole HRS.MS.Phase2S82

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_N1_conv_contDiff {K : Euc d → ℝ} (hK : LocallyIntegrable K (volume : Measure (Euc d))) {n : ℕ}
    {S : Euc d × Euc d → ℝ} (hS : ContDiff ℝ (n : WithTop ℕ∞) S) (R0 : ℝ)
    (hSv : ∀ Y w : Euc d, R0 < ‖w‖ → S (Y, w) = 0) :
    ContDiff ℝ (n : WithTop ℕ∞) (fun Yw : Euc d × Euc d => ∫ u, K u * S (Yw.1, Yw.2 - u)) := by
  have hvan : ∀ (Y : Euc d), ∀ x : Euc d, Y ∈ (Set.univ : Set (Euc d)) → x ∉ closedBall (0 : Euc d) R0 →
      (fun Y x => S (Y, x)) Y x = 0 := by
    intro Y x _ hx
    rw [mem_closedBall, dist_zero_right, not_le] at hx
    exact hSv Y x hx
  have hconv := contDiffOn_convolution_right_with_param (𝕜 := ℝ) (μ := (volume : Measure (Euc d)))
    (n := (n : ℕ∞)) (ContinuousLinearMap.mul ℝ ℝ) (f := K) (g := fun Y x : Euc d => S (Y, x))
    (s := Set.univ) (k := closedBall (0 : Euc d) R0) isOpen_univ (isCompact_closedBall _ _) hvan hK
    (by
      have : ContDiff ℝ (n : ℕ∞) (Function.uncurry fun Y x : Euc d => S (Y, x)) := by exact_mod_cast hS
      exact this.contDiffOn)
  have hcd : ContDiff ℝ (n : ℕ∞)
      (fun q : Euc d × Euc d => (K ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (fun x : Euc d => S (q.1, x))) q.2) := by
    rw [← contDiffOn_univ]
    simpa using hconv
  have heq : (fun Yw : Euc d × Euc d => ∫ u, K u * S (Yw.1, Yw.2 - u)) =
      fun q : Euc d × Euc d => (K ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (fun x : Euc d => S (q.1, x))) q.2 := by
    funext q
    rw [convolution_def]
    rfl
  rw [heq]
  exact_mod_cast hcd

theorem r26t8a_N1_nest_neg (p q : ℕ) (f : Euc d × Euc d → ℝ) (X z : Euc d) :
    ‖r26t8a_nest p q (fun Yw => -f Yw) X z‖ = ‖r26t8a_nest p q f X z‖ := by
  unfold r26t8a_nest
  have h1 : (fun Y => iteratedFDeriv ℝ q (fun w => -f (Y, w)) z) =
      -(fun Y => iteratedFDeriv ℝ q (fun w => f (Y, w)) z) := by
    funext Y
    have := iteratedFDeriv_neg_apply (𝕜 := ℝ) (i := q) (f := fun w => f (Y, w)) (x := z)
    exact this
  rw [h1, iteratedFDeriv_neg_apply, norm_neg]

end HRS.MS.R26T8A
