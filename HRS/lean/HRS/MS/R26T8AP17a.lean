import HRS.MS.R26T8AP22
import HRS.Kernel.SymbolClass

/-!
# S8.2 local Newton layer, packet T8A.P17 (part a): jets of the Riesz force kernel
`g(x) = |x|^(-s)`, `s = criticalS d = d/2`. `r26t8a_p17_force_jets`: `‖D^j (fderiv g) z‖ <= C |z|^(-s-1-j)` for `z != 0`
(`‖D^j (fderiv g)‖ = ‖D^(j+1) g‖` and `HRS.norm_iteratedFDeriv_rpow_norm_le`).
`r26t8a_p17_rk_eq`: `rieszKernel d (criticalS d) = fun x => ‖x‖^(-criticalS d)` (as `criticalS d > 0`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open HRS HRS.Whole HRS.MS.Phase2S82

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_p17_s_pos (hd : 2 ≤ d) : 0 < criticalS d := by
  unfold criticalS
  have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  positivity

theorem r26t8a_p17_rk_eq (hd : 2 ≤ d) : rieszKernel d (criticalS d) = fun x : Euc d => ‖x‖ ^ (-criticalS d) := by
  funext x
  simp [rieszKernel, (r26t8a_p17_s_pos hd).ne']

theorem r26t8a_p17_force_jets (hd : 2 ≤ d) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j ≤ k, ∀ z : Euc d, z ≠ 0 →
      ‖iteratedFDeriv ℝ j (fderiv ℝ (fun x : Euc d => ‖x‖ ^ (-criticalS d))) z‖ ≤
        C * ‖z‖ ^ (-criticalS d - 1 - j) := by
  choose Cj hCj0 hCj using fun j : ℕ => HRS.norm_iteratedFDeriv_rpow_norm_le (V := Euc d) (-criticalS d) j
  refine ⟨∑ j ∈ Finset.range (k + 2), Cj j, Finset.sum_nonneg fun j _ => hCj0 j, fun j hj z hz => ?_⟩
  rw [norm_iteratedFDeriv_fderiv]
  have h1 := hCj (j + 1) z hz
  have h2 : Cj (j + 1) ≤ ∑ j ∈ Finset.range (k + 2), Cj j :=
    Finset.single_le_sum (f := Cj) (fun j _ => hCj0 j) (Finset.mem_range.2 (by omega))
  refine h1.trans ?_
  have hfac : 0 ≤ ‖z‖ ^ (-criticalS d - ((j + 1 : ℕ) : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  have e : -criticalS d - ((j + 1 : ℕ) : ℝ) = -criticalS d - 1 - j := by push_cast; ring
  rw [e] at hfac ⊢
  exact mul_le_mul_of_nonneg_right h2 hfac

end HRS.MS.R26T8A
