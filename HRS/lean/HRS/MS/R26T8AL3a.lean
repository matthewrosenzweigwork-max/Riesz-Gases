import HRS.MS.R26T8AL2
import HRS.MS.R26T8AF05c

/-!
# S8.2 observed-time layer, generic lemma L3a: pure directional iterates of `SobSmooth` functions

`D i w = ∂_{e_i} w`, `D^[k] w` its iterates.  Facts: (1) `D^[k] f x = iteratedFDeriv k f x (const e_i)`;
(2) `D` maps `SobSmooth` to `SobSmooth` (L2); (3) squared form `sobolevNormSq k (D w) ≤ sobolevNormSq (k+1) w`
and the iterated bound `sobolevNormSq k (D^[l] v) ≤ sobolevNormSq (k+l) v`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

/-- the directional derivative `∂_{e_i}` of a function -/
def r26t8a_l3_D (i : Fin d) (w : Euc d → ℝ) : Euc d → ℝ :=
  fun x => fderiv ℝ w x (EuclideanSpace.single i (1 : ℝ))

theorem r26t8a_l3_iter_eq (i : Fin d) (f : Euc d → ℝ) (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    (r26t8a_l3_D i)^[k] f =
      fun x => iteratedFDeriv ℝ k f x (fun _ : Fin k => (EuclideanSpace.single i (1 : ℝ) : Euc d)) := by
  induction k with
  | zero =>
    funext x
    simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    funext x
    have hT : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) x :=
      (hf.differentiable_iteratedFDeriv (by
        first
        | exact_mod_cast ENat.coe_lt_top k
        | exact WithTop.coe_lt_coe.2 (ENat.coe_lt_top k)
        | exact WithTop.coe_lt_top _
        | simp)) x
    unfold r26t8a_l3_D
    rw [fderiv_continuousMultilinear_apply_const_apply hT, iteratedFDeriv_succ_apply_left]
    rfl

theorem r26t8a_l3_iter_bound (i : Fin d) (f : Euc d → ℝ) (hf : ContDiff ℝ ∞ f) (k : ℕ) (x : Euc d) :
    |(r26t8a_l3_D i)^[k] f x| ≤ ‖iteratedFDeriv ℝ k f x‖ := by
  rw [r26t8a_l3_iter_eq i f hf k]
  have h := (iteratedFDeriv ℝ k f x).le_opNorm (fun _ : Fin k => (EuclideanSpace.single i (1 : ℝ) : Euc d))
  simp only [EuclideanSpace.norm_single, norm_one, Finset.prod_const_one, mul_one] at h
  rw [Real.norm_eq_abs] at h
  exact h

theorem r26t8a_l3_sq_D (w : Euc d → ℝ) (hw : r26t8a_SobSmooth w) (i : Fin d) (n : ℕ) :
    HRS.PDE.ToolboxRd.MemSobolev (n : ℝ) (r26t8a_l3_D i w) ∧
      sobolevNormSq (n : ℝ) (r26t8a_l3_D i w) ≤ sobolevNormSq ((n : ℝ) + 1) w := by
  have hmem : HRS.PDE.ToolboxRd.MemSobolev (n : ℝ) (r26t8a_l3_D i w) := by
    have h := r26t8a_l2 hw i (n : ℝ)
    refine r26t8a_f05c_mem_of_lt_top (lt_of_le_of_lt h ?_)
    have hm : HRS.PDE.ToolboxRd.MemSobolev ((n : ℝ) + 1) w := by
      have := hw.2 (n + 1)
      push_cast at this
      exact this
    unfold sobolevNormE
    rw [if_pos hm]
    exact ENNReal.ofReal_lt_top
  refine ⟨hmem, ?_⟩
  have hm : HRS.PDE.ToolboxRd.MemSobolev ((n : ℝ) + 1) w := by
    have := hw.2 (n + 1)
    push_cast at this
    exact this
  obtain ⟨-, hF⟩ := r26t8a_l1 hw i
  unfold sobolevNormSq
  refine integral_mono_ae hmem.2 hm.2 ?_
  filter_upwards [hF] with ξ hξ
  have hξ' : fourierL2 (r26t8a_l3_D i w) ξ =
      (2 * Real.pi * Complex.I * (ξ i : ℂ)) * fourierL2 w ξ := hξ
  show wt ξ ^ (n : ℝ) * ‖fourierL2 (r26t8a_l3_D i w) ξ‖ ^ 2 ≤
    wt ξ ^ ((n : ℝ) + 1) * ‖fourierL2 w ξ‖ ^ 2
  rw [hξ']
  have hm2 := r26t8a_l2_mul_norm i ξ (fourierL2 w ξ)
  calc wt ξ ^ (n : ℝ) * ‖(2 * Real.pi * Complex.I * (ξ i : ℂ)) * fourierL2 w ξ‖ ^ 2
      ≤ wt ξ ^ (n : ℝ) * (wt ξ * ‖fourierL2 w ξ‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hm2 (Real.rpow_nonneg (wt_pos ξ).le _)
    _ = wt ξ ^ ((n : ℝ) + 1) * ‖fourierL2 w ξ‖ ^ 2 := by
        rw [Real.rpow_add (wt_pos ξ), Real.rpow_one]
        ring

theorem r26t8a_l3_sob_D (w : Euc d → ℝ) (hw : r26t8a_SobSmooth w) (i : Fin d) :
    r26t8a_SobSmooth (r26t8a_l3_D i w) := by
  refine ⟨?_, fun n => (r26t8a_l3_sq_D w hw i n).1⟩
  have hfd : ContDiff ℝ ∞ (fderiv ℝ w) := hw.1.fderiv_right (by simp)
  exact hfd.clm_apply contDiff_const

theorem r26t8a_l3_sob_iter (w : Euc d → ℝ) (hw : r26t8a_SobSmooth w) (i : Fin d) (k : ℕ) :
    r26t8a_SobSmooth ((r26t8a_l3_D i)^[k] w) := by
  induction k with
  | zero => simpa using hw
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact r26t8a_l3_sob_D _ ih i

theorem r26t8a_l3_pure_bound (v : Euc d → ℝ) (hv : r26t8a_SobSmooth v) (i : Fin d) (l : ℕ) :
    ∀ k : ℕ, sobolevNormSq (k : ℝ) ((r26t8a_l3_D i)^[l] v) ≤ sobolevNormSq ((k + l : ℕ) : ℝ) v := by
  induction l with
  | zero =>
    intro k
    simp
  | succ l ih =>
    intro k
    rw [Function.iterate_succ_apply']
    have h1 := (r26t8a_l3_sq_D _ (r26t8a_l3_sob_iter v hv i l) i k).2
    have h2 := ih (k + 1)
    have e : ((k + 1 + l : ℕ) : ℝ) = (((k + (l + 1)) : ℕ) : ℝ) := by
      congr 1
      omega
    rw [e] at h2
    push_cast at h1 h2 ⊢
    exact h1.trans (by simpa [add_assoc, add_comm, add_left_comm] using h2)

end HRS.MS.R26T8A

end
