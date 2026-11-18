import HRS.MS.R26T8AF09a

/-!
# S8.2 observed-time layer, packet T8A.F13 (helper 13a): derivatives of a function versus its gradient

`‖∂^(k+1) f x‖ ≤ ‖∂^k (∇f) x‖` for smooth `f`, and `cbNormVecE K (∇f) ≤ X` gives pointwise bounds of the
derivatives of `f` of orders `1 ≤ k ≤ K+1`.  Used to turn the native S6.7 gradient bound into `TestBound`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

theorem r26t8a_f13a_succ_le (f : Euc d → ℝ) (hf : ContDiff ℝ ∞ f) (k : ℕ) (x : Euc d) :
    ‖iteratedFDeriv ℝ (k + 1) f x‖ ≤ ‖iteratedFDeriv ℝ k (fun y => gradient f y) x‖ := by
  set L : Euc d →L[ℝ] StrongDual ℝ (Euc d) :=
    (InnerProductSpace.toDual ℝ (Euc d)).toContinuousLinearEquiv.toContinuousLinearMap with hL
  have hfd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have e : (fderiv ℝ f) = L ∘ (fun y => gradient f y) := by
    funext y
    simp [hL, gradient]
  rw [← norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (x := x) (n := k), e]
  have hgr : ContDiff ℝ ∞ (fun y => gradient f y) := by
    have e' : (fun y => gradient f y) = fun y => (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ f y) :=
      rfl
    rw [e']
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff.comp hfd
  rw [ContinuousLinearMap.iteratedFDeriv_comp_left L hgr.contDiffAt
    (by first | simp | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le L _).trans ?_
  have hLn : ‖L‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by simp [hL]
  simpa using mul_le_mul_of_nonneg_right hLn (norm_nonneg _)

end HRS.MS.R26T8A

end
