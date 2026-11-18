import HRS.Whole.AppendixAAdjoint
import HRS.MH.AdjointRdDefs

/-!
# S.A.12 N6, part A: iterated partial derivatives of a convolution with a smooth compactly supported kernel

`sa12n_conv v G x = ∫ v(y) G(x-y) dy`.  For `G ∈ C_c^∞` and `v` locally integrable,
`∂^idx (v ⋆ G) = v ⋆ ∂^idx G` (every index tuple).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

def sa12n_conv (v G : Euc d → ℝ) (x : Euc d) : ℝ := ∫ y, v y * G (x - y)

theorem sa12n_conv_eq (v G : Euc d → ℝ) :
    sa12n_conv v G = (v ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] G) := by
  funext x
  simp [sa12n_conv, convolution_def]

/-- Left recursion for `partialDeriv`: the first index is the outer derivative. -/
theorem sa12n_pd_cons {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) {k : ℕ} (idx : Fin k → Fin d) (i : Fin d)
    (x : Euc d) :
    partialDeriv (Fin.cons i idx : Fin (k + 1) → Fin d) f x =
      fderiv ℝ (partialDeriv idx f) x (EuclideanSpace.single i (1 : ℝ)) := by
  unfold partialDeriv
  rw [iteratedFDeriv_succ_apply_left]
  have hdiff : Differentiable ℝ (iteratedFDeriv ℝ k f) :=
    hf.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_coe.2 (by exact_mod_cast ENat.coe_lt_top k))
  have hA := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Euc d) ℝ
    (fun l => EuclideanSpace.single (idx l) (1 : ℝ))).hasFDerivAt.comp x (hdiff x).hasFDerivAt
  have h1 := hA.fderiv
  have h2 : (fun x' => iteratedFDeriv ℝ k f x' (fun l => EuclideanSpace.single (idx l) (1 : ℝ))) =
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Euc d) ℝ
        (fun l => EuclideanSpace.single (idx l) (1 : ℝ))) ∘ iteratedFDeriv ℝ k f := rfl
  rw [h2, h1]
  simp [Fin.cons_zero]
  congr 1

/-- Right recursion for `partialDeriv`: the last index is the innermost derivative. -/
theorem sa12n_pd_snoc {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) {j : ℕ} (i : Fin d)
    (idx : Fin j → Fin d) (x : Euc d) :
    partialDeriv (Fin.snoc idx i : Fin (j + 1) → Fin d) f x =
      partialDeriv idx (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x := by
  unfold partialDeriv
  rw [iteratedFDeriv_succ_apply_right]
  have hcd : ContDiffAt ℝ j (fun y => fderiv ℝ f y) x :=
    ((hf.fderiv_right (m := ∞) le_rfl).of_le (by exact_mod_cast le_top)).contDiffAt
  have h := (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ) : Euc d)).iteratedFDeriv_comp_left
    (f := fun y => fderiv ℝ f y) hcd (i := j) le_rfl
  have h' := congrArg (fun A => A (fun l => EuclideanSpace.single (idx l) 1)) h
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp] at h'
  have hinit : Fin.init (fun l : Fin (j + 1) => (EuclideanSpace.single
      ((Fin.snoc idx i : Fin (j + 1) → Fin d) l) (1 : ℝ) : Euc d)) =
      fun l => EuclideanSpace.single (idx l) 1 := by
    funext l
    simp [Fin.init, Fin.snoc_castSucc]
  have hlast : (EuclideanSpace.single ((Fin.snoc idx i : Fin (j + 1) → Fin d) (Fin.last j))
      (1 : ℝ) : Euc d) = EuclideanSpace.single i 1 := by simp
  rw [hinit, hlast]
  exact h'.symm

/-- `∂^idx (v ⋆ G) = v ⋆ ∂^idx G` for `G ∈ C_c^∞`. -/
theorem sa12n_conv_partial {v G : Euc d → ℝ} (hv : LocallyIntegrable v volume)
    (hG : ContDiff ℝ ∞ G) (hGc : HasCompactSupport G) :
    ContDiff ℝ ∞ (sa12n_conv v G) ∧ ∀ {k : ℕ} (idx : Fin k → Fin d) (x : Euc d),
      partialDeriv idx (sa12n_conv v G) x = sa12n_conv v (partialDeriv idx G) x := by
  have hsm : ContDiff ℝ ∞ (sa12n_conv v G) := by
    rw [sa12n_conv_eq]
    exact hGc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hv hG
  refine ⟨hsm, ?_⟩
  intro k
  induction k with
  | zero =>
    intro idx x
    have h0 : ∀ f : Euc d → ℝ, partialDeriv idx f = f := fun f => funext fun y => by
      simp [partialDeriv]
    rw [h0, h0]
  | succ k ih =>
    intro idx x
    rw [← Fin.cons_self_tail idx, sa12n_pd_cons hsm (Fin.tail idx) (idx 0) x]
    have hfun : partialDeriv (Fin.tail idx) (sa12n_conv v G) =
        sa12n_conv v (partialDeriv (Fin.tail idx) G) := funext (ih (Fin.tail idx))
    rw [hfun]
    have hP : ContDiff ℝ ∞ (partialDeriv (Fin.tail idx) G) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Euc d) ℝ
        (fun l => EuclideanSpace.single (Fin.tail idx l) (1 : ℝ))).contDiff.comp
        (hG.iteratedFDeriv_right (by simp))
    have hPc : HasCompactSupport (partialDeriv (Fin.tail idx) G) :=
      (hGc.iteratedFDeriv (𝕜 := ℝ) k).comp_left (g := fun A : (Euc d) [×k]→L[ℝ] ℝ =>
        A (fun l => EuclideanSpace.single (Fin.tail idx l) (1 : ℝ))) (by simp)
    have hder := hPc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hv
      (hP.of_le (by exact_mod_cast le_top)) x
    have hex : ConvolutionExistsAt v (fderiv ℝ (partialDeriv (Fin.tail idx) G)) x
        ((ContinuousLinearMap.mul ℝ ℝ).precompR (Euc d)) volume :=
      (hPc.fderiv (𝕜 := ℝ)).convolutionExists_right _ hv
        (hP.continuous_fderiv (by simp)) x
    rw [sa12n_conv_eq v (partialDeriv (Fin.tail idx) G), hder.fderiv, convolution_def,
      ContinuousLinearMap.integral_apply hex]
    unfold sa12n_conv
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [sa12n_pd_cons hG (Fin.tail idx) (idx 0) (x - y)]
    simp

end HRS.MH.AdjointRd.Phase2SA12Near
