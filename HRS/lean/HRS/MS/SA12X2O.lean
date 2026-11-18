import HRS.MS.SA12X2N
import HRS.MS.SA12Z3NearN7H

/-!
# S.A.12 N8 (SA12X2), part O: jets of partial derivatives and the recursion of the Leibniz remainder

* `sa12x2_jet`: `‖D^k ∂^t g‖ ≤ ‖D^{k+|t|} g‖`;
* `sa12x2_Rj_cons`: `R_j(l::t) = ∂_l R_j(t) + (∂_l a) ∂_j ∂^t F`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

theorem sa12x2_norm_D1 {G : Euc d → ℝ} (hG : ContDiff ℝ ∞ G) (p : Fin d) (k : ℕ) (y : Euc d) :
    ‖iteratedFDeriv ℝ k (D1 p G) y‖ ≤ ‖iteratedFDeriv ℝ (k + 1) G y‖ := by
  set Lp : (Euc d →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single p (1 : ℝ))
  have hL : ‖Lp‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun L => ?_)
    have := L.le_opNorm (EuclideanSpace.single p (1 : ℝ))
    simpa [Lp, PiLp.norm_single] using this
  have hf : ContDiff ℝ ∞ (fderiv ℝ G) := hG.fderiv_right (m := ∞) (by simp)
  have e : D1 p G = Lp ∘ fderiv ℝ G := rfl
  rw [e]
  refine (Lp.norm_iteratedFDeriv_comp_left (N := ∞) hf.contDiffAt (by exact_mod_cast le_top)).trans ?_
  rw [← norm_iteratedFDeriv_fderiv]
  calc ‖Lp‖ * ‖iteratedFDeriv ℝ k (fderiv ℝ G) y‖ ≤ 1 * ‖iteratedFDeriv ℝ k (fderiv ℝ G) y‖ :=
        mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    _ = _ := one_mul _

theorem sa12x2_jet {g : Euc d → ℝ} (hg : ContDiff ℝ ∞ g) :
    ∀ (s k : ℕ) (t : Fin s → Fin d) (y : Euc d),
      ‖iteratedFDeriv ℝ k (partialDeriv t g) y‖ ≤ ‖iteratedFDeriv ℝ (k + s) g y‖ := by
  intro s
  induction s with
  | zero =>
    intro k t y
    simp only [sa12z3_pd_zero_fun, Nat.add_zero]
    exact le_rfl
  | succ s ih =>
    intro k t y
    obtain ⟨p, t', rfl⟩ : ∃ p t', t = (Fin.cons p t' : Fin (s + 1) → Fin d) :=
      ⟨t 0, Fin.tail t, (Fin.cons_self_tail t).symm⟩
    have e : partialDeriv (Fin.cons p t' : Fin (s + 1) → Fin d) g = D1 p (partialDeriv t' g) :=
      funext fun z => sa12z3_pd_cons t' p (sa12z3_cd_of_inf hg _) z
    rw [e]
    refine (sa12x2_norm_D1 (sa12z3_pd_contDiff_inf hg t') p k y).trans ?_
    have := ih (k + 1) t' y
    rw [show k + (s + 1) = k + 1 + s by ring]
    exact this


theorem sa12x2_D1_sub_mul {P a K : Euc d → ℝ} (l : Fin d) (y : Euc d) (hP : DifferentiableAt ℝ P y)
    (ha : DifferentiableAt ℝ a y) (hK : DifferentiableAt ℝ K y) :
    D1 l (fun z => P z - a z * K z) y = D1 l P y - (D1 l a y * K y + a y * D1 l K y) := by
  have h1 : HasFDerivAt (fun z => a z * K z) (a y • fderiv ℝ K y + K y • fderiv ℝ a y) y :=
    ha.hasFDerivAt.mul hK.hasFDerivAt
  have h2 := hP.hasFDerivAt.fun_sub h1
  unfold D1
  rw [h2.fderiv]
  simp
  ring

theorem sa12x2_Rj_cons {m n : ℕ} (hn : n + 1 ≤ m) {a F : Euc d → ℝ} (ha : ContDiff ℝ (m + 1) a)
    (hF : ContDiff ℝ ∞ F) (j l : Fin d) (t : Fin n → Fin d) (y : Euc d) :
    sa12z3_Rj a F (Fin.cons l t : Fin (n + 1) → Fin d) j y =
      D1 l (sa12z3_Rj a F t j) y + D1 l a y * D1 j (partialDeriv t F) y := by
  have hH : ContDiff ℝ ∞ (D1 j F) := (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have han : ContDiff ℝ (n + 1) a := ha.of_le (by exact_mod_cast (by omega : n + 1 ≤ m + 1))
  have haH : ContDiff ℝ (n + 1) (fun z => a z * D1 j F z) := han.mul (sa12z3_cd_of_inf hH _)
  have hG : ContDiff ℝ ∞ (partialDeriv t F) := sa12z3_pd_contDiff_inf hF t
  have hP1 : ContDiff ℝ 1 (partialDeriv t (fun z => a z * D1 j F z)) := by
    have := sa12z3_pd_contDiff (k := n + 1) (n := n) haH (by omega) t
    simpa using this
  have hK : ContDiff ℝ ∞ (D1 j (partialDeriv t F)) :=
    (hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have ha1 : ContDiff ℝ 1 a := ha.of_le (by exact_mod_cast (by omega : 1 ≤ m + 1))
  have hcomm : D1 j (D1 l (partialDeriv t F)) y = D1 l (D1 j (partialDeriv t F)) y :=
    HRS.MS.UniqN3c.n3c_hess_symm (sa12z3_cd_of_inf hG 2) l j y
  have e1 : partialDeriv (Fin.cons l t : Fin (n + 1) → Fin d) F = D1 l (partialDeriv t F) :=
    funext fun z => sa12z3_pd_cons t l (sa12z3_cd_of_inf hF _) z
  unfold sa12z3_Rj
  rw [sa12z3_pd_cons t l haH y, e1]
  have e2 : (fun y' => partialDeriv t (fun y'' => a y'' * D1 j F y'') y' -
      a y' * D1 j (partialDeriv t F) y') = fun z => partialDeriv t (fun y'' => a y'' * D1 j F y'') z -
      a z * D1 j (partialDeriv t F) z := rfl
  have := sa12x2_D1_sub_mul (P := partialDeriv t (fun y'' => a y'' * D1 j F y'')) (a := a)
    (K := D1 j (partialDeriv t F)) l y (hP1.differentiable one_ne_zero y) (ha1.differentiable one_ne_zero y)
    ((hK.of_le (by exact_mod_cast le_top)).differentiable one_ne_zero y)
  rw [this, hcomm]
  ring

end HRS.MH.AdjointRd.Phase2SA12Near
