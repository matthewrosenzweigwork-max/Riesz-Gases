import HRS.MS.FixEqP1Aux1
import HRS.MS.SA12X2R34A

/-!
# S.A.12 R36 (SA12X2), part P0: commutation of tuple partials for `C^(n+1)` functions

`∂_v (∂^idx g) = ∂^(snoc idx v) g` for `g ∈ C^(n+1)` (no analytic hypothesis): induction on the tuple length,
with the second-order symmetry of `C^2` functions (`ContDiffAt.isSymmSndFDerivAt`) at each step.
This is the identity needed to move the top-order derivative in the R36 split.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12

open HRS HRS.Whole

variable {d : ℕ}

/-- Symmetry of the first derivatives of a `C^2` function (directional form). -/
theorem sa12x2_fderiv_swap {h : Euc d → ℝ} (hh : ContDiff ℝ 2 h) (u v x : Euc d) :
    fderiv ℝ (fun y => fderiv ℝ h y u) x v = fderiv ℝ (fun y => fderiv ℝ h y v) x u := by
  have hd1 : DifferentiableAt ℝ (fderiv ℝ h) x :=
    ((hh.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) x
  have key : ∀ w a : Euc d, fderiv ℝ (fun y => fderiv ℝ h y w) x a = fderiv ℝ (fderiv ℝ h) x a w := by
    intro w a
    rw [fderiv_clm_apply hd1 (differentiableAt_const w)]
    simp
  rw [key u v, key v u]
  have hsym := (hh.contDiffAt (x := x)).isSymmSndFDerivAt (n := 2) (by simp [minSmoothness])
  exact hsym v u

/-- Partial derivatives of order `n` of a `C^(n+k)` function are `C^k`. -/
theorem sa12x2_pd_cd {n k : ℕ} {g : Euc d → ℝ} (hg : ContDiff ℝ ((n + k : ℕ) : WithTop ℕ∞) g)
    (idx : Fin n → Fin d) : ContDiff ℝ k (partialDeriv idx g) := by
  have hT : ContDiff ℝ k (iteratedFDeriv ℝ n g) :=
    hg.iteratedFDeriv_right (m := k) (i := n) (le_of_eq (add_comm _ _))
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Euc d) ℝ
    (fun l : Fin n => EuclideanSpace.single (idx l) (1 : ℝ))).contDiff.comp hT

/-- Commutation: `∂_v ∂^idx g = ∂^(snoc idx v) g` for `g ∈ C^(n+1)`. -/
theorem sa12x2_pd_snoc (n : ℕ) : ∀ (g : Euc d → ℝ), ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) g →
    ∀ (idx : Fin n → Fin d) (v : Fin d) (x : Euc d),
      fderiv ℝ (partialDeriv idx g) x (EuclideanSpace.single v (1 : ℝ)) =
        partialDeriv (Fin.snoc idx v) g x := by
  induction n with
  | zero =>
    intro g hg idx v x
    have h0 : ∀ (i : Fin 0 → Fin d), partialDeriv i g = g := by
      intro i
      funext y
      unfold partialDeriv
      rw [iteratedFDeriv_zero_apply]
    rw [h0 idx]
    rw [HRS.MS.FixEq.s57p_partialDeriv_succ hg (Fin.snoc idx v) x, h0]
    have e0 : (Fin.snoc idx v : Fin 1 → Fin d) 0 = v := by simp [Fin.snoc]
    rw [e0]
  | succ n ih =>
    intro g hg idx v x
    have hg1 : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) g := hg.of_le (by exact_mod_cast Nat.le_succ _)
    have hidx : idx = Fin.cons (idx 0) (Fin.tail idx) := (Fin.cons_self_tail idx).symm
    have hsn : (Fin.snoc idx v : Fin (n + 2) → Fin d) = Fin.cons (idx 0) (Fin.snoc (Fin.tail idx) v) := by
      conv_lhs => rw [hidx]
      exact (Fin.cons_snoc_eq_snoc_cons (idx 0) (Fin.tail idx) v).symm
    have hfunL : partialDeriv idx g = fun y => fderiv ℝ (partialDeriv (Fin.tail idx) g) y
        (EuclideanSpace.single (idx 0) (1 : ℝ)) :=
      funext fun y => HRS.MS.FixEq.s57p_partialDeriv_succ hg1 idx y
    have hC2 : ContDiff ℝ 2 (partialDeriv (Fin.tail idx) g) := sa12x2_pd_cd (k := 2) hg _
    have hih : partialDeriv (Fin.snoc (Fin.tail idx) v) g = fun y => fderiv ℝ
        (partialDeriv (Fin.tail idx) g) y (EuclideanSpace.single v (1 : ℝ)) := by
      funext y
      exact (ih g hg1 (Fin.tail idx) v y).symm
    have htail : (fun l : Fin (n + 1) => (Fin.snoc idx v : Fin (n + 2) → Fin d) l.succ) =
        Fin.snoc (Fin.tail idx) v := by
      funext l
      rw [hsn, Fin.cons_succ]
    have hhead : (Fin.snoc idx v : Fin (n + 2) → Fin d) 0 = idx 0 := by
      rw [hsn, Fin.cons_zero]
    have hL : fderiv ℝ (partialDeriv idx g) x (EuclideanSpace.single v (1 : ℝ)) =
        fderiv ℝ (fun y => fderiv ℝ (partialDeriv (Fin.tail idx) g) y
          (EuclideanSpace.single (idx 0) (1 : ℝ))) x (EuclideanSpace.single v (1 : ℝ)) := by
      rw [hfunL]
    have hR : partialDeriv (Fin.snoc idx v) g x = fderiv ℝ (fun y => fderiv ℝ
        (partialDeriv (Fin.tail idx) g) y (EuclideanSpace.single v (1 : ℝ))) x
          (EuclideanSpace.single (idx 0) (1 : ℝ)) := by
      rw [HRS.MS.FixEq.s57p_partialDeriv_succ hg (Fin.snoc idx v) x, htail, hhead, hih]
    rw [hL, hR]
    exact sa12x2_fderiv_swap hC2 _ _ x

end HRS.MH.AdjointRd.Phase2SA12
