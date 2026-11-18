import HRS.MS.SA12X2R36P0

/-!
# S.A.12 R36 (SA12X2), part Q1: right peel and the top-order identity

`∂^{snoc idx v} g = ∂^{idx}(∂_v g)` (right peel), linearity of tuple partials, and the identity
`∂^{idx}(a ∂_jF) = ∂_j(∂^{idx}(aF)) − ∂^{idx}(F ∂_j a)` used to split the top-order pairing.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12

open HRS HRS.Whole

variable {d : ℕ}

theorem sa12x2_le_top (n : ℕ) : ((n : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast le_top

/-- Right peel: the last index acts on the function inside. -/
theorem sa12x2_pd_right {n : ℕ} (g : Euc d → ℝ) (hg : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) g)
    (idx : Fin n → Fin d) (v : Fin d) (x : Euc d) :
    partialDeriv (Fin.snoc idx v) g x =
      partialDeriv idx (fun y => fderiv ℝ g y (EuclideanSpace.single v (1 : ℝ))) x := by
  have hfd : ContDiffAt ℝ n (fun y => fderiv ℝ g y) x :=
    (hg.fderiv_right (m := n) (by exact_mod_cast le_refl _)).contDiffAt
  have hcomp : (fun y => fderiv ℝ g y (EuclideanSpace.single v (1 : ℝ))) =
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single v (1 : ℝ))) ∘ (fun y => fderiv ℝ g y) :=
    rfl
  have hinit : (Fin.init fun l : Fin (n + 1) =>
      (EuclideanSpace.single ((Fin.snoc idx v : Fin (n + 1) → Fin d) l) (1 : ℝ) : Euc d)) =
      fun l => EuclideanSpace.single (idx l) (1 : ℝ) := by
    funext l
    simp [Fin.init, Fin.snoc_castSucc]
  have hlast : (EuclideanSpace.single ((Fin.snoc idx v : Fin (n + 1) → Fin d) (Fin.last n)) (1 : ℝ) : Euc d) =
      EuclideanSpace.single v (1 : ℝ) := by
    simp
  unfold partialDeriv
  rw [iteratedFDeriv_succ_apply_right, hcomp,
    ContinuousLinearMap.iteratedFDeriv_comp_left (i := n) _ hfd (by exact_mod_cast le_refl n),
    hinit, hlast]
  simp

/-- Linearity of tuple partials (both functions `C^n`). -/
theorem sa12x2_pd_sub {n : ℕ} {f h : Euc d → ℝ} (hf : ContDiff ℝ n f) (hh : ContDiff ℝ n h)
    (idx : Fin n → Fin d) (x : Euc d) :
    partialDeriv idx (fun y => f y - h y) x = partialDeriv idx f x - partialDeriv idx h x := by
  unfold partialDeriv
  have e : (fun y => f y - h y) = f - h := rfl
  rw [e, iteratedFDeriv_sub_apply (hf.contDiffAt) (hh.contDiffAt)]
  simp

/-- The top-order identity `∂^idx(a∂_jF) = ∂_j(∂^idx(aF)) − ∂^idx(F∂_ja)` (pointwise). -/
theorem sa12x2_Q_identity {m : ℕ} {a F : Euc d → ℝ} (ha : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) a)
    (hF : ContDiff ℝ ∞ F) {n : ℕ} (hn : n ≤ m) (idx : Fin n → Fin d) (j : Fin d) (x : Euc d) :
    partialDeriv idx (fun y => a y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))) x =
      fderiv ℝ (partialDeriv idx (fun y => a y * F y)) x (EuclideanSpace.single j (1 : ℝ)) -
        partialDeriv idx (fun y => F y * fderiv ℝ a y (EuclideanSpace.single j (1 : ℝ))) x := by
  have haF : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (fun y => a y * F y) := by
    refine ContDiff.mul ?_ ?_
    · exact ha.of_le (by exact_mod_cast (show n + 1 ≤ m + 1 by omega))
    · exact hF.of_le (sa12x2_le_top _)
  have hF' : ContDiff ℝ n F := hF.of_le (sa12x2_le_top _)
  have hda : ContDiff ℝ n (fun y => fderiv ℝ a y (EuclideanSpace.single j (1 : ℝ))) := by
    have h1 : ContDiff ℝ m (fderiv ℝ a) :=
      ha.fderiv_right (m := m) (by exact_mod_cast (show m + 1 ≤ m + 1 by omega))
    exact (h1.of_le (by exact_mod_cast hn)).clm_apply contDiff_const
  have hfaF : ContDiff ℝ n (fun y => fderiv ℝ (fun z => a z * F z) y (EuclideanSpace.single j (1 : ℝ))) := by
    have h1 : ContDiff ℝ n (fderiv ℝ (fun z => a z * F z)) :=
      haF.fderiv_right (m := n) (by exact_mod_cast (show n + 1 ≤ n + 1 by omega))
    exact h1.clm_apply contDiff_const
  have hψ : ContDiff ℝ n (fun y => F y * fderiv ℝ a y (EuclideanSpace.single j (1 : ℝ))) :=
    hF'.mul hda
  have hdiff : Differentiable ℝ a := ha.differentiable (by exact_mod_cast Nat.succ_ne_zero m)
  have hfunA : (fun y => a y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))) =
      fun y => (fun y => fderiv ℝ (fun z => a z * F z) y (EuclideanSpace.single j (1 : ℝ))) y -
        (fun y => F y * fderiv ℝ a y (EuclideanSpace.single j (1 : ℝ))) y := by
    funext y
    have hd := fderiv_fun_mul (hdiff y) ((hF.differentiable (by simp)) y)
    simp only
    rw [hd]
    simp [smul_eq_mul]
  rw [hfunA, sa12x2_pd_sub hfaF hψ idx x]
  have hR := sa12x2_pd_right (fun y => a y * F y) haF idx j x
  have hP := sa12x2_pd_snoc n (fun y => a y * F y) haF idx j x
  rw [hP, hR]

end HRS.MH.AdjointRd.Phase2SA12
