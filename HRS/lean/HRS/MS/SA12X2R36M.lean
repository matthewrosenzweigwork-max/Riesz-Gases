import HRS.MS.FixEqP1Aux1
import HRS.MH.AdjRdE3R3

/-!
# S.A.12 R36 (SA12X2), part M: mollification commutes with tuple partials

For a locally integrable `φ` and `a ∈ C^n_c`: `∂^idx (φ ⋆ a) = φ ⋆ ∂^idx a` (`(φ ⋆ a)(x) = ∫ φ(x-y) a(y) dy`).
This is the density step of the R36 approximation (smooth `a_n = φ_n ⋆ a`).
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12

open HRS HRS.Whole

variable {d : ℕ}

theorem sa12x2_pd_mol {φ : Euc d → ℝ} (hφ : LocallyIntegrable φ (volume : Measure (Euc d))) :
    ∀ (n : ℕ) (a : Euc d → ℝ), ContDiff ℝ n a → HasCompactSupport a →
      ∀ (idx : Fin n → Fin d) (x : Euc d),
        partialDeriv idx (fun x => ∫ y, φ (x - y) * a y) x =
          ∫ y, φ (x - y) * partialDeriv idx a y := by
  intro n
  induction n with
  | zero =>
    intro a ha hac idx x
    unfold partialDeriv
    simp
  | succ n ih =>
    intro a ha hac idx x
    have hcd : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (fun x => ∫ y, φ (x - y) * a y) :=
      HRS.MH.AdjointRdP.r3_contDiff_conv hφ ha hac
    rw [HRS.MS.FixEq.s57p_partialDeriv_succ hcd idx x]
    have htail : partialDeriv (fun l : Fin n => idx l.succ) (fun x => ∫ y, φ (x - y) * a y) =
        fun x => ∫ y, φ (x - y) * partialDeriv (fun l : Fin n => idx l.succ) a y :=
      funext fun x => ih a (ha.of_le (by exact_mod_cast Nat.le_succ n)) hac _ x
    rw [htail]
    have hsub : tsupport (iteratedFDeriv ℝ n a) ⊆ tsupport a :=
      tsupport_iteratedFDeriv_subset (𝕜 := ℝ) (f := a) n
    have hG1 : ContDiff ℝ 1 (partialDeriv (fun l : Fin n => idx l.succ) a) := by
      have hT : ContDiff ℝ 1 (iteratedFDeriv ℝ n a) :=
        ha.iteratedFDeriv_right (m := 1) (i := n) (by exact_mod_cast (show 1 + n ≤ n + 1 by omega))
      have hE := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Euc d) ℝ
        (fun l : Fin n => EuclideanSpace.single (idx l.succ) (1 : ℝ))).contDiff.comp hT
      exact hE
    have hGc : HasCompactSupport (partialDeriv (fun l : Fin n => idx l.succ) a) := by
      refine HasCompactSupport.of_support_subset_isCompact hac.isCompact fun y hy => ?_
      have h1 : iteratedFDeriv ℝ n a y ≠ 0 := fun h0 => Function.mem_support.1 hy (by
        unfold partialDeriv; rw [h0]; simp)
      exact hsub (subset_tsupport _ (Function.mem_support.2 h1))
    rw [HRS.MH.AdjointRdP.r3_fderiv_conv_apply hφ hG1 hGc x (EuclideanSpace.single (idx 0) (1 : ℝ))]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [HRS.MS.FixEq.s57p_partialDeriv_succ ha idx y]

end HRS.MH.AdjointRd.Phase2SA12
