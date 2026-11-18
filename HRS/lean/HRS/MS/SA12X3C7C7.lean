import HRS.MS.SA12X3C7C6

/-!
# S.A.12 C7 (SA12X3), part C7 (7C): `w · T` is continuous with compact support; its `L²` norm is an integral
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x3_wT_eLp {s L : ℝ} {γ : Euc d → ℝ}
    (hγ : HRS.Whole.AppendixALemmas.IsPeriodicRieszKernel d s L γ) {h R' R'' : ℝ} (hh : 0 < h) (hR : 0 < R'')
    (hR'' : R' + h / 2 ≤ R'') (hRL : R'' < L / 2) {c : Euc d} (M : Matrix (Fin d) (Fin d) ℝ)
    {w η μ F : Euc d → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w) (hη : Continuous η)
    (hμ : Continuous μ) (hF : ContDiff ℝ ∞ F)
    (hwN : ∀ x, w x ≠ 0 → x ∈ ball c R' ∧ ∀ y ∈ ball x h, η y = 1)
    {n : ℕ} (idx : Fin n → Fin d) (i j : Fin d) :
    (eLpNorm (fun x => w x * sa12x3_Tfar L γ c η μ F idx i j x) 2 volume) ^ 2 =
      ENNReal.ofReal (∫ x, (w x * sa12x3_Tfar L γ c η μ F idx i j x) ^ 2) := by
  obtain ⟨Sh, hSs, hFar, hpd⟩ := sa12x3_far_pd hγ hh hR hR'' hRL M hw hη hμ hF hwN
  have heq : (fun x => w x * sa12x3_Tfar L γ c η μ F idx i j x) = fun x => w x * partialDeriv idx (Sh i j) x := by
    funext x
    by_cases hx : w x = 0
    · simp [hx]
    · rw [hpd n idx i j x hx]
  have hc : Continuous (fun x => w x * partialDeriv idx (Sh i j) x) :=
    hw.mul (sa12z3_pd_contDiff_inf (hSs i j) idx).continuous
  have hcs : HasCompactSupport (fun x => w x * partialDeriv idx (Sh i j) x) :=
    hwc.mul_right (f' := partialDeriv idx (Sh i j))
  have e2 : (fun x => (w x * sa12x3_Tfar L γ c η μ F idx i j x) ^ 2) =
      fun x => (w x * partialDeriv idx (Sh i j) x) ^ 2 := by
    funext x; exact congrArg (· ^ 2) (congrFun heq x)
  rw [heq, e2]
  exact sa12x3_eLp_sq hc.aestronglyMeasurable
    (Continuous.integrable_of_hasCompactSupport (f := fun x => (w x * partialDeriv idx (Sh i j) x) ^ 2)
      (hc.pow 2) (hcs.comp_left (g := fun t : ℝ => t ^ 2) (by simp)))

end HRS.MH.AdjointRd.Phase2SA12Near
