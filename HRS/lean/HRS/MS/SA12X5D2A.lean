import HRS.MS.SA12X3C15
import HRS.MS.SA12X4D1
import HRS.MS.SA12X5Defs

/-!
# S.A.12 X5 D2A: splitting the jet pairing against `-N + S`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Near
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x5_pd_split {n : ℕ} (idx : Fin n → Fin d) {N S : Euc d → ℝ} (hN : ContDiff ℝ ∞ N)
    (hS : ContDiff ℝ ∞ S) (x : Euc d) :
    partialDeriv idx (fun y => -N y + S y) x = -partialDeriv idx N x + partialDeriv idx S x := by
  unfold partialDeriv
  have e : (fun y => -N y + S y) = (-N) + S := by funext y; simp
  have h1 : ContDiffAt ℝ (n : WithTop ℕ∞) (-N) x :=
    (hN.neg.contDiffAt).of_le (by exact_mod_cast le_top)
  have h2 : ContDiffAt ℝ (n : WithTop ℕ∞) S x := (hS.contDiffAt).of_le (by exact_mod_cast le_top)
  rw [e, iteratedFDeriv_add_apply h1 h2, iteratedFDeriv_neg_apply]
  simp

theorem sa12x5_jetPair_split (m : ℕ) {w F N S : Euc d → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w)
    (hF : ContDiff ℝ ∞ F) (hN : ContDiff ℝ ∞ N) (hS : ContDiff ℝ ∞ S) :
    jetPair m w F (fun y => -N y + S y) = -jetPair m w F N + jetPair m w F S := by
  have hint : ∀ {P Q : Euc d → ℝ}, ContDiff ℝ ∞ P → ContDiff ℝ ∞ Q → ∀ {j : ℕ} (idx : Fin j → Fin d),
      Integrable (fun x => w x ^ 2 * (partialDeriv idx P x * partialDeriv idx Q x)) := by
    intro P Q hP hQ j idx
    have hcP : Continuous (partialDeriv idx P) := (sa12z3_pd_contDiff_inf hP idx).continuous
    have hcQ : Continuous (partialDeriv idx Q) := (sa12z3_pd_contDiff_inf hQ idx).continuous
    have hc : Continuous (fun x => w x ^ 2 * (partialDeriv idx P x * partialDeriv idx Q x)) :=
      (hw.pow 2).mul (hcP.mul hcQ)
    refine hc.integrable_of_hasCompactSupport ?_
    have e : (fun x => w x ^ 2 * (partialDeriv idx P x * partialDeriv idx Q x)) =
        fun x => w x * (w x * (partialDeriv idx P x * partialDeriv idx Q x)) := by
      funext x; ring
    rw [e]
    exact hwc.mul_right
  unfold jetPair
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_neg, ← mul_add, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun idx _ => ?_
  have h1 : Integrable (fun x => -(w x ^ 2 * (partialDeriv idx F x * partialDeriv idx N x))) :=
    (hint hF hN idx).neg
  rw [← integral_neg, ← integral_add h1 (hint hF hS idx)]
  congr 1
  funext x
  rw [sa12x5_pd_split idx hN hS]
  ring

end HRS.MH.AdjointRd.Phase2SA12X5
