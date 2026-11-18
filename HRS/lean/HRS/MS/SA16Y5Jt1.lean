import HRS.MS.SA16Y5Ja1
import HRS.MS.SA16QApp2
import HRS.MS.SA16SOp5

/-!
# S.A.16 (SA16Y5) Jt1: Leibniz bound in `L^p` and linearity of `T` (K3, jets part 1)

`sa16y5_leib_lp`: `‖∂^idx (a' φ)‖_r ≤ 2^l W d^k ‖wJet k φ‖_r` for `φ ∈ C_c^∞`, `‖D^κ a'‖_∞ ≤ W` (`κ ≤ l ≤ k`).
`sa16y5_T_add`, `sa16y5_T_smul`: `T` is additive / homogeneous in `(P,Q)` (`P,Q,P',Q' ∈ C_c^∞`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Jt1
variable {d : ℕ} {s : ℝ}

lemma sa16y5_leib_lp (hd1 : 1 ≤ d) {a' : Euc d → ℝ} (ha : ContDiff ℝ ∞ a') {W : ℝ} (hW : 0 ≤ W) {k l : ℕ}
    (hl : l ≤ k) (hbd : ∀ κ ≤ l, ∀ x, ‖iteratedFDeriv ℝ κ a' x‖ ≤ W) (φ : ccSub d) (idx : Fin l → Fin d)
    {r : ℝ} (hr : 1 ≤ r) :
    eLpNorm (partialDeriv idx (fun y => a' y * φ.1 y)) (ENNReal.ofReal r) volume ≤
      ENNReal.ofReal (2 ^ l * (W * (d : ℝ) ^ k)) * eLpNorm (wJet k φ.1) (ENNReal.ofReal r) volume := by
  set u := sa16so_schw φ with hu
  have hcont : Continuous (partialDeriv idx (fun y => a' y * φ.1 y)) :=
    (sa16j_pd_smooth (ha.mul φ.2.1) idx).continuous
  have hWc : ∀ κ : ℕ, Continuous (fun x => ‖iteratedFDeriv ℝ κ a' x‖ * ‖iteratedFDeriv ℝ (l - κ) φ.1 x‖) := fun κ =>
    ((ha.continuous_iteratedFDeriv (m := κ) (sa16q_nat_le_infty _)).norm).mul
      ((φ.2.1.continuous_iteratedFDeriv (m := l - κ) (sa16q_nat_le_infty _)).norm)
  have h1 := sa16q_lp_of_pointwise hcont (fun κ => (l.choose κ : ℝ))
    (fun κ x => ‖iteratedFDeriv ℝ κ a' x‖ * ‖iteratedFDeriv ℝ (l - κ) φ.1 x‖) hWc
    (fun κ => by positivity) (fun x => sa16q_pd_mul_le ha φ.2.1 idx x) hr
  refine h1.trans ?_
  have h2 : ∀ κ ∈ Finset.range (l + 1), ENNReal.ofReal (l.choose κ : ℝ) *
      eLpNorm (fun x => ‖iteratedFDeriv ℝ κ a' x‖ * ‖iteratedFDeriv ℝ (l - κ) φ.1 x‖) (ENNReal.ofReal r) volume ≤
      ENNReal.ofReal ((l.choose κ : ℝ) * (W * (d : ℝ) ^ k)) * eLpNorm (wJet k φ.1) (ENNReal.ofReal r) volume := by
    intro κ hκ
    have hκl : κ ≤ l := by have := Finset.mem_range.1 hκ; omega
    have := sa16q_unif_CZ hd1 ha hW (κ := κ) (n := l - κ) (m := k) (fun x => hbd κ hκl x) u (by omega) (p := r)
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), mul_assoc]
    gcongr
    exact this
  refine (Finset.sum_le_sum h2).trans ?_
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun κ _ => by positivity)]
  refine le_of_eq ?_
  congr 2
  rw [← Finset.sum_mul]
  have : ∑ κ ∈ Finset.range (l + 1), (l.choose κ : ℝ) = 2 ^ l := by
    exact_mod_cast Nat.sum_range_choose l
  rw [this]

end Jt1

end HRS.Whole.AppendixA.Phase2SA16R
