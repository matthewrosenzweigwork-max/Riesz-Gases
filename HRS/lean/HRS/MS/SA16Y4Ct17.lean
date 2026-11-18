import HRS.MS.SA16Y4Ct16

/-!
# S.A.16 (SA16Y4) Ct17: `‖M_θ ι Z‖` splits into the derivative gain and the weak-to-strong part

`sa16y4_MZ_le`: for `Z ∈ W^{k+1,p}`, `‖M (ι Z)‖ ≤ B' card(k) (card(k) d/(n+1)) ‖Z‖ + B' ∑_κ ‖1_{B(0,R₁)} (R_n ι Z)_κ‖_p`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q Phase2SA16Evolution Phase2SA16Transfer

section Ct17
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16y4_loc_sum_le (k : ℕ) (R₁ : ℝ) (Y : WmpSpace d k p) :
    ∑ κ : WIndex d k, sa16y4_loc k R₁ κ Y ≤ (Fintype.card (WIndex d k) : ℝ) * ‖Y‖ := by
  calc ∑ κ : WIndex d k, sa16y4_loc k R₁ κ Y ≤ ∑ κ : WIndex d k, ‖Y‖ :=
        Finset.sum_le_sum fun κ _ => sa16y4_loc_le_norm k R₁ κ Y
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem sa16y4_MZ_le (k n : ℕ) (R₁ : ℝ) (M R : WmpSpace d k p →L[ℝ] WmpSpace d k p) {B' : ℝ} (hB'0 : 0 ≤ B')
    (hMb : ∀ Y : WmpSpace d k p, ‖M Y‖ ≤ B' * ∑ κ : WIndex d k, sa16y4_loc k R₁ κ Y)
    (hR : ∀ ψ : ccSub d, R (sa16r_Jcc d k p ψ) = sa16r_Jcc d k p ⟨sa16q_mol n ψ.1, sa16y4_mol_cc ψ.2 n⟩)
    (Z : WmpSpace d (k + 1) p) :
    ‖M (sa16r_iota d k p Z)‖ ≤
      B' * (Fintype.card (WIndex d k) : ℝ) * (((Fintype.card (WIndex d k) : ℝ) * d / ((n : ℝ) + 1)) * ‖Z‖) +
        B' * ∑ κ : WIndex d k, sa16y4_loc k R₁ κ (R (sa16r_iota d k p Z)) := by
  have h2 := sa16y4_Rgain k n R hR Z
  generalize sa16r_iota d k p Z = a at h2 ⊢
  have e : M a = M (a - R a) + M (R a) := (congrArg M (sub_add_cancel a (R a)).symm).trans (map_add M _ _)
  have h1 : ‖M (a - R a)‖ ≤ B' * (Fintype.card (WIndex d k) : ℝ) * ‖a - R a‖ := by
    refine (hMb _).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (sa16y4_loc_sum_le k R₁ _) hB'0
  have h3 : ‖M (R a)‖ ≤ B' * ∑ κ : WIndex d k, sa16y4_loc k R₁ κ (R a) := hMb _
  calc ‖M a‖ = ‖M (a - R a) + M (R a)‖ := by rw [← e]
    _ ≤ ‖M (a - R a)‖ + ‖M (R a)‖ := norm_add_le _ _
    _ ≤ _ := by
      have hc : 0 ≤ B' * (Fintype.card (WIndex d k) : ℝ) := by positivity
      have := mul_le_mul_of_nonneg_left h2 hc
      linarith
end Ct17

end HRS.Whole.AppendixA.Phase2SA16R
