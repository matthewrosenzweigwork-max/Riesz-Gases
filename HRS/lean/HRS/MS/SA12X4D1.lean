import HRS.MS.SA12X3C15
import HRS.MS.SA12X4W1

/-!
# S.A.12 (SA12X4) d1: Young's inequality for the jet pairing

`2 jetPair m w F G ≤ ε jetSq m w F + ε⁻¹ jetSq m w G`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X4

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Near

variable {d : ℕ}

theorem sa12x4_jetPair_young (m : ℕ) {w F G : Euc d → ℝ} (hw : Continuous w) (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G)
    (hFi : ∀ {j : ℕ}, j ≤ m → ∀ idx : Fin j → Fin d, Integrable (fun x => (w x * partialDeriv idx F x) ^ 2))
    (hGi : ∀ {j : ℕ}, j ≤ m → ∀ idx : Fin j → Fin d, Integrable (fun x => (w x * partialDeriv idx G x) ^ 2))
    {ε : ℝ} (hε : 0 < ε) :
    2 * jetPair m w F G ≤ ε * jetSq m w F + ε⁻¹ * jetSq m w G := by
  have key : ∀ {j : ℕ}, j ≤ m → ∀ idx : Fin j → Fin d,
      2 * (∫ x, w x ^ 2 * (partialDeriv idx F x * partialDeriv idx G x)) ≤
        ε * (∫ x, (w x * partialDeriv idx F x) ^ 2) + ε⁻¹ * (∫ x, (w x * partialDeriv idx G x) ^ 2) := by
    intro j hj idx
    have hcF : Continuous (partialDeriv idx F) := (sa12z3_pd_contDiff_inf hF idx).continuous
    have hcG : Continuous (partialDeriv idx G) := (sa12z3_pd_contDiff_inf hG idx).continuous
    have hP : Integrable (fun x => w x ^ 2 * (partialDeriv idx F x * partialDeriv idx G x)) := by
      refine Integrable.mono' ((hFi hj idx).add (hGi hj idx)) ?_ (Filter.Eventually.of_forall fun x => ?_)
      · exact (hw.pow 2).mul (hcF.mul hcG) |>.aestronglyMeasurable
      · rw [Real.norm_eq_abs]
        show |w x ^ 2 * (partialDeriv idx F x * partialDeriv idx G x)| ≤
          (w x * partialDeriv idx F x) ^ 2 + (w x * partialDeriv idx G x) ^ 2
        have h1 : w x ^ 2 * (partialDeriv idx F x * partialDeriv idx G x) =
            (w x * partialDeriv idx F x) * (w x * partialDeriv idx G x) := by ring
        rw [h1, abs_le]
        constructor <;> nlinarith [sq_nonneg (w x * partialDeriv idx F x + w x * partialDeriv idx G x),
          sq_nonneg (w x * partialDeriv idx F x - w x * partialDeriv idx G x),
          sq_nonneg (w x * partialDeriv idx F x), sq_nonneg (w x * partialDeriv idx G x)]
    have e1 : 2 * (∫ x, w x ^ 2 * (partialDeriv idx F x * partialDeriv idx G x)) =
        ∫ x, 2 * (w x ^ 2 * (partialDeriv idx F x * partialDeriv idx G x)) := (integral_const_mul _ _).symm
    have e2 : ε * (∫ x, (w x * partialDeriv idx F x) ^ 2) + ε⁻¹ * (∫ x, (w x * partialDeriv idx G x) ^ 2) =
        ∫ x, (ε * (w x * partialDeriv idx F x) ^ 2 + ε⁻¹ * (w x * partialDeriv idx G x) ^ 2) := by
      rw [integral_add ((hFi hj idx).const_mul ε) ((hGi hj idx).const_mul ε⁻¹)]
      simp only [integral_const_mul]
    rw [e1, e2]
    refine integral_mono (hP.const_mul 2) (((hFi hj idx).const_mul ε).add ((hGi hj idx).const_mul ε⁻¹)) fun x => ?_
    show 2 * (w x ^ 2 * (partialDeriv idx F x * partialDeriv idx G x)) ≤
      ε * (w x * partialDeriv idx F x) ^ 2 + ε⁻¹ * (w x * partialDeriv idx G x) ^ 2
    have hε0 : ε⁻¹ * ε = 1 := inv_mul_cancel₀ hε.ne'
    have hεi : 0 < ε⁻¹ := inv_pos.2 hε
    have h2 : ε⁻¹ * (ε * (w x * partialDeriv idx F x) - w x * partialDeriv idx G x) ^ 2 ≥ 0 :=
      mul_nonneg hεi.le (sq_nonneg _)
    have h3 : ε⁻¹ * (ε * (w x * partialDeriv idx F x) - w x * partialDeriv idx G x) ^ 2 =
        ε * (w x * partialDeriv idx F x) ^ 2 - 2 * (w x * partialDeriv idx F x) * (w x * partialDeriv idx G x) +
          ε⁻¹ * (w x * partialDeriv idx G x) ^ 2 := by
      field_simp
      ring
    nlinarith [h2, h3]
  have hj : ∀ j ∈ Finset.range (m + 1), 2 * ((Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d,
      (∫ x, w x ^ 2 * (partialDeriv idx F x * partialDeriv idx G x))) ≤
      ε * ((Nat.choose m j : ℝ) * (∑ idx : Fin j → Fin d, (∫ x, (w x * partialDeriv idx F x) ^ 2))) +
        ε⁻¹ * ((Nat.choose m j : ℝ) * (∑ idx : Fin j → Fin d, (∫ x, (w x * partialDeriv idx G x) ^ 2))) := by
    intro j hj
    have hjm : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hc : (0 : ℝ) ≤ (Nat.choose m j : ℝ) := Nat.cast_nonneg _
    have hs : 2 * (∑ idx : Fin j → Fin d, (∫ x, w x ^ 2 * (partialDeriv idx F x * partialDeriv idx G x))) ≤
        ε * (∑ idx : Fin j → Fin d, (∫ x, (w x * partialDeriv idx F x) ^ 2)) +
          ε⁻¹ * (∑ idx : Fin j → Fin d, (∫ x, (w x * partialDeriv idx G x) ^ 2)) := by
      calc 2 * (∑ idx : Fin j → Fin d, (∫ x, w x ^ 2 * (partialDeriv idx F x * partialDeriv idx G x)))
          = ∑ idx : Fin j → Fin d, 2 * (∫ x, w x ^ 2 * (partialDeriv idx F x * partialDeriv idx G x)) := by
            rw [Finset.mul_sum]
        _ ≤ ∑ idx : Fin j → Fin d, (ε * (∫ x, (w x * partialDeriv idx F x) ^ 2) +
              ε⁻¹ * (∫ x, (w x * partialDeriv idx G x) ^ 2)) := Finset.sum_le_sum fun idx _ => key hjm idx
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have := mul_le_mul_of_nonneg_left hs hc
    calc 2 * ((Nat.choose m j : ℝ) * (∑ idx : Fin j → Fin d, (∫ x, w x ^ 2 * (partialDeriv idx F x * partialDeriv idx G x))))
        = (Nat.choose m j : ℝ) * (2 * (∑ idx : Fin j → Fin d, (∫ x, w x ^ 2 * (partialDeriv idx F x * partialDeriv idx G x)))) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  calc 2 * jetPair m w F G = ∑ j ∈ Finset.range (m + 1), 2 * ((Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d,
          (∫ x, w x ^ 2 * (partialDeriv idx F x * partialDeriv idx G x))) := by
        unfold jetPair; rw [Finset.mul_sum]
    _ ≤ ∑ j ∈ Finset.range (m + 1), (ε * ((Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d,
          (∫ x, (w x * partialDeriv idx F x) ^ 2)) + ε⁻¹ * ((Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d,
          (∫ x, (w x * partialDeriv idx G x) ^ 2))) := Finset.sum_le_sum hj
    _ = ε * jetSq m w F + ε⁻¹ * jetSq m w G := by
        unfold jetSq
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_add_distrib]

end HRS.MH.AdjointRd.Phase2SA12X4
