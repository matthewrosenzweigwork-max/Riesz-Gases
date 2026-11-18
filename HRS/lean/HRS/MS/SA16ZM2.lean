import HRS.MS.SA16ZM1

/-!
# S.A.16 (SA16Z) M2: pairing of a tensor with an `L^p` error against the energy density (Young)

`sa16z_young_pair`: `|W|^{p-2} ∑_κ W_κ R_κ ≤ ∑_κ (((p-1)/p)|W|^p + |R_κ|^p / p)` pointwise;
`sa16z_pair_int`: integrated version (upper bound of the integral, no integrability of the left side needed).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section M2
variable {d : ℕ}

lemma sa16z_integral_le_of_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {g h : α → ℝ}
    (hgh : ∀ x, g x ≤ h x) (hh : Integrable h μ) (hh0 : ∀ x, 0 ≤ h x) : ∫ x, g x ∂μ ≤ ∫ x, h x ∂μ := by
  by_cases hg : Integrable g μ
  · exact integral_mono hg hh hgh
  · rw [integral_undef hg]; exact integral_nonneg hh0

lemma sa16z_young_pair {ι : Type*} [Fintype ι] {p : ℝ} (hp : 2 ≤ p) (W R : ι → ℝ) :
    vnorm W ^ (p - 2) * ∑ κ, W κ * R κ ≤
      ∑ κ : ι, (((p - 1) / p) * vnorm W ^ p + (1 / p) * |R κ| ^ p) := by
  have hp1 : 1 < p := by linarith
  have hp0 : 0 < p := by linarith
  set v := vnorm W with hv
  have hv0 : 0 ≤ v := Real.sqrt_nonneg _
  have hWle : ∀ κ, |W κ| ≤ v := fun κ => by
    unfold vnorm at hv
    rw [hv]
    refine Real.abs_le_sqrt ?_
    exact Finset.single_le_sum (f := fun κ => W κ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ κ)
  have hconj : p.HolderConjugate (p / (p - 1)) := by
    refine Real.holderConjugate_iff.2 ⟨hp1, ?_⟩
    field_simp; ring
  have hterm : ∀ κ, v ^ (p - 2) * (W κ * R κ) ≤ ((p - 1) / p) * v ^ p + (1 / p) * |R κ| ^ p := by
    intro κ
    have h1 : v ^ (p - 2) * (W κ * R κ) ≤ v ^ (p - 1) * |R κ| := by
      have : v ^ (p - 2) * v = v ^ (p - 1) := by
        rcases eq_or_lt_of_le hv0 with h0 | hpos
        · rw [← h0, mul_zero, Real.zero_rpow (by linarith)]
        · rw [← Real.rpow_add_one hpos.ne']; congr 1; ring
      calc v ^ (p - 2) * (W κ * R κ) ≤ v ^ (p - 2) * (v * |R κ|) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hv0 _)
            calc W κ * R κ ≤ |W κ * R κ| := le_abs_self _
              _ = |W κ| * |R κ| := abs_mul _ _
              _ ≤ v * |R κ| := mul_le_mul_of_nonneg_right (hWle κ) (abs_nonneg _)
        _ = v ^ (p - 1) * |R κ| := by rw [← this]; ring
    refine h1.trans ?_
    have := Real.young_inequality_of_nonneg (Real.rpow_nonneg hv0 (p - 1)) (abs_nonneg (R κ)) hconj.symm
    have e : (v ^ (p - 1)) ^ (p / (p - 1)) = v ^ p := by
      rw [← Real.rpow_mul hv0]; congr 1
      have : p - 1 ≠ 0 := by linarith
      field_simp
    rw [e] at this
    refine this.trans (le_of_eq ?_)
    have hp1' : p - 1 ≠ 0 := by linarith
    field_simp
  calc v ^ (p - 2) * ∑ κ, W κ * R κ = ∑ κ, v ^ (p - 2) * (W κ * R κ) := by rw [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun κ _ => hterm κ

end M2

end HRS.Whole.AppendixA.Phase2SA16R
