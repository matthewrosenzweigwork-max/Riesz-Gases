import HRS.MS.SA12V3O

/-!
# S.A.12 C2 (SA12V3 worker), part P: generic `ℝ≥0∞` summation lemmas for the weighted bound

* `sa12v3_sq_sum_le`: `(∑_{i∈s} f_i)² ≤ |s| ∑ f_i²` for finite values;
* `sa12v3_fiber_bound`: if `wa z ≤ Q wb(τ z)` on `{p}` and the fibres of `τ` lie in finsets of size `≤ M`, then
  `∑'_z 1_p(z) wa_z a(τ z)² ≤ Q M ∑'_t wb_t a_t²`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Pointwise

namespace HRS.MH.AdjointRd.Phase2SA12V3

theorem sa12v3_sq_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) (hf : ∀ i ∈ s, f i ≠ ⊤) :
    (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ≥0∞) * ∑ i ∈ s, f i ^ 2 := by
  set r : ι → ℝ := fun i => (f i).toReal with hr
  have hfr : ∀ i ∈ s, f i = ENNReal.ofReal (r i) := fun i hi => (ENNReal.ofReal_toReal (hf i hi)).symm
  have hr0 : ∀ i ∈ s, 0 ≤ r i := fun i _ => ENNReal.toReal_nonneg
  have e1 : ∑ i ∈ s, f i = ENNReal.ofReal (∑ i ∈ s, r i) := by
    rw [ENNReal.ofReal_sum_of_nonneg hr0]
    exact Finset.sum_congr rfl hfr
  have e2 : ∑ i ∈ s, f i ^ 2 = ENNReal.ofReal (∑ i ∈ s, r i ^ 2) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => sq_nonneg _)]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hfr i hi, ENNReal.ofReal_pow (hr0 i hi)]
  rw [e1, e2, ← ENNReal.ofReal_pow (Finset.sum_nonneg hr0), ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (sq_sum_le_card_mul_sum_sq)

theorem sa12v3_fiber_bound {ι ι' : Type*} (p : ι → Prop) [DecidablePred p] (wa : ι → ℝ≥0∞) (wb a : ι' → ℝ≥0∞)
    (τ : ι → ι') (Q : ℝ≥0∞) (M : ℕ) (hwa : ∀ z, p z → wa z ≤ Q * wb (τ z))
    (hfib : ∀ t, ∃ B : Finset ι, τ ⁻¹' {t} ⊆ ↑B ∧ B.card ≤ M) :
    ∑' z, (if p z then wa z * a (τ z) ^ 2 else 0) ≤ Q * M * ∑' t, wb t * a t ^ 2 := by
  set h : ι' → ℝ≥0∞ := fun t => wb t * a t ^ 2 with hh
  have h1 : ∑' z, (if p z then wa z * a (τ z) ^ 2 else 0) ≤ ∑' z, Q * h (τ z) := by
    refine ENNReal.tsum_le_tsum fun z => ?_
    by_cases hz : p z
    · rw [if_pos hz, hh]
      calc wa z * a (τ z) ^ 2 ≤ (Q * wb (τ z)) * a (τ z) ^ 2 := mul_le_mul' (hwa z hz) le_rfl
        _ = Q * (wb (τ z) * a (τ z) ^ 2) := mul_assoc _ _ _
    · rw [if_neg hz]; exact bot_le
  rw [ENNReal.tsum_mul_left] at h1
  refine h1.trans ?_
  rw [mul_assoc]
  refine mul_le_mul' le_rfl ?_
  rw [← ENNReal.tsum_fiberwise (fun z => h (τ z)) τ]
  have h2 : ∀ t, ∑' z : τ ⁻¹' {t}, h (τ z) ≤ (M : ℝ≥0∞) * h t := by
    intro t
    obtain ⟨B, hB, hcard⟩ := hfib t
    have e : ∀ z : τ ⁻¹' {t}, h (τ z) = h t := fun z => by rw [show τ z = t from z.2]
    simp_rw [e]
    calc ∑' _z : τ ⁻¹' {t}, h t ≤ ∑' _z : (B : Set ι), h t :=
          ENNReal.tsum_comp_le_tsum_of_injective (f := Set.inclusion hB) (Set.inclusion_injective hB) (fun _ => h t)
      _ = B.card • h t := by
          rw [Finset.tsum_subtype' B (fun _ => h t), Finset.sum_const]
      _ = (B.card : ℝ≥0∞) * h t := by rw [nsmul_eq_mul]
      _ ≤ (M : ℝ≥0∞) * h t := mul_le_mul' (Nat.cast_le.2 hcard) le_rfl
  calc ∑' t, ∑' z : τ ⁻¹' {t}, h (τ z) ≤ ∑' t, (M : ℝ≥0∞) * h t := ENNReal.tsum_le_tsum h2
    _ = (M : ℝ≥0∞) * ∑' t, h t := ENNReal.tsum_mul_left

end HRS.MH.AdjointRd.Phase2SA12V3
