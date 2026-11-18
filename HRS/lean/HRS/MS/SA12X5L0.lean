import HRS.MS.SA12Z3NearN7F
import HRS.MH.AdjointRdDefs

/-!
# S.A.12 X5 LOC0: elementary properties of `jetSq`

nonnegativity, monotonicity in the level, the scalar identity, and the integrability of the jet integrands.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Near

variable {d : ℕ}

theorem sa12x5_loc_integral_nonneg {n : ℕ} (w F : Euc d → ℝ) (idx : Fin n → Fin d) :
    0 ≤ ∫ x, (w x * partialDeriv idx F x) ^ 2 :=
  integral_nonneg fun x => sq_nonneg _

theorem sa12x5_jetSq_nonneg (m : ℕ) (w F : Euc d → ℝ) : 0 ≤ jetSq m w F := by
  unfold jetSq
  exact Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _)
    (Finset.sum_nonneg fun idx _ => sa12x5_loc_integral_nonneg w F idx)

theorem sa12x5_jetSq_mono {m m' : ℕ} (h : m ≤ m') (w F : Euc d → ℝ) : jetSq m w F ≤ jetSq m' w F := by
  unfold jetSq
  calc ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d, ∫ x, (w x * partialDeriv idx F x) ^ 2
      ≤ ∑ j ∈ Finset.range (m + 1), (Nat.choose m' j : ℝ) * ∑ idx : Fin j → Fin d,
          ∫ x, (w x * partialDeriv idx F x) ^ 2 := by
        refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right ?_
          (Finset.sum_nonneg fun idx _ => sa12x5_loc_integral_nonneg w F idx)
        exact_mod_cast Nat.choose_le_choose j h
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.2 (by omega)) (fun j _ _ => mul_nonneg (Nat.cast_nonneg _)
          (Finset.sum_nonneg fun idx _ => sa12x5_loc_integral_nonneg w F idx))

/-- Every jet integrand is integrable (continuous with compact support). -/
theorem sa12x5_loc_integrable {w g : Euc d → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w)
    (hg : Continuous g) : Integrable (fun x => (w x * g x) ^ 2) := by
  refine Continuous.integrable_of_hasCompactSupport ((hw.mul hg).pow 2) ?_
  exact (hwc.mul_right (f' := g)).comp_left (g := fun t : ℝ => t ^ 2) (by simp)

theorem sa12x5_jetSq_const_mul (m : ℕ) (w F : Euc d → ℝ) (c : ℝ) {G : Euc d → ℝ}
    (hG : ∀ {n : ℕ} (idx : Fin n → Fin d) (x : Euc d), partialDeriv idx G x = c * partialDeriv idx F x) :
    jetSq m w G = c ^ 2 * jetSq m w F := by
  unfold jetSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun idx _ => ?_
  have : ∫ x, (w x * partialDeriv idx G x) ^ 2 = ∫ x, c ^ 2 * (w x * partialDeriv idx F x) ^ 2 :=
    integral_congr_ae (Eventually.of_forall fun x => by simp only [hG idx x]; ring)
  rw [this, integral_const_mul]
  ring

/-- The terms of the jet sum with coefficient at least `1`: `∑_{r ≤ m}∑_γ ∫ (w ∂^γ F)² ≤ jetSq m w F`. -/
theorem sa12x5_loc_sum_le_jetSq (m : ℕ) (w F : Euc d → ℝ) :
    ∑ r ∈ Finset.range (m + 1), ∑ γ : Fin r → Fin d, ∫ x, (w x * partialDeriv γ F x) ^ 2 ≤ jetSq m w F := by
  unfold jetSq
  refine Finset.sum_le_sum fun r hr => ?_
  have hrm : r ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
  have hc1 : (1 : ℝ) ≤ (Nat.choose m r : ℝ) := by exact_mod_cast Nat.choose_pos hrm
  have h0 : 0 ≤ ∑ γ : Fin r → Fin d, ∫ x, (w x * partialDeriv γ F x) ^ 2 :=
    Finset.sum_nonneg fun γ _ => sa12x5_loc_integral_nonneg w F γ
  nlinarith

end HRS.MH.AdjointRd.Phase2SA12X5
