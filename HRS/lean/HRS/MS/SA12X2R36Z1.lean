import HRS.MS.SA12X2R36P

/-!
# S.A.12 R36 (SA12X2), part Z1: pointwise Leibniz bound with the power sum `Z`

`Z F x = ∑_{l ≤ m+1} ∑_{γ : Fin l → Fin d} (∂^γ F x)²`. For `a ∈ C^(m+1)` with bounded jets,
`(∂^idx (a F) x)² ≤ B² (2^(m+1))² (m+2) d^(m+1) Z F x` for `|idx| ≤ m+1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12

open HRS HRS.Whole

variable {d : ℕ}

theorem sa12x2_le_top' (n : ℕ) : ((n : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast le_top

/-- The order-`(m+1)` power sum of the jets of `F`. -/
def sa12x2_Z (m : ℕ) (F : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∑ l ∈ Finset.range (m + 2), ∑ γ : Fin l → Fin d, partialDeriv γ F x ^ 2

theorem sa12x2_Z_nonneg (m : ℕ) (F : Euc d → ℝ) (x : Euc d) : 0 ≤ sa12x2_Z m F x :=
  Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun γ _ => sq_nonneg _

theorem sa12x2_leib_Z {m : ℕ} {B : ℝ} (hB : 0 ≤ B) (hd : 1 ≤ d) {a F : Euc d → ℝ}
    (ha : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) a) (hF : ContDiff ℝ ∞ F)
    (hB' : ∀ j ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ B) {j : ℕ} (hj : j ≤ m + 1)
    (idx : Fin j → Fin d) (x : Euc d) :
    (partialDeriv idx (fun y => a y * F y) x) ^ 2 ≤
      B ^ 2 * ((2 : ℝ) ^ (m + 1)) ^ 2 * ((m : ℝ) + 2) * (d : ℝ) ^ (m + 1) * sa12x2_Z m F x := by
  have hpd := sa12x2_pd_le_norm (fun y => a y * F y) idx x
  have hleib := sa12x2_leib_pt hB ha (hF.of_le (sa12x2_le_top' _)) hB' hj x
  -- the F-part: ∑_{i ≤ j} ‖∂^{j-i} F‖² ≤ d^(m+1) Z
  have hsumF : ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ (j - i) F x‖ ^ 2 ≤
      (d : ℝ) ^ (m + 1) * sa12x2_Z m F x := by
    have e1 : ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ (j - i) F x‖ ^ 2 ≤
        ∑ i ∈ Finset.range (j + 1), (d : ℝ) ^ (j - i) *
          ∑ γ : Fin (j - i) → Fin d, (partialDeriv γ F x) ^ 2 :=
      Finset.sum_le_sum fun i _ => sa12x2_multi_sq_le (d := d) (iteratedFDeriv ℝ (j - i) F x)
    have e2 : ∑ i ∈ Finset.range (j + 1), (d : ℝ) ^ (j - i) *
          ∑ γ : Fin (j - i) → Fin d, (partialDeriv γ F x) ^ 2 =
        ∑ l ∈ Finset.range (j + 1), (d : ℝ) ^ l * ∑ γ : Fin l → Fin d, (partialDeriv γ F x) ^ 2 := by
      have := Finset.sum_range_reflect
        (fun l => (d : ℝ) ^ l * ∑ γ : Fin l → Fin d, (partialDeriv γ F x) ^ 2) (j + 1)
      simpa using this
    have e3 : ∑ l ∈ Finset.range (j + 1), (d : ℝ) ^ l * ∑ γ : Fin l → Fin d, (partialDeriv γ F x) ^ 2 ≤
        (d : ℝ) ^ (m + 1) * sa12x2_Z m F x := by
      unfold sa12x2_Z
      rw [Finset.mul_sum]
      refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.2 (show j + 1 ≤ m + 2 by omega))
        (fun l _ _ => mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
          (Finset.sum_nonneg fun _ _ => sq_nonneg _)))
      refine Finset.sum_le_sum fun l hl => ?_
      have hl' : l ≤ m + 1 := by have := Finset.mem_range.mp hl; omega
      have hdl : (d : ℝ) ^ l ≤ (d : ℝ) ^ (m + 1) :=
        pow_le_pow_right₀ (by exact_mod_cast hd) hl'
      have hs : 0 ≤ ∑ γ : Fin l → Fin d, (partialDeriv γ F x) ^ 2 :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      calc (d : ℝ) ^ l * ∑ γ : Fin l → Fin d, (partialDeriv γ F x) ^ 2
          ≤ (d : ℝ) ^ (m + 1) * ∑ γ : Fin l → Fin d, (partialDeriv γ F x) ^ 2 :=
            mul_le_mul_of_nonneg_right hdl hs
        _ = (d : ℝ) ^ (m + 1) * ∑ γ : Fin l → Fin d, (partialDeriv γ F x) ^ 2 := rfl
    exact e1.trans (e2.le.trans e3)
  -- combine
  have hj2 : ((2 : ℝ) ^ j) ^ 2 ≤ ((2 : ℝ) ^ (m + 1)) ^ 2 := by
    have h2j : (2 : ℝ) ^ j ≤ 2 ^ (m + 1) := pow_le_pow_right₀ (by norm_num) hj
    exact pow_le_pow_left₀ (by positivity) h2j 2
  have hjm : (j : ℝ) + 1 ≤ (m : ℝ) + 2 := by
    have : (j : ℝ) ≤ m + 1 := by exact_mod_cast hj
    linarith
  have hZ0 : 0 ≤ (d : ℝ) ^ (m + 1) * sa12x2_Z m F x :=
    mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (sa12x2_Z_nonneg m F x)
  have hC : B ^ 2 * ((2 : ℝ) ^ j) ^ 2 * ((j : ℝ) + 1) ≤ B ^ 2 * ((2 : ℝ) ^ (m + 1)) ^ 2 * ((m : ℝ) + 2) := by
    gcongr
  calc (partialDeriv idx (fun y => a y * F y) x) ^ 2
      ≤ ‖iteratedFDeriv ℝ j (fun y => a y * F y) x‖ ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hpd 2
    _ ≤ B ^ 2 * ((2 : ℝ) ^ j) ^ 2 * ((j : ℝ) + 1) *
          ∑ i ∈ Finset.range (j + 1), ‖iteratedFDeriv ℝ (j - i) F x‖ ^ 2 := hleib
    _ ≤ B ^ 2 * ((2 : ℝ) ^ j) ^ 2 * ((j : ℝ) + 1) * ((d : ℝ) ^ (m + 1) * sa12x2_Z m F x) :=
        mul_le_mul_of_nonneg_left hsumF (by positivity)
    _ ≤ B ^ 2 * ((2 : ℝ) ^ (m + 1)) ^ 2 * ((m : ℝ) + 2) * ((d : ℝ) ^ (m + 1) * sa12x2_Z m F x) :=
        mul_le_mul_of_nonneg_right hC hZ0
    _ = B ^ 2 * ((2 : ℝ) ^ (m + 1)) ^ 2 * ((m : ℝ) + 2) * (d : ℝ) ^ (m + 1) * sa12x2_Z m F x := by ring

end HRS.MH.AdjointRd.Phase2SA12
