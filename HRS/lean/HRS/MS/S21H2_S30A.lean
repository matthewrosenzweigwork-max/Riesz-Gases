import HRS.MS.S21F_D02
import HRS.MS.S21F_S00
import HRS.MS.R2IidAux1
import HRS.MS.QsfFeat1
import HRS.MS.QsfAux3
import HRS.MS.SuppU11Aux1

/-!
# S21H2, packet R26-T3.S30 (part A): the centered feature summand `Y : ℝ^d → ℓ²`

For a summable feature family `q` (`∑ ‖q_j‖_{C_b^J} < ∞`) and a probability measure `μ` the centered feature
`Y x = (q_j x - μ(q_j))_j ∈ ℓ²` is continuous, bounded, `μ`-centered, with uniformly summable coordinate squares
`(Y x)_j² ≤ (2‖q_j‖)²`.  These are the hypotheses of `HRS.Whole.s11iid_core`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.R26T3
open HRS HRS.Whole

variable {d J : ℕ} {q : ℕ → Euc d → ℝ}

/-- The centered feature summand. -/
def s21h2_Y (q : ℕ → Euc d → ℝ) (μ : Measure (Euc d)) (x : Euc d) : SeqL2 :=
  SeqL2.ofSeq fun j => q j x - HRS.Whole.pair μ (q j)

theorem s21h2_abs_le (hq : IsSummableFeatureFamily J q) (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] (x : Euc d) (j : ℕ) :
    |q j x - HRS.Whole.pair μ (q j)| ≤ 2 * cbNorm J (q j) := by
  have hb : ∀ x, |q j x| ≤ cbNorm J (q j) := fun x => by
    have := HRS.MS.Tc5.tc5_cb_sup_le (hq.1 j) x
    rwa [Real.norm_eq_abs] at this
  have h2 : |HRS.Whole.pair μ (q j)| ≤ cbNorm J (q j) :=
    HRS.MS.Tc5.tc5_pair_le (fun x => by rw [Real.norm_eq_abs]; exact hb x)
  have := hb x
  calc |q j x - HRS.Whole.pair μ (q j)| ≤ |q j x| + |HRS.Whole.pair μ (q j)| := abs_sub _ _
    _ ≤ _ := by linarith

theorem s21h2_summable_sq (hq : IsSummableFeatureFamily J q) :
    Summable fun j => (2 * cbNorm J (q j)) ^ 2 :=
  S45.s45_summable_sq (fun j => by have := HRS.MS.Tc5.tc5_cb_nonneg (d := d) J (q j); positivity)
    (hq.2.mul_left _)

theorem s21h2_memℓp (hq : IsSummableFeatureFamily J q) (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] (x : Euc d) : Memℓp (fun j => q j x - HRS.Whole.pair μ (q j)) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) (s21h2_summable_sq hq)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (s21h2_abs_le hq μ x j) 2

theorem s21h2_coord (hq : IsSummableFeatureFamily J q) (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] (x : Euc d) (j : ℕ) :
    SeqL2.coord (s21h2_Y q μ x) j = q j x - HRS.Whole.pair μ (q j) :=
  S45.s45_coord_ofSeq (s21h2_memℓp hq μ x) j

theorem s21h2_inner (hq : IsSummableFeatureFamily J q) (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] (x : Euc d) (j : ℕ) :
    inner ℝ (S45.s45_seqBasis j) (s21h2_Y q μ x) = q j x - HRS.Whole.pair μ (q j) := by
  rw [S45.s45_inner_seqBasis, s21h2_coord hq]

theorem s21h2_norm_le (hq : IsSummableFeatureFamily J q) (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] : ∃ C : ℝ, ∀ x, ‖s21h2_Y q μ x‖ ≤ C := by
  refine ⟨Real.sqrt (∑' j, (2 * cbNorm J (q j)) ^ 2), fun x => ?_⟩
  refine Real.le_sqrt_of_sq_le ?_
  rw [← u11_norm_sq]
  refine Summable.tsum_le_tsum (fun j => ?_) (u11_coord_summable _) (s21h2_summable_sq hq)
  rw [s21h2_coord hq]
  exact (sq_abs _).symm.le.trans (pow_le_pow_left₀ (abs_nonneg _) (s21h2_abs_le hq μ x j) 2)

end HRS.MS.R26T3
