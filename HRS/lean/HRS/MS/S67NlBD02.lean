import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovOscAux3

/-!
# S6.7 nonlinear breakdown, packet 02: coefficient converse with output summability proved first

`s67bd_coeff_converse`: if `∑ λ^r c²` and the raising coefficients `√(2(α_i+1)) c_{α+e_i}` are
`λ^r`-square-summable then `∑ λ^(r+1) c²` is summable and bounded by `C` times the two inputs.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

theorem s67bd_coeff_converse (d : ℕ) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : MultiIndex d → ℝ,
      Summable (fun α => oscEigenvalue d α ^ r * c α ^ 2) →
      (∀ i : Fin d, Summable (fun α => oscEigenvalue d α ^ r *
        (Real.sqrt (2 * ((α i : ℝ) + 1)) * c (mova1_up i α)) ^ 2)) →
      Summable (fun α => oscEigenvalue d α ^ (r + 1) * c α ^ 2) ∧
      (∑' α, oscEigenvalue d α ^ (r + 1) * c α ^ 2) ≤
        C * ((∑' α, oscEigenvalue d α ^ r * c α ^ 2) +
          ∑ i : Fin d, ∑' α, oscEigenvalue d α ^ r *
            (Real.sqrt (2 * ((α i : ℝ) + 1)) * c (mova1_up i α)) ^ 2) := by
  set κ : ℝ := 2 ^ |r| with hκ
  have hκ0 : 0 < κ := by positivity
  refine ⟨((d : ℝ) + 1) + κ, by positivity, fun c hs0 hsg => ?_⟩
  have hl0 : ∀ β : MultiIndex d, 0 < oscEigenvalue d β := fun β => oscEigenvalue_pos β
  set R : Fin d → MultiIndex d → ℝ := fun j α =>
    Real.sqrt (2 * ((α j : ℝ) + 1)) * c (mova1_up j α) with hR
  have hsg' : ∀ j, Summable fun α : MultiIndex d => oscEigenvalue d α ^ r * R j α ^ 2 := hsg
  -- the shifted pieces
  set H : Fin d → MultiIndex d → ℝ := fun j β =>
    oscEigenvalue d β ^ r * (if 1 ≤ β j then R j (mova1_dn j β) ^ 2 else 0) with hH
  have hHsq : ∀ j β, (if 1 ≤ β j then R j (mova1_dn j β) ^ 2 else 0) =
      2 * (β j : ℝ) * c β ^ 2 := by
    intro j β
    by_cases h : 1 ≤ β j
    · simp only [h, ↓reduceIte]
      rw [hR]
      simp only
      rw [mul_pow, mova1_up_dn j β h, Real.sq_sqrt (by positivity), mova1_dn_apply]
      have : ((β j - 1 : ℕ) : ℝ) + 1 = (β j : ℝ) := by
        have : ((β j - 1 : ℕ) : ℝ) = (β j : ℝ) - 1 := by
          rw [Nat.cast_sub h]; simp
        rw [this]; ring
      rw [this]
    · have h0 : β j = 0 := by omega
      simp [h0]
  have hHsupp : ∀ j, ∀ β ∉ Set.range (mova1_up (d := d) j), H j β = 0 := by
    intro j β hβ
    by_cases h : 1 ≤ β j
    · exact absurd (mova1_up_ne_dn_range j β h) hβ
    · simp [hH, h]
  have hHup : ∀ j α, H j (mova1_up j α) =
      oscEigenvalue d (mova1_up j α) ^ r * R j α ^ 2 := by
    intro j α
    simp [hH, mova1_up_apply, mova1_dn_up]
  have hcmp : ∀ j α, oscEigenvalue d (mova1_up j α) ^ r ≤ κ * oscEigenvalue d α ^ r := by
    intro j α
    have h2 := mova1_eigen_two_le j α
    exact mova1_rpow_cmp r (hl0 _) (hl0 _) (by rw [mova1_eigen_up]; linarith)
      (by rw [mova1_eigen_up]; linarith)
  have hHsum : ∀ j, Summable (H j) := by
    intro j
    refine ((mova1_up_injective (d := d) j).summable_iff (hHsupp j)).1 ?_
    have hle : ∀ α, (H j ∘ mova1_up j) α ≤ κ * (oscEigenvalue d α ^ r * R j α ^ 2) := by
      intro α
      simp only [Function.comp_apply, hHup]
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hcmp j α) (sq_nonneg _)
    refine Summable.of_nonneg_of_le (fun α => ?_) hle ((hsg' j).mul_left κ)
    simp only [Function.comp_apply, hHup]
    exact mul_nonneg (Real.rpow_nonneg (hl0 _).le _) (sq_nonneg _)
  have hHtsum : ∀ j, ∑' β, H j β ≤ κ * ∑' α, oscEigenvalue d α ^ r * R j α ^ 2 := by
    intro j
    have h := (mova1_up_injective (d := d) j).tsum_eq (f := H j) (fun β hβ => by
      by_contra h; exact hβ (hHsupp j β h))
    rw [← h, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun α => ?_) ((hHsum j).comp_injective (mova1_up_injective j))
      ((hsg' j).mul_left κ)
    simp only [hHup]
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hcmp j α) (sq_nonneg _)
  -- pointwise identity
  have hpt : ∀ β, oscEigenvalue d β ^ (r + 1) * c β ^ 2 =
      ((d : ℝ) + 1) * (oscEigenvalue d β ^ r * c β ^ 2) + ∑ j, H j β := by
    intro β
    rw [Real.rpow_add_one (hl0 β).ne']
    have hlam := mova1_eigen_split (d := d) β
    have : ∑ j, H j β = oscEigenvalue d β ^ r * (2 * (∑ j : Fin d, (β j : ℝ)) * c β ^ 2) := by
      simp only [hH, ← Finset.mul_sum]
      congr 1
      rw [Finset.sum_congr rfl fun j _ => hHsq j β, ← Finset.sum_mul, ← Finset.mul_sum]
    rw [this]
    linear_combination (oscEigenvalue d β ^ r * c β ^ 2) * hlam
  have hsum2 : Summable fun β => ∑ j, H j β := summable_sum fun j _ => hHsum j
  have hsumm : Summable (fun α => oscEigenvalue d α ^ (r + 1) * c α ^ 2) := by
    rw [show (fun α => oscEigenvalue d α ^ (r + 1) * c α ^ 2) =
      fun β => ((d : ℝ) + 1) * (oscEigenvalue d β ^ r * c β ^ 2) + ∑ j, H j β from funext hpt]
    exact (hs0.mul_left _).add hsum2
  refine ⟨hsumm, ?_⟩
  have htot : ∑' β, oscEigenvalue d β ^ (r + 1) * c β ^ 2 =
      ((d : ℝ) + 1) * ∑' β, oscEigenvalue d β ^ r * c β ^ 2 + ∑ j, ∑' β, H j β := by
    rw [tsum_congr hpt, (hs0.mul_left _).tsum_add hsum2, tsum_mul_left,
      Summable.tsum_finsetSum fun j _ => hHsum j]
  have hA : 0 ≤ ∑' β, oscEigenvalue d β ^ r * c β ^ 2 :=
    tsum_nonneg fun α => mul_nonneg (Real.rpow_nonneg (hl0 α).le _) (sq_nonneg _)
  have hB : 0 ≤ ∑ j : Fin d, ∑' α, oscEigenvalue d α ^ r * R j α ^ 2 :=
    Finset.sum_nonneg fun j _ =>
      tsum_nonneg fun α => mul_nonneg (Real.rpow_nonneg (hl0 α).le _) (sq_nonneg _)
  have hS : ∑ j, ∑' β, H j β ≤ κ * ∑ j : Fin d, ∑' α, oscEigenvalue d α ^ r * R j α ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hHtsum j
  show ∑' β, oscEigenvalue d β ^ (r + 1) * c β ^ 2 ≤
    (((d : ℝ) + 1) + κ) * ((∑' α, oscEigenvalue d α ^ r * c α ^ 2) +
      ∑ j : Fin d, ∑' α, oscEigenvalue d α ^ r * R j α ^ 2)
  rw [htot]
  have hd : (0 : ℝ) ≤ (d : ℝ) + 1 := by positivity
  nlinarith [mul_nonneg hd hB, mul_nonneg hκ0.le hA]

end HRS.MS.BreakdownS67
