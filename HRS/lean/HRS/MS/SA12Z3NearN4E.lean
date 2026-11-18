import HRS.MS.SA12Z3NearN4D
import HRS.MS.SA12Z3NearN7D
import HRS.MS.UniqN4bB
import HRS.MS.UniqN4a

/-!
# S.A.12 N4 (SA12Z3), part E: the difference identity and the `H¹ → L²` pairing bound for `T`
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

/-- The antisymmetrized pairing, in the limit `ε → 0`. -/
theorem sa12z3_diff (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i : Fin d) {Z a : Euc d → ℝ}
    (hZ : ContDiff ℝ 2 Z) (hZc : HasCompactSupport Z) (ha : ContDiff ℝ 1 a) (l j : Fin d) :
    (∫ x, (D1 l Z x * a x) * firstRiesz d s i (D1 j Z) x) -
        (∫ x, (D1 j Z x * a x) * firstRiesz d s i (D1 l Z) x) =
      (∫ x, (Z x * D1 j a x) * firstRiesz d s i (D1 l Z) x) -
        ∫ x, (Z x * D1 l a x) * firstRiesz d s i (D1 j Z) x := by
  have hf : ∀ k, ContDiff ℝ 1 (D1 k Z) := fun k => D1_contDiff hZ k
  have hfc : ∀ k, HasCompactSupport (D1 k Z) := fun k => D1_supp hZc k
  have hac := ha.continuous
  have ha2 : ∀ k, Continuous (D1 k a) := fun k => (ha.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have t1 := sa12z3_S_lim hd hs0 hsd i ((hf l).continuous.mul hac) ((hfc l).mul_right) (hf j) (hfc j)
  have t2 := sa12z3_S_lim hd hs0 hsd i ((hf j).continuous.mul hac) ((hfc j).mul_right) (hf l) (hfc l)
  have t3 := sa12z3_S_lim hd hs0 hsd i (hZ.continuous.mul (ha2 j)) (hZc.mul_right) (hf l) (hfc l)
  have t4 := sa12z3_S_lim hd hs0 hsd i (hZ.continuous.mul (ha2 l)) (hZc.mul_right) (hf j) (hfc j)
  have hL := t1.sub t2
  have hR := t3.sub t4
  refine tendsto_nhds_unique hL (hR.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (sa12z3_diff_eps s i hε hZ hZc ha l j).symm

theorem sa12z3_pow_interp {A B σ : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) (hσ1 : σ ≤ 1) :
    A ^ (1 - σ) * B ^ σ ≤ B := by
  have h1 : A ^ (1 - σ) ≤ B ^ (1 - σ) := Real.rpow_le_rpow hA hAB (by linarith)
  have hB : 0 ≤ B := hA.trans hAB
  calc A ^ (1 - σ) * B ^ σ ≤ B ^ (1 - σ) * B ^ σ :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hB _)
    _ = B := by
        rw [← Real.rpow_add' hB (by linarith : 1 - σ + σ ≠ 0)]
        simp

/-- `|∫ g T w| ≤ C ‖g‖₂ (‖w‖₂ + ‖∇w‖₂)`. -/
theorem sa12z3_T_pair (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hs1 : (d : ℝ) - 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin d) (w g : Euc d → ℝ), ContDiff ℝ 1 w → HasCompactSupport w →
      Continuous g → HasCompactSupport g →
      |∫ x, g x * firstRiesz d s i w x| ≤ C * Real.sqrt (∫ x, g x ^ 2) *
        (Real.sqrt (∫ x, w x ^ 2) + Real.sqrt (∫ x, ‖fderiv ℝ w x‖ ^ 2)) := by
  obtain ⟨CG, hCG⟩ := HRS.MS.UniqN0.n0_kcd_global hd hsd hs1.le
  refine ⟨|CG| * (1 + Real.sqrt d), by positivity, fun i w g hw hwc hg hgc => ?_⟩
  have hK : firstRiesz d s i w = HRS.Whole.AppendixALemmas.kernelConvDeriv d s i w :=
    funext fun x => sa12z3_firstRiesz_eq' hs0 hsd i hw hwc x
  have hwL : MemLp w 2 volume := hw.continuous.memLp_of_hasCompactSupport hwc
  have hgL : MemLp g 2 volume := hg.memLp_of_hasCompactSupport hgc
  obtain ⟨hTL, hTb⟩ := hCG i w hw hwc
  set A : ℝ := Real.sqrt (∫ x, w x ^ 2) with hA
  set Γ : ℝ := Real.sqrt (∫ x, ‖fderiv ℝ w x‖ ^ 2) with hΓ
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hΓ0 : 0 ≤ Γ := Real.sqrt_nonneg _
  have h0 : eLpNorm w 2 volume ≤ ENNReal.ofReal A := (sa12z3_eLp_eq hwL).le
  have h1 : ∫ x, ‖fderiv ℝ w x‖ ^ 2 ≤ Γ ^ 2 := by
    rw [hΓ, Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)]
  obtain ⟨hmem, hE0, hE1⟩ := HRS.MS.UniqN4b.n4b_sob_one hw hwc hA0 hΓ0 h0 h1
  have hB0 : 0 ≤ A + Real.sqrt d * Γ := by positivity
  have hAB : A ≤ A + Real.sqrt d * Γ := by
    have : 0 ≤ Real.sqrt d * Γ := by positivity
    linarith
  have hσ0 : 0 ≤ s + 1 - d := by linarith
  have hσ1 : s + 1 - d ≤ 1 := by linarith
  have hEσ := HRS.MS.UniqN4a.n4a_interp_E_bound (s + 1 - d) hσ0 hσ1 hmem hA0 hB0 hE0 hE1
  have hEσ' : sobolevNormE (s + 1 - d) w ≤ ENNReal.ofReal (A + Real.sqrt d * Γ) :=
    hEσ.trans (ENNReal.ofReal_le_ofReal (sa12z3_pow_interp hA0 hAB hσ1))
  have hT2 : eLpNorm (HRS.Whole.AppendixALemmas.kernelConvDeriv d s i w) 2 volume ≤
      ENNReal.ofReal (|CG| * (A + Real.sqrt d * Γ)) := by
    refine hTb.trans ?_
    rw [ENNReal.ofReal_mul (abs_nonneg _)]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (le_abs_self CG)) hEσ'
  have hT3 : Real.sqrt (∫ x, (HRS.Whole.AppendixALemmas.kernelConvDeriv d s i w x) ^ 2) ≤
      |CG| * (A + Real.sqrt d * Γ) := by
    rw [sa12z3_eLp_eq hTL] at hT2
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hT2
  rw [hK]
  have hcs := HRS.MS.UniqN3a.cs_real hgL hTL
  refine hcs.trans ?_
  have hB1 : A + Real.sqrt d * Γ ≤ (1 + Real.sqrt d) * (A + Γ) := by
    have : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
    nlinarith [mul_nonneg this hA0]
  calc Real.sqrt (∫ x, g x ^ 2) * Real.sqrt (∫ x, (HRS.Whole.AppendixALemmas.kernelConvDeriv d s i w x) ^ 2)
      ≤ Real.sqrt (∫ x, g x ^ 2) * (|CG| * ((1 + Real.sqrt d) * (A + Γ))) :=
        mul_le_mul_of_nonneg_left (hT3.trans (mul_le_mul_of_nonneg_left hB1 (abs_nonneg _)))
          (Real.sqrt_nonneg _)
    _ = |CG| * (1 + Real.sqrt d) * Real.sqrt (∫ x, g x ^ 2) * (A + Γ) := by ring

end HRS.MH.AdjointRd.Phase2SA12Near
