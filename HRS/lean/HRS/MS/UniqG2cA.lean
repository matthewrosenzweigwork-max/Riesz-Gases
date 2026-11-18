import HRS.MS.UniqM1Fin

/-!
# G2c, part A: mollification of a test function, `∫ u φ - ∫ z_ε φ = O(ε)`

For `φ` smooth with compact support and `u` with `LocMass B u`:
`|∫ u φ - ∫ moll ε u · φ| ≤ A |B| ε` for `0 < ε ≤ 1`, with `A` depending only on `φ` (and `d`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqG2c

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqM1

variable {d : ℕ}

/-- The mollified test function is within `C ε` of `φ` when `φ` is `C`-Lipschitz. -/
theorem g2c_moll_sub_le {φ : Euc d → ℝ} {C : NNReal} (hφ : LipschitzWith C φ)
    (hφi : LocallyIntegrable φ volume) {ε : ℝ} (hε : 0 < ε) (hφc : HasCompactSupport φ) (y : Euc d) :
    |moll d ε φ y - φ y| ≤ C * ε := by
  have hco : Continuous fun x : Euc d => eta d ε (y - x) :=
    eta_contDiff.continuous.comp (continuous_const.sub continuous_id)
  have hcs : HasCompactSupport fun x : Euc d => eta d ε (y - x) :=
    (eta_hasCompactSupport hε).comp_homeomorph (Homeomorph.subLeft y)
  have hone : ∫ x, eta d ε (y - x) = 1 := by
    rw [integral_sub_left_eq_self (fun x => eta d ε x) volume y]
    exact integral_eta hε
  have hint1 : Integrable (fun x => eta d ε (y - x)) volume := hco.integrable_of_hasCompactSupport hcs
  have hint2 : Integrable (fun x => eta d ε (y - x) * φ x) volume := by
    have := hφi.integrable_smul_left_of_hasCompactSupport hco hcs
    simpa [smul_eq_mul, mul_comm] using this
  have h1 : moll d ε φ y - φ y = ∫ x, eta d ε (y - x) * (φ x - φ y) := by
    have : ∫ x, eta d ε (y - x) * (φ x - φ y) =
        (∫ x, eta d ε (y - x) * φ x) - ∫ x, eta d ε (y - x) * φ y := by
      rw [← integral_sub hint2 (hint1.mul_const (φ y))]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp [mul_sub])
    rw [this, integral_mul_const, hone, one_mul]; rfl
  rw [h1, ← Real.norm_eq_abs]
  have hbd : Integrable (fun x => (C * ε : ℝ) * eta d ε (y - x)) volume := hint1.const_mul _
  refine (norm_integral_le_of_norm_le hbd (Eventually.of_forall fun x => ?_)).trans ?_
  · rw [norm_mul, Real.norm_of_nonneg (eta_nonneg hε _)]
    by_cases h0 : eta d ε (y - x) = 0
    · simp [h0]
    · have hlt : ‖y - x‖ < ε := by
        have := eta_support hε (Function.mem_support.2 h0)
        simpa using this
      have hd : ‖φ x - φ y‖ ≤ C * ε := by
        have := hφ.dist_le_mul x y
        rw [dist_eq_norm, dist_eq_norm] at this
        have h2 : ‖x - y‖ ≤ ε := by rw [norm_sub_rev]; exact hlt.le
        calc ‖φ x - φ y‖ ≤ C * ‖x - y‖ := this
          _ ≤ C * ε := by gcongr
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hd (eta_nonneg hε _)
  · rw [integral_const_mul, hone, mul_one]

theorem g2c_moll_support {φ : Euc d → ℝ} {R : ℝ} (hR : tsupport φ ⊆ closedBall 0 R) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (y : Euc d) (hy : y ∉ closedBall (0 : Euc d) (R + 1)) :
    moll d ε φ y = 0 := by
  unfold moll
  refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
  show eta d ε (y - x) * φ x = 0
  by_contra hne
  have h1 : eta d ε (y - x) ≠ 0 := left_ne_zero_of_mul hne
  have h2 : φ x ≠ 0 := right_ne_zero_of_mul hne
  have hx : x ∈ closedBall (0 : Euc d) R := hR (subset_tsupport _ h2)
  have hyx : ‖y - x‖ < ε := by simpa using eta_support hε (Function.mem_support.2 h1)
  apply hy
  rw [mem_closedBall_zero_iff] at hx ⊢
  calc ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
    _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
    _ ≤ R + 1 := by linarith

theorem g2c_mollTest_close {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (B : ℝ) (u : Euc d → ℝ), LocMass B u → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      |(∫ x, u x * φ x) - ∫ x, moll d ε u x * φ x| ≤ A * |B| * ε := by
  obtain ⟨C, hC⟩ := hφ.lipschitzWith_of_hasCompactSupport hφc (by simp)
  obtain ⟨R, hR⟩ := hφc.isCompact.isBounded.subset_closedBall (0 : Euc d)
  have hR' : tsupport φ ⊆ closedBall 0 R := hR
  obtain ⟨K, hK0, hK⟩ := exists_closedBall_l1_real d (R + 1)
  refine ⟨K * C, by positivity, fun B u hu ε hε hε1 => ?_⟩
  have hφl : LocallyIntegrable φ volume := hφ.continuous.locallyIntegrable
  have hmc : Continuous (moll d ε φ) := (moll_contDiff hε hφl).continuous
  have hmcs : HasCompactSupport (moll d ε φ) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Euc d) (R + 1))
      (fun y hy => by
        by_contra h
        exact hy (g2c_moll_support hR' hε hε1 y h))
  have hex := integral_moll_mul' hε hu hφ.continuous hφc
  have hex' : ∫ x, moll d ε u x * φ x = ∫ y, u y * moll d ε φ y := hex
  rw [hex']
  have i1 : Integrable (fun y => u y * φ y) volume := by
    simpa [smul_eq_mul] using
      hu.locallyIntegrable.integrable_smul_right_of_hasCompactSupport hφ.continuous hφc
  have i2 : Integrable (fun y => u y * moll d ε φ y) volume := by
    simpa [smul_eq_mul] using
      hu.locallyIntegrable.integrable_smul_right_of_hasCompactSupport hmc hmcs
  rw [← integral_sub i1 i2, ← Real.norm_eq_abs]
  have hball : Integrable (fun y => (closedBall (0 : Euc d) (R + 1)).indicator
      (fun y => ‖u y‖ * (C * ε)) y) volume := by
    refine (integrable_indicator_iff measurableSet_closedBall).2 ?_
    exact ((hu.locallyIntegrable.integrableOn_isCompact (isCompact_closedBall _ _)).norm).mul_const _
  refine (norm_integral_le_of_norm_le hball (Eventually.of_forall fun y => ?_)).trans ?_
  · by_cases hy : y ∈ closedBall (0 : Euc d) (R + 1)
    · rw [Set.indicator_of_mem hy, ← mul_sub, norm_mul]
      have := g2c_moll_sub_le hC hφl hε hφc y
      have h3 : ‖φ y - moll d ε φ y‖ ≤ C * ε := by
        rw [norm_sub_rev, Real.norm_eq_abs]; exact this
      exact mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    · have h1 : φ y = 0 := by
        by_contra h
        have := hR' (subset_tsupport _ h)
        apply hy
        rw [mem_closedBall_zero_iff] at this ⊢; linarith
      simp [Set.indicator_of_notMem hy, h1, g2c_moll_support hR' hε hε1 y hy]
  · rw [integral_indicator measurableSet_closedBall, integral_mul_const]
    have := hK |B| u (abs_nonneg B) (hu.mono_B (by simp)) 0
    calc (∫ y in closedBall (0 : Euc d) (R + 1), ‖u y‖) * (C * ε) ≤ (K * |B|) * (C * ε) := by
          gcongr
      _ = K * C * |B| * ε := by ring

end HRS.MS.UniqG2c
