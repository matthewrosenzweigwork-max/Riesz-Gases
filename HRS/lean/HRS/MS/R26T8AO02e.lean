import HRS.MS.R26T8AO02d

/-!
# S8.2 T8A O02 (part e): pointwise `B`-linear bounds of the pair statistic and the error statistic
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82W HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_o02_wBq_lin (M B : ℝ) {N : ℕ} (i j : Fin N) (X : EucConfig d N) :
    wBq M B i j X = B * wBq M 1 i j X := by
  unfold wBq; ring

set_option maxHeartbeats 6400000 in
theorem r26t8a_o02_stat_bounds (hd : 2 ≤ d) (a beta M : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    {rho : Euc d → ℝ} (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) :
    ∃ K1 Cb M' : ℝ, 0 ≤ K1 ∧ 0 ≤ Cb ∧ M ≤ M' ∧ ∀ (f : Euc d → ℝ) (B : ℝ), 0 ≤ B →
      ∀ Q : Euc d → Euc d → ℝ, PairCorrector a beta rho M B f Q → ∀ (N : ℕ) (X : EucConfig d N),
        X ∉ eucCollisionSet d N →
        |pairStatistic Q X| ≤ 5 * (N : ℝ) ^ (-(3 / 2 : ℝ)) * (B * r26t8a_o02_Wb M X) ∧
        |errorStatistic (critCoeff d a beta rho) rho Q X| ≤
          B * ((2 / (N : ℝ)) * (N : ℝ) ^ (-(3 / 2 : ℝ)) * r26t8a_o02_Wb M X +
            (N : ℝ) ^ (-(5 / 2 : ℝ)) * (K1 * r26t8a_o02_Tr M' X + Cb * r26t8a_o02_Pj M' X)) := by
  obtain ⟨hFs, hFb⟩ := r26t8a_thermal_force d hd a beta ha hbeta rho hrho
  obtain ⟨BF, hBF0, hBFb⟩ := hFb 0
  have hBF : ∀ u, ‖forceMean rho u‖ ≤ BF := fun u => by
    have := hBFb u
    rw [norm_iteratedFDeriv_zero] at this
    linarith [norm_nonneg (fderiv ℝ (iteratedFDeriv ℝ 0 (forceMean rho)) u u)]
  obtain ⟨K, M', hK0, hMM', hEnv⟩ := r26t8a_a01_env d hd a beta M hM
  refine ⟨K * (1 + BF), 2 * criticalS d + 4 * BF, M', by positivity, by
    have : (0 : ℝ) < criticalS d := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      unfold criticalS; linarith
    positivity, hMM', ?_⟩
  intro f B hB Q hQ N X hX
  have hnd : ∀ i j : Fin N, i ≠ j → X i ≠ X j := fun i j hij h => hX ⟨i, j, hij, h⟩
  have hk0 : 0 ≤ (N : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hk5 : 0 ≤ (N : ℝ) ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hWb0 : 0 ≤ r26t8a_o02_Wb M X := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    wBq_nonneg M zero_le_one i j X
  -- pair statistic
  obtain ⟨-, hjet⟩ := w_pairstat_jets (N := N) hd hQ hB 0
  have h1 : |pairStatistic Q X| ≤ 5 * (N : ℝ) ^ (-(3 / 2 : ℝ)) * (B * r26t8a_o02_Wb M X) := by
    have := hjet X hX
    simp only [sub_zero, abs_zero, add_zero] at this
    have hs : ∑ i, ∑ j ∈ Finset.univ.erase i, wBq M B i j X = B * r26t8a_o02_Wb M X := by
      unfold r26t8a_o02_Wb
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => r26t8a_o02_wBq_lin M B i j X
    rw [hs] at this
    have h2 : |pairStatistic Q X| ≤ |pairStatistic Q X| + ‖fderiv ℝ (fun Y => pairStatistic Q Y) X‖ +
        ‖iteratedFDeriv ℝ 2 (fun Y => pairStatistic Q Y) X‖ := by
      have := norm_nonneg (fderiv ℝ (fun Y : EucConfig d N => pairStatistic Q Y) X)
      have := norm_nonneg (iteratedFDeriv ℝ 2 (fun Y : EucConfig d N => pairStatistic Q Y) X)
      linarith
    exact h2.trans this
  refine ⟨h1, ?_⟩
  -- error statistic
  have hB' : (0 : ℝ) ≤ B := hB
  have t1 : |pairStatistic (pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q) X| ≤
      (N : ℝ) ^ (-(3 / 2 : ℝ)) * (B * r26t8a_o02_Wb M X) := by
    unfold pairStatistic Phase2S82.pairSum
    rw [abs_mul, abs_of_nonneg hk0]
    refine mul_le_mul_of_nonneg_left ?_ hk0
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    unfold r26t8a_o02_Wb
    simp only [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    have := hQ.nonlocal.2 (X i) (X j) (hnd i j hij)
    refine this.trans (le_of_eq ?_)
    unfold wBq; ring
  have t2 : |Phase2S82.tripleSum (tripleG (critCoeff d a beta rho) rho Q) X| ≤ (K * (1 + BF)) * (B * r26t8a_o02_Tr M' X) := by
    unfold Phase2S82.tripleSum r26t8a_o02_Tr
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    have hki : k ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
    have hkj : k ≠ j := Finset.ne_of_mem_erase hk
    have := hEnv rho f B hB Q hQ BF hBF0 hBF (X i) (X j) (X k) (hnd i j hij) (hnd i k hki.symm) (hnd j k hkj.symm)
    refine this.trans (le_of_eq ?_)
    ring
  have t3 : |Phase2S82.pairSum (repeatedB rho Q) X| ≤ (2 * criticalS d + 4 * BF) * (B * r26t8a_o02_Pj M' X) := by
    unfold Phase2S82.pairSum r26t8a_o02_Pj
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    simp only [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    have := r26t8a_a02_repeatedB_bound d hd (M := M) (M' := M') hMM' hB hQ hBF0 hBF (hnd i j hij)
    refine this.trans (le_of_eq ?_)
    ring
  unfold errorStatistic
  have hN0 : (0 : ℝ) ≤ 2 / (N : ℝ) := by positivity
  have e1 : |-(2 / (N : ℝ)) * pairStatistic (pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q) X| ≤
      (2 / (N : ℝ)) * ((N : ℝ) ^ (-(3 / 2 : ℝ)) * (B * r26t8a_o02_Wb M X)) := by
    rw [abs_mul, abs_neg, abs_of_nonneg hN0]
    exact mul_le_mul_of_nonneg_left t1 hN0
  have e2 : |(N : ℝ) ^ (-(5 / 2 : ℝ)) * (Phase2S82.tripleSum (tripleG (critCoeff d a beta rho) rho Q) X - Phase2S82.pairSum (repeatedB rho Q) X)| ≤
      (N : ℝ) ^ (-(5 / 2 : ℝ)) * ((K * (1 + BF)) * (B * r26t8a_o02_Tr M' X) +
        (2 * criticalS d + 4 * BF) * (B * r26t8a_o02_Pj M' X)) := by
    rw [abs_mul, abs_of_nonneg hk5]
    refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add t2 t3)) hk5
  refine (abs_add_le _ _).trans ((add_le_add e1 e2).trans (le_of_eq ?_))
  ring

end HRS.MS.R26T8A
