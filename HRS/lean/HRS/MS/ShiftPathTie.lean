import HRS.MS.ShiftFldAux29
import HRS.MS.CritPathTie

/-!
# S79P: `shifted_field_path` (S7.9), the frozen statement

Proof: S2.1(i) (`whole_space_stationary_proof`) applied to the time-shifted canonical realization
`(X_u, W_{u+·} - W_u, X_{u+·})`, `u = a₀`, whose window `ζ_N^{0+·}` is the window `ζ_N^{a₀+·}` of `X` (`s79p_zetaPathW_shift`), together
with the stationarity of the Gaussian window (`s79g_gauss_stationary`, the Lyapunov identity for the susceptibility covariance), and the
deterministic comparison `s79_core`.  Unlike `shifted_field_path_of_S21` no particle path-law stationarity is needed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

namespace HRS.Whole.S79

open HRS (Euc)

theorem shifted_field_path_proof : type_of% @HRS.Whole.shifted_field_path := by
  intro d s hd hs hsd a β ha hβ T hT
  have h21 : HRS.Whole.WholeSpaceStationaryStatement := HRS.MS.S21.whole_space_stationary_proof
  have hd0 : (0 : ℝ) < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hs0 : 0 ≤ s := by linarith
  have hmd : (d : ℝ) < ((wholeSpaceIndex d : ℕ) : ℝ) := by
    unfold wholeSpaceIndex
    push_cast
    linarith
  obtain ⟨C₀, C, hcomp, hmain⟩ := h21 hd s hs0 hsd a β ha hβ T hT
  obtain ⟨K, hK0, hK⟩ := s79_core hd hs hsd ha hβ hmd (s := s)
  refine ⟨C₀, max C 0 + K, hcomp, ?_⟩
  intro ρβ hρβ N hN Ω _ P _ X₀ W X hR Ω' _ P' _ Z hZ a₀ ha₀
  have hRN := hR
  -- Gaussian side
  obtain ⟨hg1, hg2⟩ := HRS.MS.S79G.s79g_gauss_stationary hd (by linarith) hsd ha hβ T hT ρβ hρβ P' Z hZ a₀ ha₀
  -- particle side: S2.1(i) for the shifted realization
  have hBr := s79p_isVectorBrownian_shift hR.brownian a₀.toNNReal
  have hInd := s79p_indep_shift hR a₀.toNNReal
  have hInit : law P (X a₀.toNNReal) = canonicalGibbs (rieszKernel d s) (confinement a) N β :=
    s79p_law_init hR a₀.toNNReal
  have hSol := s79p_strongSolution_shift hR a₀.toNNReal T
  obtain ⟨hz1, hz2, hz3, hz4⟩ := hmain ρβ hρβ N hN hRN.invariant P (X a₀.toNNReal)
    (s79p_shiftW a₀.toNNReal W) (s79p_shiftX a₀.toNNReal X) hBr hInd hInit hSol P' Z (hZ T)
  have hzeta : zetaPathW (wholeSpaceIndex d) T 0 P (s79p_shiftX a₀.toNNReal X) =
      zetaPathW (wholeSpaceIndex d) T a₀ P X :=
    funext fun ζ => (s79p_zetaPathW_shift P T X ha₀ ζ).symm
  rw [hzeta] at hz1 hz3 hz4
  obtain ⟨c1, c2, c3, c4⟩ := hK T a₀ ρβ hρβ N hN P X₀ W X hR P' Z hz1 hg1
  rw [hg2] at c3 c4
  have hδ0 : 0 ≤ Real.sqrt (deltaN d s N) := Real.sqrt_nonneg _
  have hw0 := s79_localizationRate_nonneg d s C₀ N
  have hpow : 0 ≤ (N : ℝ) ^ (3 / 2 - biasP d s - biasTheta d s) :=
    Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hCm : 0 ≤ max C 0 := le_max_right _ _
  refine ⟨c1, c2, ?_, ?_⟩
  · refine c3.trans ?_
    have h1 : C * (Real.sqrt (deltaN d s N) + localizationRate d s C₀ N) ≤
        max C 0 * (Real.sqrt (deltaN d s N) + localizationRate d s C₀ N) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (add_nonneg hδ0 hw0)
    have h2 : K * (N : ℝ) ^ (3 / 2 - biasP d s - biasTheta d s) ≤
        (max C 0 + K) * (N : ℝ) ^ (3 / 2 - biasP d s - biasTheta d s) := by
      nlinarith [mul_nonneg hCm hpow]
    have h3 : max C 0 * (Real.sqrt (deltaN d s N) + localizationRate d s C₀ N) ≤
        (max C 0 + K) * (Real.sqrt (deltaN d s N) + localizationRate d s C₀ N) := by
      nlinarith [mul_nonneg hK0 (add_nonneg hδ0 hw0)]
    nlinarith
  · refine c4.trans ?_
    have hδp : 0 ≤ deltaN d s N ^ ((3 : ℝ) / 20) :=
      Real.rpow_nonneg (s79_deltaN_pos hs (by omega)).le _
    have hsw : 0 ≤ Real.sqrt (localizationRate d s C₀ N) := Real.sqrt_nonneg _
    have hA : 0 ≤ max C 0 * (deltaN d s N ^ ((3 : ℝ) / 20) +
        Real.sqrt (localizationRate d s C₀ N)) := mul_nonneg hCm (add_nonneg hδp hsw)
    have hB : 0 ≤ K * (N : ℝ) ^ (3 / 2 - biasP d s - biasTheta d s) := mul_nonneg hK0 hpow
    calc _ ≤ ENNReal.ofReal (max C 0 * (deltaN d s N ^ ((3 : ℝ) / 20) +
            Real.sqrt (localizationRate d s C₀ N))) +
          ENNReal.ofReal (K * (N : ℝ) ^ (3 / 2 - biasP d s - biasTheta d s)) :=
          add_le_add (hz4.trans (ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (add_nonneg hδp hsw)))) le_rfl
      _ = ENNReal.ofReal (max C 0 * (deltaN d s N ^ ((3 : ℝ) / 20) +
            Real.sqrt (localizationRate d s C₀ N)) +
          K * (N : ℝ) ^ (3 / 2 - biasP d s - biasTheta d s)) := (ENNReal.ofReal_add hA hB).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          nlinarith [mul_nonneg hK0 (add_nonneg hδp hsw), mul_nonneg hCm hpow]

example := (@shifted_field_path_proof : type_of% @HRS.Whole.shifted_field_path)

end HRS.Whole.S79
