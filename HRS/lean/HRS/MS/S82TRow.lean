import HRS.MS.S82QT2

/-!
# S8.2 (S82T): single-anchor capped row and elementary log bounds for R06
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82T
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2 HRS.MS.S82Q HRS.MS.S82N HRS.MS.S82P

lemma s82t_logN_sq_le {N : ℕ} (hN : 1 ≤ N) : logN N ^ 2 ≤ 12 * N := by
  have h1 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL := s82q_logN_nonneg hN
  set y := Real.sqrt (Real.exp 1 * N) with hy
  have hy0 : 0 < y := Real.sqrt_pos.2 (by positivity)
  have hy2 : y ^ 2 = Real.exp 1 * N := Real.sq_sqrt (by positivity)
  have hlog : logN N = 2 * Real.log y := by
    unfold logN
    rw [← hy2, Real.log_pow]
    norm_num
  have hle : Real.log y ≤ y := (Real.log_le_sub_one_of_pos hy0).trans (by linarith)
  have h2 : logN N ≤ 2 * y := by rw [hlog]; linarith
  have he : Real.exp 1 ≤ 3 := (Real.exp_one_lt_d9).le.trans (by norm_num)
  have h3 : logN N ^ 2 ≤ (2 * y) ^ 2 := pow_le_pow_left₀ (by linarith) h2 2
  have h4 : (2 * y) ^ 2 = 4 * (Real.exp 1 * N) := by rw [mul_pow, hy2]; ring
  nlinarith

/-- Capped single-anchor row (one pin `x`): `int <z>^M pole(x,z) min(1,(1+q(x-z))/N) dmu <= C <x>^M logN / N`. -/
theorem s82t_row_cap (d : ℕ) (hd : 2 ≤ d) (M G c : ℝ) (hM : 0 ≤ M) (hG : 0 < G) (hc : 0 < c)
    (q : Euc d → ℝ) (hq : ShortRangePole d q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ, HRS.Whole.IsProbDensity rho → HasR2GaussianUpper G c rho →
      ∀ N : ℕ, 2 ≤ N → ∀ x : Euc d,
      ∫⁻ z, ENNReal.ofReal (jbracket z ^ M * pole x z * min 1 ((1 + q (x - z)) / N))
          ∂HRS.Whole.withDensityReal rho ≤ ENNReal.ofReal (C * jbracket x ^ M * logN N / N) := by
  obtain ⟨K1, hK1, hqK⟩ := s82p_q_le (s82q_pole_bridge hq)
  have hK : 1 ≤ 1 + K1 := by linarith
  obtain ⟨C, hC, hanch⟩ := s82p_anchor hd M G c (1 + K1) hM hG.le hc hK
  refine ⟨C, hC, fun rho hρ hρG N hN x => ?_⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  refine le_trans (lintegral_mono_ae ((s82q_ae_ne hd rho x).mono fun z hz => ?_))
    (hanch rho hρ hρG N hN x)
  apply ENNReal.ofReal_le_ofReal
  have hxz : x - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
  have h1 : q (x - z) ≤ K1 * pole x z := hqK _ hxz
  have hP := s82q_pole_ge_one x z
  have hj := s82q_jb_rpow_nonneg M z
  have hmin : min 1 ((1 + q (x - z)) / N) ≤ min 1 ((1 + K1) * pole x z / N) :=
    min_le_min_left _ (div_le_div_of_nonneg_right (by nlinarith) hNr.le)
  show jbracket z ^ M * pole x z * min 1 ((1 + q (x - z)) / N) ≤
    jbracket z ^ M * (pole x z * min 1 ((1 + K1) * pole x z / N))
  calc jbracket z ^ M * pole x z * min 1 ((1 + q (x - z)) / N)
      = jbracket z ^ M * (pole x z * min 1 ((1 + q (x - z)) / N)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmin (by linarith)) hj

end HRS.MS.S82T
