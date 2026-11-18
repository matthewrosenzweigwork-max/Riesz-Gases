import HRS.MS.S82RN1

/-!
# S8.2 R02 (S82R), N2: the high-level sets of two rows are disjoint at large levels
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace HRS.MS.S82R
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

/-- If `q(w) > L > 2K` then `|w| < 1` and `L/(2K) < |w|^{-s}`. -/
lemma s82r_level_ball {q : Euc d → ℝ} {K1 : ℝ} (hK1 : 0 < K1) {s : ℝ} (hs : 0 < s)
    (hqK : ∀ w : Euc d, w ≠ 0 → q w ≤ K1 * (1 + (min 1 ‖w‖) ^ (-s)))
    {L : ℝ} (hL : 2 * K1 < L) {w : Euc d} (hw : w ≠ 0) (hlev : L < q w) :
    ‖w‖ < 1 ∧ L / (2 * K1) < ‖w‖ ^ (-s) := by
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have h1 := hqK w hw
  by_cases h : ‖w‖ < 1
  · refine ⟨h, ?_⟩
    rw [min_eq_right h.le] at h1
    have hp : 1 ≤ ‖w‖ ^ (-s) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hn h.le (by linarith)
    have : L < K1 * (1 + ‖w‖ ^ (-s)) := lt_of_lt_of_le hlev h1
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  · exfalso
    push Not at h
    rw [min_eq_left h, Real.one_rpow] at h1
    linarith


lemma s82r_disjoint (hd : 1 ≤ d) {q : Euc d → ℝ} (hq : ShortRangePole d q) :
    ∃ L₁ C₂ : ℝ, 1 ≤ L₁ ∧ 0 ≤ C₂ ∧ ∀ (z p u : Euc d) (L : ℝ), z ≠ p → u ≠ z → u ≠ p → L₁ ≤ L →
      C₂ * q (z - p) < L → ¬ (L < q (z - u) ∧ L < q (p - u)) := by
  obtain ⟨K1, hK1, hqK⟩ := HRS.MS.S82P2.s82p2_q_le hq
  obtain ⟨r0, c0, C0, hr0, hr1, hc0, hnear⟩ := hq.near
  have hs : 0 < criticalS d := by
    unfold criticalS
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set K : ℝ := K1 + 1 with hK
  have hKpos : 0 < K := by rw [hK]; linarith
  have hqK' : ∀ w : Euc d, w ≠ 0 → q w ≤ K * (1 + (min 1 ‖w‖) ^ (-criticalS d)) := by
    intro w hw
    refine (hqK w hw).trans ?_
    have : 0 ≤ 1 + (min 1 ‖w‖) ^ (-criticalS d) := by
      have := Real.rpow_nonneg (le_min zero_le_one (norm_nonneg w)) (-criticalS d); linarith
    rw [hK]; nlinarith
  have h2r : 1 ≤ (2 / r0) ^ criticalS d :=
    Real.one_le_rpow (by rw [le_div_iff₀ hr0]; linarith) hs.le
  refine ⟨2 * K * (2 / r0) ^ criticalS d + 1, 2 * K * (2 : ℝ) ^ criticalS d / c0, by nlinarith, by positivity,
    fun z p u L hzp huz hup hL hC => ?_⟩
  rintro ⟨ha, hb⟩
  have hL2K : 2 * K < L := by nlinarith
  have hw1 : z - u ≠ 0 := sub_ne_zero.2 (Ne.symm huz)
  have hw2 : p - u ≠ 0 := sub_ne_zero.2 (Ne.symm hup)
  obtain ⟨hX1, hX2⟩ := s82r_level_ball hKpos hs hqK' hL2K hw1 ha
  obtain ⟨hY1, hY2⟩ := s82r_level_ball hKpos hs hqK' hL2K hw2 hb
  have hLK : (2 / r0) ^ criticalS d < L / (2 * K) := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  have hsmall : ∀ w : Euc d, w ≠ 0 → L / (2 * K) < ‖w‖ ^ (-criticalS d) → ‖w‖ < r0 / 2 := by
    intro w hw h
    by_contra hge
    push Not at hge
    have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
    have := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < r0 / 2) hge (by linarith : -criticalS d ≤ 0)
    have e : (r0 / 2) ^ (-criticalS d) = (2 / r0) ^ criticalS d := by
      rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity)]; congr 1; field_simp
    rw [e] at this
    linarith
  have hX := hsmall _ hw1 hX2
  have hY := hsmall _ hw2 hY2
  have hzp' : 0 < ‖z - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hzp)
  have htri : ‖z - p‖ ≤ ‖z - u‖ + ‖p - u‖ := by
    calc ‖z - p‖ = ‖(z - u) - (p - u)‖ := by congr 1; abel
      _ ≤ ‖z - u‖ + ‖p - u‖ := norm_sub_le _ _
  have hzr : ‖z - p‖ ≤ r0 := by linarith
  have hlow := (hnear (z - p) hzp' hzr).1
  -- the larger of the two distances
  obtain ⟨m, hm1, hm2, hm3⟩ : ∃ m : ℝ, ‖z - u‖ ≤ m ∧ ‖p - u‖ ≤ m ∧ L / (2 * K) < m ^ (-criticalS d) := by
    by_cases hxy : ‖z - u‖ ≤ ‖p - u‖
    · exact ⟨‖p - u‖, hxy, le_rfl, hY2⟩
    · exact ⟨‖z - u‖, le_rfl, (not_le.1 hxy).le, hX2⟩
  have hmpos : 0 < m := lt_of_lt_of_le (norm_pos_iff.2 hw1) hm1
  have h2m : ‖z - p‖ ≤ 2 * m := by linarith
  have hpow : (2 * m) ^ (-criticalS d) ≤ ‖z - p‖ ^ (-criticalS d) :=
    Real.rpow_le_rpow_of_nonpos hzp' h2m (by linarith)
  have hsplit : (2 * m) ^ (-criticalS d) = 2 ^ (-criticalS d) * m ^ (-criticalS d) :=
    Real.mul_rpow (by norm_num) hmpos.le
  have h2s : (2:ℝ) ^ (-criticalS d) = ((2 : ℝ) ^ criticalS d)⁻¹ := Real.rpow_neg (by norm_num) _
  have h2pos : 0 < (2 : ℝ) ^ criticalS d := by positivity
  have hq1 : c0 * (((2 : ℝ) ^ criticalS d)⁻¹ * (L / (2 * K))) ≤ q (z - p) := by
    refine le_trans ?_ hlow
    refine mul_le_mul_of_nonneg_left ?_ hc0.le
    calc ((2 : ℝ) ^ criticalS d)⁻¹ * (L / (2 * K)) ≤ ((2 : ℝ) ^ criticalS d)⁻¹ * m ^ (-criticalS d) :=
          mul_le_mul_of_nonneg_left hm3.le (inv_nonneg.2 h2pos.le)
      _ = (2 * m) ^ (-criticalS d) := by rw [hsplit, h2s]
      _ ≤ _ := hpow
  have : 2 * K * (2 : ℝ) ^ criticalS d / c0 * q (z - p) ≥ L := by
    have e : 2 * K * (2 : ℝ) ^ criticalS d / c0 * (c0 * (((2 : ℝ) ^ criticalS d)⁻¹ * (L / (2 * K)))) = L := by
      field_simp
    calc L = 2 * K * (2 : ℝ) ^ criticalS d / c0 * (c0 * (((2 : ℝ) ^ criticalS d)⁻¹ * (L / (2 * K)))) := e.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hq1 (by positivity)
  linarith

end HRS.MS.S82R

end
