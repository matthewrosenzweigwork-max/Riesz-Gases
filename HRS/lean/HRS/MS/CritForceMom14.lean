import HRS.MS.CritForceMom13

/-!
# S8.2 NormalForm packet R03: weighted radial rows

Pro packet `S82.R03` (`weighted_radial_rows`, `S8.2-Moments.lean`), with `smallRadius`, `pole`, `logN`,
`ShortRangePole`, `criticalS d = d/2` replaced by their `s82n_` versions.  The five integrals are
(1) gradient-square row, (2) gradient-times-pole row, (3) squared pole with the repulsive cutoff
(cost `log(eN)`), (4) fourth pole (cost `N²`), (5) squared pole with squared logarithm (cost `log(eN)^3`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.MS.S82N

open HRS HRS.Whole

variable {d : ℕ}

theorem s82n_weighted_radial_rows (hd : 2 ≤ d) (β M G c : ℝ) (hβ : 0 < β) (hM : 0 ≤ M)
    (hG : 0 < G) (hc : 0 < c) (q : Euc d → ℝ) (hq : S82nShortRangePole d q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ →
      HRS.Whole.HasR2GaussianUpper G c ρ → ∀ N : ℕ, 2 ≤ N → ∀ x : Euc d,
      (∫⁻ y, ENNReal.ofReal (jbracket y ^ M *
        (1 + s82n_smallRadius x y ^ (1 - s82n_critS d)) ^ 2) ∂(HRS.Whole.withDensityReal ρ)) ≤
        ENNReal.ofReal (C * jbracket x ^ M) ∧
      (∫⁻ y, ENNReal.ofReal (jbracket y ^ M *
        (1 + s82n_smallRadius x y ^ (1 - s82n_critS d)) * s82n_pole x y)
          ∂(HRS.Whole.withDensityReal ρ)) ≤ ENNReal.ofReal (C * jbracket x ^ M) ∧
      (∫⁻ y, ENNReal.ofReal (jbracket y ^ M * s82n_pole x y ^ 2 *
        Real.exp (-(β / N) * q (x - y))) ∂(HRS.Whole.withDensityReal ρ)) ≤
        ENNReal.ofReal (C * jbracket x ^ M * s82n_logN N) ∧
      (∫⁻ y, ENNReal.ofReal (jbracket y ^ M * s82n_pole x y ^ 4 *
        Real.exp (-(β / N) * q (x - y))) ∂(HRS.Whole.withDensityReal ρ)) ≤
        ENNReal.ofReal (C * jbracket x ^ M * (N : ℝ) ^ 2) ∧
      (∫⁻ y, ENNReal.ofReal (jbracket y ^ M * s82n_pole x y ^ 2 *
        (s82n_logN N + 1 + |Real.log (s82n_smallRadius x y)|) ^ 2 *
        Real.exp (-(β / N) * q (x - y))) ∂(HRS.Whole.withDensityReal ρ)) ≤
        ENNReal.ofReal (C * jbracket x ^ M * s82n_logN N ^ 3) := by
  obtain ⟨r0, c0, C0, hr0, hr1, hc0, hnear⟩ := hq.near
  have hs := s82n_critS_pos (by omega : 1 ≤ d)
  set κ : ℝ := (d : ℝ) * (volume : Measure (Euc d)).real (Metric.ball (0 : Euc d) 1) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set Mom := s82n_Mom d M G c with hMom
  have hMom0 : 0 ≤ Mom := s82n_Mom_nonneg (by omega) M G c hM hG.le hc
  obtain ⟨C3, hC30, h3⟩ := s82n_E3 hd β M G c hβ hM hG.le hc q hq
  obtain ⟨C4, hC40, h4⟩ := s82n_E4 hd β M G c hβ hM hG.le hc q hq
  obtain ⟨C5, hC50, h5⟩ := s82n_E5 hd β M G c hβ hM hG.le hc q hq
  set C1 : ℝ := 4 ^ M * G * (κ * (4 * r0)) + (1 + r0 ^ (1 - s82n_critS d)) ^ 2 * Mom with hC1
  set C2 : ℝ := 4 ^ M * G * (κ * (4 * r0)) +
    ((1 + r0 ^ (1 - s82n_critS d)) * (1 + r0 ^ (-s82n_critS d))) * Mom with hC2
  have hC10 : 0 ≤ C1 := by positivity
  have hC20 : 0 ≤ C2 := by
    have h1 : 0 ≤ r0 ^ (1 - s82n_critS d) := Real.rpow_nonneg hr0.le _
    have h2 : 0 ≤ r0 ^ (-s82n_critS d) := Real.rpow_nonneg hr0.le _
    positivity
  refine ⟨C1 + C2 + C3 + C4 + C5, by positivity, ?_⟩
  intro ρ hρ hρG N hN x
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hJ : 0 ≤ jbracket x ^ M := Real.rpow_nonneg (s82n_jb_pos x).le _
  have hL : 0 ≤ s82n_logN N := by rw [s82n_logN_eq N hN1]; have := Real.log_nonneg hNr; linarith
  have hN2 : 0 ≤ (N : ℝ) ^ 2 := by positivity
  have hL3 : 0 ≤ s82n_logN N ^ 3 := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine (s82n_E1 hd M G c r0 hM hG.le hc hr0 hr1 ρ hρ hρG x).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have : jbracket x ^ M * (4 ^ M * G * (κ * (4 * r0)) +
        (1 + r0 ^ (1 - s82n_critS d)) ^ 2 * Mom) = C1 * jbracket x ^ M := by rw [hC1]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) hJ
  · have h := s82n_E2 hd M G c r0 hM hG.le hc hr0 hr1 ρ hρ hρG x
    refine le_trans (le_of_eq ?_) (h.trans ?_)
    · refine lintegral_congr fun y => ?_
      congr 1; ring
    · refine ENNReal.ofReal_le_ofReal ?_
      have : jbracket x ^ M * (4 ^ M * G * (κ * (4 * r0)) +
          ((1 + r0 ^ (1 - s82n_critS d)) * (1 + r0 ^ (-s82n_critS d))) * Mom) = C2 * jbracket x ^ M := by
        rw [hC2]; ring
      rw [this]
      exact mul_le_mul_of_nonneg_right (by linarith) hJ
  · refine (h3 ρ hρ hρG N hN x).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hJ) hL
  · refine (h4 ρ hρ hρG N hN x).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hJ) hN2
  · refine (h5 ρ hρ hρG N hN x).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hJ) hL3

end HRS.MS.S82N
