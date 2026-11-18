import HRS.MC.CepN1Aux6

/-!
# Packet CEPN1, part 7: choice of the mesh
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal Real

noncomputable section

namespace HRS.MC.CepN1

/-- For `h > 0` and `ε = κ h`, the one-piece bound factorises as `√h * φ(h)`. -/
theorem cepn1_q_factor {h : ℝ≥0} (hh : 0 < h) {L κ ρ : ℝ} (hρ : 0 < ρ) :
    cepn1_q h L (κ * h) ρ = Real.sqrt h *
      (2 * κ / Real.sqrt (2 * π) * Real.exp (-(L + κ) ^ 2 * h / 2) - Real.sqrt h / ρ ^ 2) := by
  have hpos : (0 : ℝ) < h := by exact_mod_cast hh
  have hs : 0 < Real.sqrt h := Real.sqrt_pos.2 hpos
  have hs2 : Real.sqrt h * Real.sqrt h = h := Real.mul_self_sqrt hpos.le
  have hp : 0 < Real.sqrt (2 * π) := Real.sqrt_pos.2 (by positivity)
  unfold cepn1_q
  have e1 : Real.sqrt (2 * π * h) = Real.sqrt (2 * π) * Real.sqrt h := Real.sqrt_mul (by positivity) _
  have e2 : -(L * h + κ * h) ^ 2 / (2 * h) = -(L + κ) ^ 2 * h / 2 := by
    field_simp
  rw [e1, e2]
  have e3 : (h : ℝ) / ρ ^ 2 = Real.sqrt h * (Real.sqrt h / ρ ^ 2) := by
    rw [← mul_div_assoc, hs2]
  rw [e3]
  have e4 : 2 * (κ * h) * ((Real.sqrt (2 * π) * Real.sqrt h)⁻¹ * Real.exp (-(L + κ) ^ 2 * h / 2)) =
      Real.sqrt h * (2 * κ / Real.sqrt (2 * π) * Real.exp (-(L + κ) ^ 2 * h / 2)) := by
    generalize Real.sqrt h = s at hs hs2 ⊢
    rw [← hs2]
    field_simp
  rw [e4, mul_sub]


theorem cepn1_param {T' η L : ℝ} (hT' : 0 < T') (hη : 0 < η) (hL : 0 ≤ L) :
    ∃ M : ℕ, 0 < M ∧ ∃ h : ℝ≥0, (h : ℝ) = T' / M ∧ 0 < h ∧ L * h ≤ η / 8 ∧
      0 < cepn1_q h L (η / (8 * M)) (η / 8) := by
  set κ : ℝ := η / (8 * T') with hκ
  have hκpos : 0 < κ := by positivity
  set φ : ℝ → ℝ := fun x => 2 * κ / Real.sqrt (2 * π) * Real.exp (-(L + κ) ^ 2 * x / 2) -
    Real.sqrt x / (η / 8) ^ 2 with hφ
  have hφc : Continuous φ := by
    simp only [hφ]
    fun_prop
  have hφ0 : 0 < φ 0 := by
    simp only [hφ, mul_zero, zero_div, Real.exp_zero, mul_one, Real.sqrt_zero, sub_zero]
    positivity
  have h1 : ∀ᶠ x in 𝓝 (0 : ℝ), 0 < φ x := hφc.continuousAt.eventually (lt_mem_nhds hφ0)
  have hlim : Tendsto (fun M : ℕ => T' / (M : ℝ)) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat T'
  have h2 := hlim.eventually h1
  have hlim2 : Tendsto (fun M : ℕ => L * (T' / (M : ℝ))) atTop (𝓝 0) := by
    simpa using hlim.const_mul L
  have h3 : ∀ᶠ M : ℕ in atTop, L * (T' / (M : ℝ)) < η / 8 := hlim2.eventually_lt_const (by positivity)
  obtain ⟨M, hM1, hM2, hM3⟩ := (h2.and (h3.and (eventually_gt_atTop 0))).exists
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM3
  have hTM : 0 ≤ T' / (M : ℝ) := by positivity
  set h : ℝ≥0 := Real.toNNReal (T' / M) with hh
  have hhc : (h : ℝ) = T' / M := Real.coe_toNNReal _ hTM
  have hhpos : 0 < h := by
    have : (0 : ℝ) < h := by rw [hhc]; positivity
    exact_mod_cast this
  refine ⟨M, hM3, h, hhc, hhpos, by rw [hhc]; exact hM2.le, ?_⟩
  have hε : η / (8 * M) = κ * h := by
    rw [hhc, hκ]; field_simp
  rw [hε, cepn1_q_factor hhpos (by positivity : (0:ℝ) < η / 8)]
  have : φ (T' / M) = 2 * κ / Real.sqrt (2 * π) * Real.exp (-(L + κ) ^ 2 * h / 2) -
      Real.sqrt h / (η / 8) ^ 2 := by
    simp only [hφ, hhc]
  rw [← this]
  exact mul_pos (Real.sqrt_pos.2 (by exact_mod_cast hhpos)) hM1

end HRS.MC.CepN1
