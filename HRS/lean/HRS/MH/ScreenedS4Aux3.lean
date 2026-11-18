import HRS.MH.ScreenedS4Aux2

/-!
# Packet S4, part 3: the symbol `m_i(ξ) = c·2πi ξ_i ‖ξ‖^{s-d}`
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform ContDiff

namespace HRS.MH.Screened

open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

/-- The symbol `m_i(ξ) = c · 2π ξ_i ‖ξ‖^{s-d} · I`. -/
def s4m (c s : ℝ) (i : Fin d) (ξ : Euc d) : ℂ :=
  ((c * (2 * Real.pi * ξ i) * ‖ξ‖ ^ (s - d) : ℝ) : ℂ) * Complex.I

lemma measurable_s4m (c s : ℝ) (i : Fin d) : Measurable (s4m c s i) := by
  unfold s4m
  refine Measurable.mul ?_ measurable_const
  exact Complex.measurable_ofReal.comp
    ((measurable_const.mul (measurable_const.mul (measurable_pi_apply i |>.comp
      (by fun_prop : Measurable fun ξ : Euc d => ξ.ofLp)))).mul (measurable_norm.pow_const _))

lemma conj_s4m (c s : ℝ) (i : Fin d) (ξ : Euc d) : conj (s4m c s i ξ) = -s4m c s i ξ := by
  unfold s4m
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- `‖m_i(ξ)‖ ≤ 2π c ‖ξ‖^{s+1-d}`. -/
lemma norm_s4m_le {c : ℝ} (hc : 0 < c) (s : ℝ) (i : Fin d) (ξ : Euc d) :
    ‖s4m c s i ξ‖ ≤ 2 * Real.pi * c * ‖ξ‖ ^ (s + 1 - d) := by
  unfold s4m
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hi : |ξ i| ≤ ‖ξ‖ := by simpa using PiLp.norm_apply_le ξ i
  have h3 : 0 ≤ ‖ξ‖ ^ (s - d) := Real.rpow_nonneg (norm_nonneg ξ) _
  have h4 : |c * (2 * Real.pi * ξ i) * ‖ξ‖ ^ (s - d)| =
      c * (2 * Real.pi * |ξ i|) * ‖ξ‖ ^ (s - d) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hc, abs_of_pos (by positivity : 0 < 2 * Real.pi),
      abs_of_nonneg h3]
  rw [h4]
  by_cases hξ : ξ = 0
  · subst hξ
    have h0 : |(0 : Euc d) i| = 0 := by simp
    rw [h0]
    simp only [norm_zero, mul_zero, zero_mul]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg le_rfl _)
  · have h5 : ‖ξ‖ ^ (s + 1 - d) = ‖ξ‖ ^ (s - d) * ‖ξ‖ := by
      rw [← Real.rpow_add_one (norm_ne_zero_iff.2 hξ)]; congr 1; ring
    rw [h5]
    calc c * (2 * Real.pi * |ξ i|) * ‖ξ‖ ^ (s - d)
        ≤ c * (2 * Real.pi * ‖ξ‖) * ‖ξ‖ ^ (s - d) := by gcongr
      _ = _ := by ring

/-- `‖m_i(ξ)‖² ≤ K² (1+4π²‖ξ‖²)^σ`, `σ = s+1-d ≥ 0`. -/
lemma norm_s4m_sq_le {c : ℝ} (hc : 0 < c) {s : ℝ} (hσ : 0 ≤ s + 1 - d) (i : Fin d) (ξ : Euc d) :
    ‖s4m c s i ξ‖ ^ 2 ≤ (2 * Real.pi * c) ^ 2 * (4 * Real.pi ^ 2) ^ (-(s + 1 - d)) *
      (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (s + 1 - d) := by
  set σ := s + 1 - d with hσdef
  have h1 := norm_s4m_le hc s i ξ
  have h2 : ‖s4m c s i ξ‖ ^ 2 ≤ (2 * Real.pi * c) ^ 2 * (‖ξ‖ ^ σ) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : (‖ξ‖ ^ σ) ^ 2 ≤ (4 * Real.pi ^ 2) ^ (-σ) * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ σ := by
    have hp : 0 < 4 * Real.pi ^ 2 := by positivity
    have e1 : (‖ξ‖ ^ σ) ^ 2 = (‖ξ‖ ^ 2) ^ σ := by
      rw [← Real.rpow_natCast (‖ξ‖ ^ σ) 2, ← Real.rpow_mul (norm_nonneg ξ),
        ← Real.rpow_natCast ‖ξ‖ 2, ← Real.rpow_mul (norm_nonneg ξ), mul_comm]
    have e2 : ‖ξ‖ ^ 2 ≤ (4 * Real.pi ^ 2)⁻¹ * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) := by
      rw [← div_eq_inv_mul, le_div_iff₀ hp]; nlinarith [sq_nonneg ‖ξ‖]
    calc (‖ξ‖ ^ σ) ^ 2 = (‖ξ‖ ^ 2) ^ σ := e1
      _ ≤ ((4 * Real.pi ^ 2)⁻¹ * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2)) ^ σ :=
          Real.rpow_le_rpow (by positivity) e2 hσ
      _ = (4 * Real.pi ^ 2) ^ (-σ) * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ σ := by
          rw [Real.mul_rpow (by positivity) (by positivity), Real.rpow_neg hp.le,
            Real.inv_rpow hp.le]
  calc ‖s4m c s i ξ‖ ^ 2 ≤ (2 * Real.pi * c) ^ 2 * (‖ξ‖ ^ σ) ^ 2 := h2
    _ ≤ (2 * Real.pi * c) ^ 2 * ((4 * Real.pi ^ 2) ^ (-σ) *
          (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ σ) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

end HRS.MH.Screened
