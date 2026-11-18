import HRS.Main.ThermAux5

/-!
# THERM helper 6: the per-mode second moment of `η_N` under an exchangeable law
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d N : ℕ}

/-- `μ_N(f) = N⁻¹ ∑ f(x_i)` (the statistic of `linearStat_variance`). -/
def therm_stat (f : Torus d → ℝ) (X : Config d N) : ℝ := (1 / (N : ℝ)) * ∑ i, f (X i)

theorem therm_measurable_stat {f : Torus d → ℝ} (hf : Measurable f) :
    Measurable (therm_stat (N := N) f) := by
  unfold therm_stat
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ => hf.comp (measurable_pi_apply i))

theorem therm_abs_stat_le {f : Torus d → ℝ} {B : ℝ} (hB : ∀ x, |f x| ≤ B) (hN : 1 ≤ N)
    (X : Config d N) : |therm_stat f X| ≤ B := by
  unfold therm_stat
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / N)]
  calc 1 / (N : ℝ) * |∑ i, f (X i)| ≤ 1 / (N : ℝ) * ∑ i, |f (X i)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ 1 / (N : ℝ) * ∑ _i : Fin N, B :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hB _) (by positivity)
    _ = B := by simp; field_simp

/-- The mean of `μ_N(f)` under an exchangeable probability law is `∫ f d(first marginal)`. -/
theorem therm_integral_stat (Q : Measure (Config d N)) [IsProbabilityMeasure Q]
    (hQ : IsExchangeable Q) (hN : 1 ≤ N) {f : Torus d → ℝ} (hf : Continuous f) :
    ∫ X, therm_stat f X ∂Q = ∫ x, f x ∂(firstMarginal Q) := by
  rw [← meanEmpirical_eq_firstMarginal Q hQ hN, integral_meanEmpirical Q hf]
  unfold therm_stat
  rw [integral_const_mul, integral_finsetSum]
  · simp [one_div]
  · intro i _
    exact (hf.comp (continuous_apply i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem therm_mode_bound (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (Q : Measure (Config d N)) [IsProbabilityMeasure Q] (hQ : IsExchangeable Q) (hN : 1 ≤ N)
    (k : NonzeroLattice d) :
    ∫⁻ X, ENNReal.ofReal (therm_eta μ k X ^ 2) ∂Q ≤
      2 * ((N : ℝ≥0∞) * evariance (therm_stat (Torus.realMode k)) Q) +
        2 * ENNReal.ofReal ((N : ℝ) * (∫ x, Torus.realMode k x ∂(firstMarginal Q) -
          Torus.measureRealCoeff μ k) ^ 2) := by
  set f : Torus d → ℝ := Torus.realMode k with hf
  have hfc : Continuous f := continuous_realMode' k
  have hfm : Measurable f := hfc.measurable
  set S : Config d N → ℝ := therm_stat f with hS
  have hSm : Measurable S := therm_measurable_stat hfm
  set c0 : ℝ := Torus.measureRealCoeff μ k with hc0
  set m₀ : ℝ := ∫ x, f x ∂(firstMarginal Q) with hm₀
  have hmean : ∫ X, S X ∂Q = m₀ := therm_integral_stat Q hQ hN hfc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have heta : ∀ X, therm_eta μ k X = Real.sqrt N * (S X - c0) := fun X => by
    simp [therm_eta, hS, therm_stat, one_div, hf, hc0]
  have hpt : ∀ X, ENNReal.ofReal (therm_eta μ k X ^ 2) ≤
      ENNReal.ofReal (2 * N) * ENNReal.ofReal ((S X - ∫ X, S X ∂Q) ^ 2) +
        2 * ENNReal.ofReal ((N : ℝ) * (m₀ - c0) ^ 2) := fun X => by
    rw [heta, mul_pow, Real.sq_sqrt hN0.le, hmean]
    have h1 : (N : ℝ) * (S X - c0) ^ 2 ≤ 2 * N * (S X - m₀) ^ 2 + 2 * (N * (m₀ - c0) ^ 2) := by
      nlinarith [sq_nonneg (S X - m₀ - (m₀ - c0)), hN0]
    calc ENNReal.ofReal ((N : ℝ) * (S X - c0) ^ 2)
        ≤ ENNReal.ofReal (2 * N * (S X - m₀) ^ 2 + 2 * (N * (m₀ - c0) ^ 2)) :=
          ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal (2 * N) * ENNReal.ofReal ((S X - m₀) ^ 2) +
          2 * ENNReal.ofReal ((N : ℝ) * (m₀ - c0) ^ 2) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by norm_num)]
          simp
  calc ∫⁻ X, ENNReal.ofReal (therm_eta μ k X ^ 2) ∂Q
      ≤ ∫⁻ X, (ENNReal.ofReal (2 * N) * ENNReal.ofReal ((S X - ∫ X, S X ∂Q) ^ 2) +
          2 * ENNReal.ofReal ((N : ℝ) * (m₀ - c0) ^ 2)) ∂Q := lintegral_mono hpt
    _ = ENNReal.ofReal (2 * N) * evariance S Q + 2 * ENNReal.ofReal ((N : ℝ) * (m₀ - c0) ^ 2) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, evariance_eq_lintegral_ofReal]
    _ = _ := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast, mul_assoc]
        simp

end Main

end HRS
