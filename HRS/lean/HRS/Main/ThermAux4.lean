import HRS.Main.ThermAux3

/-!
# THERM helper 4: rate tendsto, `ofFun` scaling
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

/-- `ofFun` is homogeneous in the scalar. -/
theorem therm_ofFun_smul (m a : ℝ) (b ρ : Torus d → ℝ) :
    NegSobolev.ofFun m (fun x => a * b x * ρ x) = a • NegSobolev.ofFun m (fun x => b x * ρ x) := by
  unfold NegSobolev.ofFun
  rw [← therm_ofSeq_smul]
  congr 1
  funext k
  unfold Torus.funRealCoeff
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

/-- `log(e N)/√N → 0`. -/
theorem therm_lograte_tendsto :
    Tendsto (fun N : ℕ => Real.log (Real.exp 1 * N) / Real.sqrt N) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => Real.log N / (N : ℝ) ^ (1 / 2 : ℝ)) atTop (𝓝 0) :=
    ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun N : ℕ => 1 / Real.sqrt N) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
    simpa [Function.comp_def] using this
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  rw [Real.log_mul (Real.exp_pos 1).ne' hN0.ne', Real.log_exp, Real.sqrt_eq_rpow]
  ring

theorem therm_iidRateW_tendsto {m : ℝ} (hm : (d : ℝ) / 2 < m) :
    Tendsto (fun N : ℕ => iidRateW d m N) atTop (𝓝 0) := by
  have hp : 0 < (m - (d : ℝ) / 2) / (m + (d : ℝ) / 2) := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    apply div_pos <;> linarith
  have := (therm_lograte_tendsto).rpow_const (p := (m - (d : ℝ) / 2) / (m + (d : ℝ) / 2))
    (Or.inr hp.le)
  rw [Real.zero_rpow hp.ne'] at this
  exact this

end Main

end HRS
