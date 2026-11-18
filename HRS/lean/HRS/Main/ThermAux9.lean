import HRS.Main.ThermAux8

/-!
# THERM helper 9: the independent preparation (`β₀ = 0`)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

theorem therm_evariance_iid_le (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {N : ℕ}
    (hN : 1 ≤ N) (k : NonzeroLattice d) :
    (N : ℝ≥0∞) * evariance (therm_stat (Torus.realMode k)) (Measure.pi fun _ : Fin N => μ) ≤
      ENNReal.ofReal 2 := by
  set f : Torus d → ℝ := Torus.realMode k with hf
  have hfc : Continuous f := continuous_realMode' k
  have hfm : Measurable f := hfc.measurable
  set P : Measure (Config d N) := Measure.pi fun _ : Fin N => μ with hP
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set X : Fin N → Config d N → ℝ := fun i ω => f (ω i) with hX
  have hXm : ∀ i, Measurable (X i) := fun i => hfm.comp (measurable_pi_apply i)
  have hXL : ∀ i, MemLp (X i) 2 P := fun i =>
    MemLp.of_bound (hXm i).aestronglyMeasurable (Real.sqrt 2) (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact Torus.abs_realMode_le k (ω i))
  have hindep : iIndepFun X P := iIndepFun_pi (μ := fun _ : Fin N => μ) (X := fun _ => f)
    (fun _ => hfm.aemeasurable)
  have hvs : variance (∑ i, X i) P = ∑ i, variance (X i) P :=
    IndepFun.variance_sum (s := Finset.univ) (fun i _ => hXL i)
      (fun i _ j _ hij => hindep.indepFun hij)
  have hvi : ∀ i, variance (X i) P ≤ 2 := fun i => by
    refine (variance_le_expectation_sq (hXm i).aestronglyMeasurable).trans ?_
    have h := norm_integral_le_of_norm_le_const (μ := P) (f := (X i) ^ 2) (C := 2)
      (Eventually.of_forall fun ω => by
        simp only [Pi.pow_apply, Real.norm_eq_abs, abs_pow]
        have := Torus.abs_realMode_le k (ω i)
        calc |f (ω i)| ^ 2 ≤ (Real.sqrt 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
          _ = 2 := Real.sq_sqrt (by norm_num))
    simp only [measure_univ, ENNReal.toReal_one, mul_one, Measure.real] at h
    exact (le_abs_self _).trans (by simpa using h)
  have hstat : therm_stat (N := N) f = fun ω => (1 / (N : ℝ)) * (∑ i, X i) ω := by
    funext ω; simp [therm_stat, hX, Finset.sum_apply]
  have hvar : variance (therm_stat (N := N) f) P ≤ 2 / N := by
    rw [hstat, variance_const_mul, hvs]
    calc (1 / (N : ℝ)) ^ 2 * ∑ i, variance (X i) P ≤ (1 / (N : ℝ)) ^ 2 * ∑ _i : Fin N, (2 : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hvi i) (by positivity)
      _ = 2 / N := by simp; field_simp
  have hSL : MemLp (therm_stat (N := N) f) 2 P :=
    MemLp.of_bound (therm_measurable_stat hfm).aestronglyMeasurable (Real.sqrt 2)
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact therm_abs_stat_le (fun x => Torus.abs_realMode_le k x) hN ω)
  rw [← hSL.ofReal_variance_eq, ← ENNReal.ofReal_natCast N, ← ENNReal.ofReal_mul hN0.le]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (N : ℝ) * variance (therm_stat (N := N) f) P ≤ (N : ℝ) * (2 / N) :=
        mul_le_mul_of_nonneg_left hvar hN0.le
    _ = 2 := by field_simp

/-- `β₀ = 0`: the second moment of every Fourier mode of `η_N^0` is at most `4`. -/
theorem therm_mode_bound_iid (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {N : ℕ}
    (hN : 1 ≤ N) (k : NonzeroLattice d) :
    ∫⁻ X, ENNReal.ofReal (therm_eta μ k X ^ 2) ∂(Measure.pi fun _ : Fin N => μ) ≤
      ENNReal.ofReal 4 := by
  set P : Measure (Config d N) := Measure.pi fun _ : Fin N => μ with hP
  have hex : IsExchangeable P := by
    have := modulatedGibbs_isExchangeable (N := N) (periodicRiesz d 0) 0 μ
      (fun x => periodicRiesz_neg x)
    rwa [modulatedGibbs_zero] at this
  refine (therm_mode_bound μ P hex hN k).trans ?_
  have hfm : firstMarginal P = μ := by
    unfold firstMarginal
    rw [dif_pos (by omega)]
    have := Measure.pi_map_eval (fun _ : Fin N => μ) ⟨0, by omega⟩
    simpa using this
  rw [hfm]
  have h0 : Torus.measureRealCoeff μ k = ∫ x, Torus.realMode k x ∂μ := rfl
  rw [h0, sub_self]
  have := therm_evariance_iid_le μ hN k
  calc 2 * ((N : ℝ≥0∞) * evariance (therm_stat (Torus.realMode k)) P) +
      2 * ENNReal.ofReal ((N : ℝ) * 0 ^ 2) ≤ 2 * ENNReal.ofReal 2 + 2 * ENNReal.ofReal ((N : ℝ) * 0 ^ 2) := by
        gcongr
    _ = ENNReal.ofReal 4 := by
        have : ENNReal.ofReal (4 : ℝ) = 2 * ENNReal.ofReal 2 := by
          rw [show (4 : ℝ) = 2 * 2 by norm_num, ENNReal.ofReal_mul (by norm_num)]; simp
        rw [this]; simp

end Main

end HRS
