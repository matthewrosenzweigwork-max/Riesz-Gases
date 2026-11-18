import HRS.Main.ThermAux7

/-!
# THERM helper 8: uniform second moment of `η_N^0` for the Gibbs preparations (`β₀ > 0`) and the
independent preparation (`β₀ = 0`)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

theorem therm_deltaN_pos {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (N : ℕ) (hN : 1 ≤ N) :
    0 < deltaN d s N := by
  have h := (deltaN_basic (by omega) hs0 hsd N hN).1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  by_contra hneg
  push_neg at hneg
  nlinarith

theorem therm_sqrtN_delta_bdd {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < 2 * (d : ℝ) / 3) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ N : ℕ, Real.sqrt N * deltaN d s N ≤ M := by
  have h := (deltaN_errors_tendsto (by omega) hs0 hs).1
  obtain ⟨M, hM⟩ := h.bddAbove_range
  refine ⟨max M 0, le_max_right _ _, fun N => ?_⟩
  exact (hM ⟨N, rfl⟩).trans (le_max_left _ _)

theorem therm_realMode_sq_integral_le (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (k : NonzeroLattice d) : ∫ x, Torus.realMode k x ^ 2 ∂μ ≤ 2 := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => Torus.realMode k x ^ 2)
    (C := 2) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_pow]
      have := Torus.abs_realMode_le k x
      calc |Torus.realMode k x| ^ 2 ≤ (Real.sqrt 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
        _ = 2 := Real.sq_sqrt (by norm_num))
  simp only [measure_univ, ENNReal.toReal_one, mul_one, Measure.real] at h
  exact (le_abs_self _).trans (by simpa using h)

/-- `β₀ > 0`: a uniform bound for the second moment of every Fourier mode. -/
theorem therm_mode_bound_gibbs_aux {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hs : s < 2 * (d : ℝ) / 3)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) {β₀ : ℝ} (hβ₀ : 0 < β₀) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ, 2 ≤ N → ∀ k : NonzeroLattice d,
      ∫⁻ X, ENNReal.ofReal (therm_eta (withDensityReal ρ) k X ^ 2) ∂(modulatedGibbs (periodicRiesz d s) N β₀ (withDensityReal ρ)) ≤
        ENNReal.ofReal A := by
  haveI hμ0 : IsProbabilityMeasure (withDensityReal ρ) := HRS.isProb_withDensityReal hρ.density
  obtain ⟨C₁, hC₁⟩ := linearStat_variance hd hs0 hsd β₀ hβ₀ ρ hρ
  obtain ⟨C₂, hC₂⟩ := firstMarginal_density_L2 hd hs0 hsd β₀ hβ₀ ρ hρ
  obtain ⟨M, hM0, hM⟩ := therm_sqrtN_delta_bdd hd hs0 hs
  have hρc : Continuous ρ := therm_continuous_of_smooth hρ.smooth
  obtain ⟨xmax, -, hxmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hρc.continuousOn
  set Λ : ℝ := max 1 (ρ xmax) with hΛ
  set C₁' : ℝ := max C₁ 0 with hC₁'
  set C₂' : ℝ := max C₂ 0 with hC₂'
  have hC₁'0 : 0 ≤ C₁' := le_max_right _ _
  have hC₂'0 : 0 ≤ C₂' := le_max_right _ _
  refine ⟨2 * (C₁' * 2) + 2 * (2 * C₂' ^ 2 * M ^ 2), by positivity, fun N hN k => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hQ : IsProbabilityMeasure (modulatedGibbs (periodicRiesz d s) N β₀ (withDensityReal ρ)) :=
    HRS.Q32c.q32c_Q_isProb hd hs0 hsd hβ₀ (le_max_left _ _) hρ.density
      (fun x => (hxmax (Set.mem_univ x)).trans (le_max_right _ _)) (by omega)
  have hex := modulatedGibbs_isExchangeable (N := N) (periodicRiesz d s) β₀ (withDensityReal ρ)
    (fun x => periodicRiesz_neg x)
  refine (therm_mode_bound (withDensityReal ρ) _ hex hN1 k).trans ?_
  have hf : Measurable (Torus.realMode k : Torus d → ℝ) := (continuous_realMode' k).measurable
  have hfL : MemLp (Torus.realMode k : Torus d → ℝ) 2 (withDensityReal ρ) :=
    MemLp.of_bound hf.aestronglyMeasurable (Real.sqrt 2) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact Torus.abs_realMode_le k x)
  have hvar := hC₁ N hN _ hf hfL
  have hvar' : (N : ℝ≥0∞) * evariance (therm_stat (Torus.realMode k))
      (modulatedGibbs (periodicRiesz d s) N β₀ (withDensityReal ρ)) ≤ ENNReal.ofReal (C₁' * 2) := by
    refine hvar.trans (ENNReal.ofReal_le_ofReal ?_)
    have hI := therm_realMode_sq_integral_le (withDensityReal ρ) k
    have hI0 : 0 ≤ ∫ x, Torus.realMode k x ^ 2 ∂(withDensityReal ρ) :=
      integral_nonneg fun x => sq_nonneg _
    calc C₁ * ∫ x, Torus.realMode k x ^ 2 ∂(withDensityReal ρ) ≤ C₁' * ∫ x, Torus.realMode k x ^ 2 ∂(withDensityReal ρ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hI0
      _ ≤ C₁' * 2 := mul_le_mul_of_nonneg_left hI (le_max_right _ _)
  -- the bias
  obtain ⟨hac, hL2⟩ := hC₂ N hN
  haveI := hQ
  have : IsProbabilityMeasure (firstMarginal (modulatedGibbs (periodicRiesz d s) N β₀ (withDensityReal ρ))) := by
    unfold firstMarginal
    rw [dif_pos (by omega)]
    exact inferInstance
  have hδ := therm_deltaN_pos hd hs0 hsd N hN1
  have he : 0 ≤ C₂' * deltaN d s N := mul_nonneg (le_max_right _ _) hδ.le
  have hbias := therm_bias_bound hac hf (B := Real.sqrt 2) (fun x => Torus.abs_realMode_le k x) he
    (hL2.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ.le)))
  have hb2 : (N : ℝ) * (∫ x, Torus.realMode k x ∂(firstMarginal
      (modulatedGibbs (periodicRiesz d s) N β₀ (withDensityReal ρ))) - Torus.measureRealCoeff (withDensityReal ρ) k) ^ 2 ≤
      2 * C₂' ^ 2 * M ^ 2 := by
    have h1 : Torus.measureRealCoeff (withDensityReal ρ) k = ∫ x, Torus.realMode k x ∂(withDensityReal ρ) := rfl
    rw [h1]
    have h2 := sq_le_sq' (abs_le.1 hbias).1 (abs_le.1 hbias).2
    have h3 : (∫ x, Torus.realMode k x ∂(firstMarginal
        (modulatedGibbs (periodicRiesz d s) N β₀ (withDensityReal ρ))) - ∫ x, Torus.realMode k x ∂(withDensityReal ρ)) ^ 2 ≤
        (Real.sqrt 2 * (C₂' * deltaN d s N)) ^ 2 := h2
    have h4 : (N : ℝ) * (Real.sqrt 2 * (C₂' * deltaN d s N)) ^ 2 =
        2 * C₂' ^ 2 * (Real.sqrt N * deltaN d s N) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hN0.le]; ring
    have h5 : (Real.sqrt N * deltaN d s N) ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) hδ.le) (hM N) 2
    calc (N : ℝ) * (_ - _) ^ 2 ≤ (N : ℝ) * (Real.sqrt 2 * (C₂' * deltaN d s N)) ^ 2 :=
          mul_le_mul_of_nonneg_left h3 hN0.le
      _ = 2 * C₂' ^ 2 * (Real.sqrt N * deltaN d s N) ^ 2 := h4
      _ ≤ 2 * C₂' ^ 2 * M ^ 2 := mul_le_mul_of_nonneg_left h5 (by positivity)
  calc 2 * ((N : ℝ≥0∞) * evariance (therm_stat (Torus.realMode k))
        (modulatedGibbs (periodicRiesz d s) N β₀ (withDensityReal ρ))) +
      2 * ENNReal.ofReal ((N : ℝ) * (∫ x, Torus.realMode k x ∂(firstMarginal
        (modulatedGibbs (periodicRiesz d s) N β₀ (withDensityReal ρ))) - Torus.measureRealCoeff (withDensityReal ρ) k) ^ 2)
      ≤ 2 * ENNReal.ofReal (C₁' * 2) + 2 * ENNReal.ofReal (2 * C₂' ^ 2 * M ^ 2) := by
        gcongr
    _ = ENNReal.ofReal (2 * (C₁' * 2) + 2 * (2 * C₂' ^ 2 * M ^ 2)) := by
        have e1 : 0 ≤ 2 * (C₁' * 2) := by positivity
        have e2 : 0 ≤ 2 * (2 * C₂' ^ 2 * M ^ 2) := by positivity
        rw [ENNReal.ofReal_add e1 e2, ENNReal.ofReal_mul (p := 2) (q := C₁' * 2) (by norm_num),
          ENNReal.ofReal_mul (p := 2) (q := 2 * C₂' ^ 2 * M ^ 2) (by norm_num)]
        simp


theorem therm_mode_bound_gibbs (S : PreparedData d) (hs : S.s < 2 * (d : ℝ) / 3) {β₀ : ℝ}
    (hβ₀ : 0 < β₀) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ, 2 ≤ N → ∀ k : NonzeroLattice d,
      ∫⁻ X, ENNReal.ofReal (therm_eta S.μ0 k X ^ 2) ∂(modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0) ≤
        ENNReal.ofReal A :=
  therm_mode_bound_gibbs_aux S.hd S.hs0 S.hsd hs S.ρ0 S.hρ0 hβ₀

end Main

end HRS
