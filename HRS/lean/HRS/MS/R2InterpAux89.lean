import HRS.MS.R2InterpAux88

/-!
# S10.2 (worker S10R), part 89 (packet M3b): the centred empirical path `u ↦ ζ_N^u` is a genuine continuous path in `B_m`
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d : ℕ}

theorem s102_zeta_cont {m : ℝ} (hm : (d : ℝ) < m) {N : ℕ} (hN : 0 < N) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → EucConfig d N) (hXm : ∀ t, Measurable (X t))
    (hcont : ∀ᵐ ζ ∂P, ∀ i, Continuous fun t => X t ζ i) :
    ∀ᵐ ζ ∂P, Continuous fun u : ℝ => zetaB m (P.map (X u.toNNReal)) (X u.toNNReal ζ) := by
  obtain ⟨Ch, hCh⟩ := hermiteFunD_uniform_bound (d := d)
  have hCh0 : 0 ≤ Ch := (abs_nonneg _).trans (hCh 0 0)
  filter_upwards [hcont] with ζ hζ
  -- the mean coefficients
  have hformM : ∀ (α : MultiIndex d) (u : ℝ),
      HRS.Whole.measureHermiteCoeff (HRS.Whole.meanEmpirical (P.map (X u.toNNReal))) α =
        (N : ℝ)⁻¹ * ∑ i, ∫ ζ', hermiteFunD α (X u.toNNReal ζ' i) ∂P := by
    intro α u
    have : IsProbabilityMeasure (P.map (X u.toNNReal)) := ⟨by
      rw [Measure.map_apply (hXm _) MeasurableSet.univ]; simp⟩
    have h := HRS.MS.S21.s21_integral_meanEmpirical (P.map (X u.toNNReal)) (f := hermiteFunD α)
      (contDiff_hermiteFunD α).continuous.measurable (B := Ch) (fun x => hCh α x)
    refine h.trans ?_
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact integral_map (hXm _).aemeasurable ((contDiff_hermiteFunD α).continuous.measurable.comp
      (measurable_pi_apply i)).aestronglyMeasurable
  have hmean : ∀ α : MultiIndex d, Continuous fun u : ℝ =>
      HRS.Whole.measureHermiteCoeff (HRS.Whole.meanEmpirical (P.map (X u.toNNReal))) α := by
    intro α
    have hform := hformM α
    simp_rw [hform]
    refine continuous_const.mul (continuous_finsetSum _ fun i _ => ?_)
    refine continuous_of_dominated (bound := fun _ => Ch) (fun u => ?_) (fun u => Eventually.of_forall fun ζ' => ?_)
      (integrable_const _) ?_
    · exact ((contDiff_hermiteFunD α).continuous.measurable.comp
        ((measurable_pi_apply i).comp (hXm _))).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact hCh α _
    · filter_upwards [hcont] with ζ' hζ'
      exact (contDiff_hermiteFunD α).continuous.comp ((hζ' i).comp continuous_real_toNNReal)
  have hemp : ∀ α : MultiIndex d, Continuous fun u : ℝ =>
      HRS.Whole.measureHermiteCoeff (HRS.Whole.empirical (X u.toNNReal ζ)) α := by
    intro α
    have hform : ∀ u : ℝ, HRS.Whole.measureHermiteCoeff (HRS.Whole.empirical (X u.toNNReal ζ)) α =
        (N : ℝ)⁻¹ * ∑ i, hermiteFunD α (X u.toNNReal ζ i) := fun u =>
      HRS.Whole.pair_empirical hN _ (hermiteFunD α)
    simp_rw [hform]
    exact continuous_const.mul (continuous_finsetSum _ fun i _ =>
      (contDiff_hermiteFunD α).continuous.comp ((hζ i).comp continuous_real_toNNReal))
  have hbd : ∀ (u : ℝ) α, |HRS.Whole.measureHermiteCoeff (HRS.Whole.empirical (X u.toNNReal ζ)) α -
      HRS.Whole.measureHermiteCoeff (HRS.Whole.meanEmpirical (P.map (X u.toNNReal))) α| ≤ 2 * Ch := by
    intro u α
    have h1 : |HRS.Whole.measureHermiteCoeff (HRS.Whole.empirical (X u.toNNReal ζ)) α| ≤ Ch := by
      rw [show HRS.Whole.measureHermiteCoeff (HRS.Whole.empirical (X u.toNNReal ζ)) α =
        (N : ℝ)⁻¹ * ∑ i, hermiteFunD α (X u.toNNReal ζ i) from HRS.Whole.pair_empirical hN _ (hermiteFunD α),
        abs_mul, abs_of_nonneg (by positivity)]
      have hs : |∑ i, hermiteFunD α (X u.toNNReal ζ i)| ≤ N * Ch := by
        calc |∑ i, hermiteFunD α (X u.toNNReal ζ i)| ≤ ∑ i, |hermiteFunD α (X u.toNNReal ζ i)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin N, Ch := Finset.sum_le_sum fun i _ => hCh α _
          _ = N * Ch := by simp
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      calc (N : ℝ)⁻¹ * |∑ i, hermiteFunD α (X u.toNNReal ζ i)| ≤ (N : ℝ)⁻¹ * (N * Ch) :=
            mul_le_mul_of_nonneg_left hs (by positivity)
        _ = Ch := by field_simp
    have h2 : |HRS.Whole.measureHermiteCoeff (HRS.Whole.meanEmpirical (P.map (X u.toNNReal))) α| ≤ Ch := by
      rw [hformM α u, abs_mul, abs_of_nonneg (by positivity)]
      have hs : |∑ i, ∫ ζ', hermiteFunD α (X u.toNNReal ζ' i) ∂P| ≤ N * Ch := by
        calc |∑ i, ∫ ζ', hermiteFunD α (X u.toNNReal ζ' i) ∂P|
            ≤ ∑ i, |∫ ζ', hermiteFunD α (X u.toNNReal ζ' i) ∂P| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin N, Ch := Finset.sum_le_sum fun i _ => by
              have := norm_integral_le_of_norm_le_const (μ := P)
                (f := fun ζ' => hermiteFunD α (X u.toNNReal ζ' i)) (C := Ch)
                (Eventually.of_forall fun ζ' => by rw [Real.norm_eq_abs]; exact hCh α _)
              simpa [Real.norm_eq_abs] using this
          _ = N * Ch := by simp
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      calc (N : ℝ)⁻¹ * |∑ i, ∫ ζ', hermiteFunD α (X u.toNNReal ζ' i) ∂P| ≤ (N : ℝ)⁻¹ * (N * Ch) :=
            mul_le_mul_of_nonneg_left hs (by positivity)
        _ = Ch := by field_simp
    calc _ ≤ |HRS.Whole.measureHermiteCoeff (HRS.Whole.empirical (X u.toNNReal ζ)) α| +
          |HRS.Whole.measureHermiteCoeff (HRS.Whole.meanEmpirical (P.map (X u.toNNReal))) α| := abs_sub _ _
      _ ≤ 2 * Ch := by linarith
  have := s102_ofSeq_continuousOn (m := m) (S := Set.univ) hm (fun u α =>
    HRS.Whole.measureHermiteCoeff (HRS.Whole.empirical (X u.toNNReal ζ)) α -
      HRS.Whole.measureHermiteCoeff (HRS.Whole.meanEmpirical (P.map (X u.toNNReal))) α) (C0 := 2 * Ch)
    (fun u _ α => hbd u α) (fun α => ((hemp α).sub (hmean α)).continuousOn)
  have h2 : Continuous fun u : ℝ => (OscDual.ofSeq m fun α => HRS.Whole.measureHermiteCoeff
      (HRS.Whole.empirical (X u.toNNReal ζ)) α - HRS.Whole.measureHermiteCoeff
      (HRS.Whole.meanEmpirical (P.map (X u.toNNReal))) α : OscDual d m) := continuousOn_univ.1 this
  exact h2.const_smul (Real.sqrt N)

end HRS.MS.R2Interp

end
