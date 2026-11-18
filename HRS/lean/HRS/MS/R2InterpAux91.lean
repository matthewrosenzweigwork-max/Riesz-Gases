import HRS.MS.R2InterpAux90

/-!
# S10.2 (worker S10R), part 91 (packet M3c): coordinates of the centred empirical field, and the observations of the predicted path

* `s102_coord_zetaB`: `coord(ζ_N^u)_α = ζ_N^u(φ_α)` (the field as a functional on test functions);
* `s102_Z_zf`: the field `ζ_N^u` is an admissible functional on the weighted tests (finite `⟨x⟩^P` moment of the one-particle marginal);
* `s102_obs_Y`: the `i`-th observation of the predicted path `Y_u` is `ζ_N^{u∧τ_i}(U^{u∧τ_i,τ_i}φ_i)`.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas

variable {d : ℕ}

theorem s102_coeff_bdd {N : ℕ} (hN : 0 < N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → EucConfig d N) (hXm : ∀ t, Measurable (X t)) :
    ∃ Cb : ℝ, ∀ (u : ℝ) (ζ : Ω) (α : MultiIndex d),
      |HRS.Whole.measureHermiteCoeff (HRS.Whole.empirical (X u.toNNReal ζ)) α -
        HRS.Whole.measureHermiteCoeff (HRS.Whole.meanEmpirical (P.map (X u.toNNReal))) α| ≤ Cb := by
  obtain ⟨Ch, hCh⟩ := hermiteFunD_uniform_bound (d := d)
  refine ⟨2 * Ch, fun u ζ α => ?_⟩
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hform : HRS.Whole.measureHermiteCoeff (HRS.Whole.meanEmpirical (P.map (X u.toNNReal))) α =
      (N : ℝ)⁻¹ * ∑ i, ∫ ζ', hermiteFunD α (X u.toNNReal ζ' i) ∂P := by
    have : IsProbabilityMeasure (P.map (X u.toNNReal)) := ⟨by
      rw [Measure.map_apply (hXm _) MeasurableSet.univ]; simp⟩
    have h := HRS.MS.S21.s21_integral_meanEmpirical (P.map (X u.toNNReal)) (f := hermiteFunD α)
      (contDiff_hermiteFunD α).continuous.measurable (B := Ch) (fun x => hCh α x)
    refine h.trans ?_
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact integral_map (hXm _).aemeasurable ((contDiff_hermiteFunD α).continuous.measurable.comp
      (measurable_pi_apply i)).aestronglyMeasurable
  have h1 : |HRS.Whole.measureHermiteCoeff (HRS.Whole.empirical (X u.toNNReal ζ)) α| ≤ Ch := by
    rw [show HRS.Whole.measureHermiteCoeff (HRS.Whole.empirical (X u.toNNReal ζ)) α =
      (N : ℝ)⁻¹ * ∑ i, hermiteFunD α (X u.toNNReal ζ i) from HRS.Whole.pair_empirical hN _ (hermiteFunD α),
      abs_mul, abs_of_nonneg (by positivity)]
    have hs : |∑ i, hermiteFunD α (X u.toNNReal ζ i)| ≤ N * Ch := by
      calc |∑ i, hermiteFunD α (X u.toNNReal ζ i)| ≤ ∑ i, |hermiteFunD α (X u.toNNReal ζ i)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin N, Ch := Finset.sum_le_sum fun i _ => hCh α _
        _ = N * Ch := by simp
    calc (N : ℝ)⁻¹ * |∑ i, hermiteFunD α (X u.toNNReal ζ i)| ≤ (N : ℝ)⁻¹ * (N * Ch) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = Ch := by field_simp
  have h2 : |HRS.Whole.measureHermiteCoeff (HRS.Whole.meanEmpirical (P.map (X u.toNNReal))) α| ≤ Ch := by
    rw [hform, abs_mul, abs_of_nonneg (by positivity)]
    have hs : |∑ i, ∫ ζ', hermiteFunD α (X u.toNNReal ζ' i) ∂P| ≤ N * Ch := by
      calc |∑ i, ∫ ζ', hermiteFunD α (X u.toNNReal ζ' i) ∂P|
          ≤ ∑ i, |∫ ζ', hermiteFunD α (X u.toNNReal ζ' i) ∂P| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin N, Ch := Finset.sum_le_sum fun i _ => by
            have := norm_integral_le_of_norm_le_const (μ := P)
              (f := fun ζ' => hermiteFunD α (X u.toNNReal ζ' i)) (C := Ch)
              (Eventually.of_forall fun ζ' => by rw [Real.norm_eq_abs]; exact hCh α _)
            simpa [Real.norm_eq_abs] using this
        _ = N * Ch := by simp
    calc (N : ℝ)⁻¹ * |∑ i, ∫ ζ', hermiteFunD α (X u.toNNReal ζ' i) ∂P| ≤ (N : ℝ)⁻¹ * (N * Ch) :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = Ch := by field_simp
  calc _ ≤ |HRS.Whole.measureHermiteCoeff (HRS.Whole.empirical (X u.toNNReal ζ)) α| +
        |HRS.Whole.measureHermiteCoeff (HRS.Whole.meanEmpirical (P.map (X u.toNNReal))) α| := abs_sub _ _
    _ ≤ 2 * Ch := by linarith

theorem s102_coord_zetaB {m : ℝ} (hm : (d : ℝ) < m) {N : ℕ} (hN : 0 < N) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → EucConfig d N) (hXm : ∀ t, Measurable (X t))
    (u : ℝ) (ζ : Ω) (α : MultiIndex d) :
    OscDual.coord (zetaB m (P.map (X u.toNNReal)) (X u.toNNReal ζ)) α = s102_zf P X ζ u (oscTestFun m α) := by
  obtain ⟨Cb, hCb⟩ := s102_coeff_bdd hN P X hXm
  have hmem := s102_ofSeq_mem (m := m) hm (fun α => HRS.Whole.measureHermiteCoeff (HRS.Whole.empirical (X u.toNNReal ζ)) α -
    HRS.Whole.measureHermiteCoeff (HRS.Whole.meanEmpirical (P.map (X u.toNNReal))) α) (C0 := Cb) (hCb u ζ)
  unfold zetaB OscDual.ofMeasureDiff
  rw [OscDual.coord_smul, OscDual.coord_ofSeq_of_mem _ hmem]
  unfold s102_zf HRS.Whole.pair HRS.Whole.measureHermiteCoeff oscTestFun
  simp only [integral_const_mul]
  ring

end HRS.MS.R2Interp

end
