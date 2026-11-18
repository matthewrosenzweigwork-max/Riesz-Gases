import HRS.PDE.MovDAux3

/-!
# MOVD Aux4: truncation of the initial density (`movT_cond_entropy_limit`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {α : Type*} [MeasurableSpace α]

theorem movd_truncLaw_eq_cond (ν Q : Measure α) (k : ℕ) :
    movT_truncLaw ν Q k = movT_cond ν (movT_truncSet ν Q k) := rfl

/-- Properties of the truncated law at a level with `ν(B_k) ≠ 0`. -/
theorem movd_trunc_props (ν Q : Measure α) [IsProbabilityMeasure ν] [IsProbabilityMeasure Q]
    (hac : ν ≪ Q) (hint : Integrable (llr ν Q) ν) {k : ℕ} (h0 : ν (movT_truncSet ν Q k) ≠ 0) :
    IsProbabilityMeasure (movT_truncLaw ν Q k) ∧ movT_truncLaw ν Q k ≪ Q ∧
    Integrable (llr (movT_truncLaw ν Q k) Q) (movT_truncLaw ν Q k) ∧
    (klDiv (movT_truncLaw ν Q k) Q).toReal =
      ((ν (movT_truncSet ν Q k)).toReal)⁻¹ * ∫ x in movT_truncSet ν Q k, llr ν Q x ∂ν +
        Real.log (((ν (movT_truncSet ν Q k)).toReal)⁻¹) ∧
    (∃ kk : ℝ, ∀ᵐ x ∂Q, (movT_truncLaw ν Q k).rnDeriv Q x ≤ ENNReal.ofReal kk) := by
  set B := movT_truncSet ν Q k with hBdef
  have hBm : MeasurableSet B := movT_truncSet_meas ν Q k
  set c : ℝ≥0∞ := (ν B)⁻¹ with hc
  have hc0 : c ≠ 0 := ENNReal.inv_ne_zero.2 (measure_ne_top _ _)
  have hct : c ≠ ⊤ := ENNReal.inv_ne_top.2 h0
  have hμB : ν.restrict B ≪ Q := Measure.restrict_le_self.absolutelyContinuous.trans hac
  have hlaw : movT_truncLaw ν Q k = c • ν.restrict B := rfl
  have hprob : IsProbabilityMeasure (movT_truncLaw ν Q k) := by
    rw [movd_truncLaw_eq_cond]
    exact movT_cond_isProb ν h0 (measure_ne_top _ _)
  have hacK : movT_truncLaw ν Q k ≪ Q := by
    rw [hlaw]; exact Measure.smul_absolutelyContinuous.trans hμB
  have haeμ : ∀ᵐ x ∂(ν.restrict B), llr (ν.restrict B) Q x = llr ν Q x := by
    have h1 := hμB.ae_le (Measure.rnDeriv_restrict ν Q hBm)
    filter_upwards [h1, ae_restrict_mem hBm] with x hx hxB
    simp only [llr, hx, Set.indicator_of_mem hxB]
  have hllr : llr (c • ν.restrict B) Q =ᵐ[ν.restrict B] fun x => llr ν Q x + Real.log c.toReal := by
    filter_upwards [llr_smul_left hμB c hc0 hct, haeμ] with x hx1 hx2
    rw [hx1, hx2]
  have hllrK : llr (movT_truncLaw ν Q k) Q =ᵐ[movT_truncLaw ν Q k]
      fun x => llr ν Q x + Real.log c.toReal := by
    rw [hlaw]
    exact Measure.smul_absolutelyContinuous.ae_le hllr
  have hintB : Integrable (fun x => llr ν Q x + Real.log c.toReal) (ν.restrict B) :=
    hint.restrict.add (integrable_const _)
  have hintK : Integrable (llr (movT_truncLaw ν Q k) Q) (movT_truncLaw ν Q k) := by
    refine Integrable.congr ?_ hllrK.symm
    rw [hlaw]
    exact hintB.smul_measure hct
  have hνB : (ν B).toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h0, measure_ne_top _ _⟩
  have hct' : c.toReal = ((ν B).toReal)⁻¹ := by rw [hc, ENNReal.toReal_inv]
  have hkl : (klDiv (movT_truncLaw ν Q k) Q).toReal =
      ((ν B).toReal)⁻¹ * ∫ x in B, llr ν Q x ∂ν + Real.log (((ν B).toReal)⁻¹) := by
    rw [toReal_klDiv_of_measure_eq hacK (by simp [measure_univ])]
    rw [integral_congr_ae hllrK, hlaw, integral_smul_measure, integral_add hint.restrict
      (integrable_const _), integral_const]
    simp only [smul_eq_mul, measureReal_def, Measure.restrict_apply_univ, hct']
    field_simp
  refine ⟨hprob, hacK, hintK, hkl, ?_⟩
  refine ⟨c.toReal * k, ?_⟩
  have h1 := Measure.rnDeriv_smul_left_of_ne_top (ν.restrict B) Q hct
  have h2 := Measure.rnDeriv_restrict ν Q hBm
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hlaw, hx1]
  simp only [Pi.smul_apply, smul_eq_mul, hx2]
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hct]
  refine mul_le_mul' le_rfl ?_
  by_cases hxB : x ∈ B
  · rw [Set.indicator_of_mem hxB]
    simpa [hBdef, movT_truncSet] using hxB
  · rw [Set.indicator_of_notMem hxB]; simp

theorem movd_trunc_tendsto (ν Q : Measure α) [IsProbabilityMeasure ν] [IsProbabilityMeasure Q]
    (hac : ν ≪ Q) :
    Tendsto (fun k : ℕ => ν (movT_truncSet ν Q k)) atTop (𝓝 1) ∧
      Monotone (movT_truncSet ν Q) ∧ ν (⋃ k, movT_truncSet ν Q k) = 1 := by
  have hmono : Monotone (movT_truncSet ν Q) := fun a b hab x hx =>
    le_trans hx (ENNReal.ofReal_le_ofReal (by exact_mod_cast hab))
  have hae : ∀ᵐ x ∂ν, x ∈ ⋃ k, movT_truncSet ν Q k := by
    filter_upwards [hac.ae_le (Measure.rnDeriv_lt_top ν Q)] with x hx
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hx.ne
    refine Set.mem_iUnion.2 ⟨n, ?_⟩
    simp only [movT_truncSet, Set.mem_ofPred_eq]
    rw [ENNReal.ofReal_natCast]
    exact hn.le
  have hU : ν (⋃ k, movT_truncSet ν Q k) = 1 := by
    have h0 : ν (⋃ k, movT_truncSet ν Q k)ᶜ = 0 := by
      exact ae_iff.1 hae
    exact (prob_compl_eq_zero_iff (MeasurableSet.iUnion fun k => movT_truncSet_meas ν Q k)).1 h0
  refine ⟨?_, hmono, hU⟩
  have := tendsto_measure_iUnion_atTop (μ := ν) hmono
  rwa [hU] at this

theorem movd_cond_entropy_limit (ν Q : Measure α)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure Q] (hfin : relEntropy ν Q ≠ ⊤) :
    ∃ K₀ : ℕ, Tendsto (fun k : ℕ => ν (movT_truncSet ν Q k)) atTop (𝓝 1) ∧
      (∀ k : ℕ, K₀ ≤ k → ν (movT_truncSet ν Q k) ≠ 0 ∧ movT_truncLaw ν Q k ≪ Q ∧
        (∃ kk : ℝ, ∀ᵐ x ∂Q, (movT_truncLaw ν Q k).rnDeriv Q x ≤ ENNReal.ofReal kk) ∧
        relEntropy (movT_truncLaw ν Q k) Q ≠ ⊤) ∧
      Tendsto (fun k : ℕ => (relEntropy (movT_truncLaw ν Q k) Q).toReal) atTop
        (𝓝 (relEntropy ν Q).toReal) := by
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.1 (show klDiv ν Q ≠ ⊤ from hfin)
  obtain ⟨hν1, hmono, hU⟩ := movd_trunc_tendsto ν Q hac
  obtain ⟨K₀, hK⟩ := eventually_atTop.1 (hν1.eventually (lt_mem_nhds (zero_lt_one' ℝ≥0∞)))
  have hpos : ∀ k, K₀ ≤ k → ν (movT_truncSet ν Q k) ≠ 0 := fun k hk => (hK k hk).ne'
  refine ⟨K₀, hν1, fun k hk => ?_, ?_⟩
  · obtain ⟨hp, hacK, hintK, -, hb⟩ := movd_trunc_props ν Q hac hint (hpos k hk)
    exact ⟨hpos k hk, hacK, hb, klDiv_ne_top hacK hintK⟩
  · have hlim : ∫ x, llr ν Q x ∂ν = (klDiv ν Q).toReal :=
      (toReal_klDiv_of_measure_eq hac (by simp [measure_univ])).symm
    have hr : Tendsto (fun k : ℕ => (ν (movT_truncSet ν Q k)).toReal) atTop (𝓝 1) := by
      have := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp hν1
      rw [ENNReal.toReal_one] at this
      exact this
    have hI : Tendsto (fun k : ℕ => ∫ x in movT_truncSet ν Q k, llr ν Q x ∂ν) atTop
        (𝓝 (∫ x, llr ν Q x ∂ν)) := by
      have := tendsto_setIntegral_of_monotone (μ := ν) (f := llr ν Q)
        (fun k => movT_truncSet_meas ν Q k) hmono hint.integrableOn
      have hae : (⋃ k, movT_truncSet ν Q k) =ᵐ[ν] (Set.univ : Set α) := by
        rw [ae_eq_univ]
        exact (prob_compl_eq_zero_iff (MeasurableSet.iUnion fun k => movT_truncSet_meas ν Q k)).2 hU
      rwa [setIntegral_congr_set hae, Measure.restrict_univ] at this
    have hform : Tendsto (fun k : ℕ => ((ν (movT_truncSet ν Q k)).toReal)⁻¹ *
        ∫ x in movT_truncSet ν Q k, llr ν Q x ∂ν +
          Real.log (((ν (movT_truncSet ν Q k)).toReal)⁻¹)) atTop
        (𝓝 (1⁻¹ * ∫ x, llr ν Q x ∂ν + Real.log (1⁻¹))) := by
      refine Tendsto.add ((hr.inv₀ one_ne_zero).mul hI) ?_
      exact Tendsto.log (hr.inv₀ one_ne_zero) (by norm_num)
    simp only [inv_one, one_mul, Real.log_one, add_zero] at hform
    rw [show (relEntropy ν Q).toReal = ∫ x, llr ν Q x ∂ν from hlim.symm]
    refine hform.congr' ?_
    filter_upwards [eventually_ge_atTop K₀] with k hk
    obtain ⟨-, -, -, hkl, -⟩ := movd_trunc_props ν Q hac hint (hpos k hk)
    exact hkl.symm

end HRS

end
