import HRS.Sections.AdjKGlueAux10

/-!
# ADJK-GLUE, part 11: characteristic functions are controlled by `smoothDist 2`
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.AdjK

open HRS.Uniform

section Contractions

variable {B B' : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]
  [NormedAddCommGroup B'] [NormedSpace ℝ B'] [MeasurableSpace B'] [BorelSpace B']

/-- Copy of `HRS.Main.smoothDist_map_clm_le` (avoids importing `HRS.Main.Headline`). -/
theorem adjkg_smoothDist_map_clm_le (L : B →L[ℝ] B') (k : ℕ) (P Q : Measure B) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    smoothDist k (P.map L) (Q.map L) ≤ max 1 (‖L‖ ^ k) * smoothDist k P Q := by
  set c : ℝ := max 1 (‖L‖ ^ k) with hc_def
  have hc1 : 1 ≤ c := le_max_left _ _
  have hcpos : 0 < c := by linarith
  have hLm : Measurable L := L.continuous.measurable
  have hpow : ∀ j ≤ k, ‖L‖ ^ j ≤ c := by
    intro j hj
    rcases le_total ‖L‖ 1 with h | h
    · exact le_trans (pow_le_one₀ (norm_nonneg _) h) hc1
    · exact le_trans (pow_le_pow_right₀ h hj) (le_max_right _ _)
  refine Real.iSup_le (fun Φ => ?_) (mul_nonneg (le_trans zero_le_one hc1) (smoothDist_nonneg k P Q))
  obtain ⟨hΦd, hΦb, hΦn⟩ := Φ.2
  set M : ℕ → ℝ := fun j => ⨆ y : B', ‖iteratedFDeriv ℝ j Φ.1 y‖ with hM_def
  have hM0 : ∀ j, 0 ≤ M j := fun j => Real.iSup_nonneg fun _ => norm_nonneg _
  have hcomp : ∀ j ≤ k, ∀ z : B, ‖iteratedFDeriv ℝ j (fun z => Φ.1 (L z)) z‖ ≤ ‖L‖ ^ j * M j := by
    intro j hj z
    have e := ContinuousLinearMap.iteratedFDeriv_comp_right (𝕜 := ℝ) L hΦd (x := z) (i := j)
      (by exact_mod_cast hj)
    rw [show (fun z => Φ.1 (L z)) = Φ.1 ∘ L from rfl, e]
    have h1 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ j Φ.1 (L z)) (fun _ : Fin j => L)
    have h2 : ‖iteratedFDeriv ℝ j Φ.1 (L z)‖ ≤ M j :=
      le_ciSup (hΦb j (by exact_mod_cast hj)) (L z)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
    calc _ ≤ _ := h1
      _ ≤ M j * ‖L‖ ^ j := mul_le_mul h2 le_rfl (by positivity) (hM0 j)
      _ = _ := mul_comm _ _
  set Ψ : B → ℝ := fun z => c⁻¹ • Φ.1 (L z) with hΨ_def
  have hΨD : ∀ j ≤ k, ∀ z : B, ‖iteratedFDeriv ℝ j Ψ z‖ ≤ M j := by
    intro j hj z
    have e : iteratedFDeriv ℝ j Ψ z = c⁻¹ • iteratedFDeriv ℝ j (fun z => Φ.1 (L z)) z :=
      iteratedFDeriv_const_smul_apply'
        (((hΦd.comp L.contDiff).of_le (by exact_mod_cast hj : (j : WithTop ℕ∞) ≤ k)).contDiffAt)
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcpos)]
    calc c⁻¹ * ‖iteratedFDeriv ℝ j (fun z => Φ.1 (L z)) z‖ ≤ c⁻¹ * (‖L‖ ^ j * M j) :=
          mul_le_mul_of_nonneg_left (hcomp j hj z) (inv_nonneg.mpr hcpos.le)
      _ ≤ c⁻¹ * (c * M j) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hpow j hj) (hM0 j)) (inv_nonneg.mpr hcpos.le)
      _ = M j := by field_simp
  have hΨmem : Ψ ∈ CbUnitBall B k := by
    refine ⟨(hΦd.comp L.contDiff).const_smul c⁻¹, fun j hj => ⟨M j, ?_⟩, ?_⟩
    · rintro _ ⟨z, rfl⟩
      exact hΨD j hj z
    · unfold cbNorm
      calc ∑ j ∈ Finset.range (k + 1), ⨆ z : B, ‖iteratedFDeriv ℝ j Ψ z‖
          ≤ ∑ j ∈ Finset.range (k + 1), M j :=
            Finset.sum_le_sum fun j hj => ciSup_le fun z =>
              hΨD j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) z
        _ = cbNorm k Φ.1 := rfl
        _ ≤ 1 := hΦn
  have hsd := abs_integral_sub_le_smoothDist hΨmem P Q
  have hΦc : Continuous Φ.1 := hΦd.continuous
  have e : ∫ z, Φ.1 (L z) ∂P - ∫ z, Φ.1 (L z) ∂Q = c * (∫ z, Ψ z ∂P - ∫ z, Ψ z ∂Q) := by
    have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hcpos.ne'
    simp only [hΨ_def, smul_eq_mul, integral_const_mul]
    linear_combination (-(∫ z, Φ.1 (L z) ∂P - ∫ z, Φ.1 (L z) ∂Q)) * hcc
  rw [smoothDist, show |∫ z, Φ.1 z ∂(P.map L) - ∫ z, Φ.1 z ∂(Q.map L)| =
      |∫ z, Φ.1 (L z) ∂P - ∫ z, Φ.1 (L z) ∂Q| by
    rw [integral_map hLm.aemeasurable hΦc.aestronglyMeasurable,
      integral_map hLm.aemeasurable hΦc.aestronglyMeasurable]]
  rw [e, abs_mul, abs_of_pos hcpos]
  exact mul_le_mul_of_nonneg_left hsd hcpos.le

end Contractions

theorem adjkg_trig_mem {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hb : ∀ (n : ℕ) (x : ℝ), |iteratedDeriv n f x| ≤ 1) :
    (fun y : ℝ => (1 / 3 : ℝ) * f y) ∈ CbUnitBall ℝ 2 := by
  have hD : ∀ (j : ℕ) (y : ℝ), ‖iteratedFDeriv ℝ j (fun y : ℝ => (1 / 3 : ℝ) * f y) y‖ ≤ 1 / 3 := by
    intro j y
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_const_mul_field, Real.norm_eq_abs,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 3)]
    have := hb j y
    nlinarith
  refine ⟨(contDiff_const.mul hf).of_le le_rfl, fun j _ => ⟨1 / 3, ?_⟩, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact hD j y
  · unfold cbNorm
    have : ∀ j ∈ Finset.range (2 + 1), (⨆ y : ℝ, ‖iteratedFDeriv ℝ j (fun y : ℝ => (1 / 3 : ℝ) * f y) y‖) ≤ 1 / 3 :=
      fun j _ => ciSup_le fun y => hD j y
    calc ∑ j ∈ Finset.range (2 + 1), (⨆ y : ℝ, ‖iteratedFDeriv ℝ j (fun y : ℝ => (1 / 3 : ℝ) * f y) y‖)
        ≤ ∑ j ∈ Finset.range (2 + 1), (1 / 3 : ℝ) := Finset.sum_le_sum this
      _ = 1 := by simp

theorem adjkg_charFun_eq {p : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure μ]
    (t : EuclideanSpace ℝ (Fin p)) :
    charFun μ t = ((∫ x, Real.cos (innerSL ℝ t x) ∂μ : ℝ) : ℂ) +
      Complex.I * ((∫ x, Real.sin (innerSL ℝ t x) ∂μ : ℝ) : ℂ) := by
  have hLx : ∀ x : EuclideanSpace ℝ (Fin p), innerSL ℝ t x = inner ℝ x t := fun x => by
    rw [innerSL_apply_apply, real_inner_comm]
  have hLc : Continuous (innerSL ℝ t : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ) := (innerSL ℝ t).continuous
  have h1 : Integrable (fun x : EuclideanSpace ℝ (Fin p) => Real.cos (innerSL ℝ t x)) μ :=
    Integrable.of_bound (Real.continuous_cos.comp hLc).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by simpa using Real.abs_cos_le_one _)
  have h2 : Integrable (fun x : EuclideanSpace ℝ (Fin p) => Real.sin (innerSL ℝ t x)) μ :=
    Integrable.of_bound (Real.continuous_sin.comp hLc).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by simpa using Real.abs_sin_le_one _)
  rw [charFun_apply]
  have e : ∀ x : EuclideanSpace ℝ (Fin p), Complex.exp ((inner ℝ x t : ℝ) * Complex.I) =
      ((Real.cos (innerSL ℝ t x) : ℝ) : ℂ) + Complex.I * ((Real.sin (innerSL ℝ t x) : ℝ) : ℂ) := by
    intro x
    rw [Complex.exp_mul_I, ← hLx x]
    push_cast
    ring
  simp_rw [e]
  rw [integral_add h1.ofReal (h2.ofReal.const_mul _), integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]

theorem adjkg_charFun_sub_le {p : ℕ} (μ ν : Measure (EuclideanSpace ℝ (Fin p)))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (t : EuclideanSpace ℝ (Fin p)) :
    ‖charFun μ t - charFun ν t‖ ≤ 6 * max 1 (‖t‖ ^ 2) * smoothDist 2 μ ν := by
  set L : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ := innerSL ℝ t with hL
  have hLn : ‖L‖ = ‖t‖ := innerSL_apply_norm ℝ t
  haveI hmapμ : IsProbabilityMeasure (μ.map L) :=
    (Measure.isProbabilityMeasure_map_iff L.continuous.aemeasurable).2 inferInstance
  haveI hmapν : IsProbabilityMeasure (ν.map L) :=
    (Measure.isProbabilityMeasure_map_iff L.continuous.aemeasurable).2 inferInstance
  have hsm := adjkg_smoothDist_map_clm_le L 2 μ ν
  rw [hLn] at hsm
  set c : ℝ := max 1 (‖t‖ ^ 2) with hc
  have hc1 : 1 ≤ c := le_max_left _ _
  have hcos : (fun y : ℝ => (1 / 3 : ℝ) * Real.cos y) ∈ CbUnitBall ℝ 2 :=
    adjkg_trig_mem Real.contDiff_cos Real.abs_iteratedDeriv_cos_le_one
  have hsin : (fun y : ℝ => (1 / 3 : ℝ) * Real.sin y) ∈ CbUnitBall ℝ 2 :=
    adjkg_trig_mem Real.contDiff_sin Real.abs_iteratedDeriv_sin_le_one
  have key : ∀ f : ℝ → ℝ, Continuous f → (fun y : ℝ => (1 / 3 : ℝ) * f y) ∈ CbUnitBall ℝ 2 →
      Integrable (fun x : EuclideanSpace ℝ (Fin p) => f (L x)) μ →
      Integrable (fun x : EuclideanSpace ℝ (Fin p) => f (L x)) ν →
      |∫ x, f (L x) ∂μ - ∫ x, f (L x) ∂ν| ≤ 3 * c * smoothDist 2 μ ν := by
    intro f hf hmem hiμ hiν
    have h1 := abs_integral_sub_le_smoothDist hmem (μ.map L) (ν.map L)
    have e1 : ∫ y, (1 / 3 : ℝ) * f y ∂(μ.map L) = (1 / 3 : ℝ) * ∫ x, f (L x) ∂μ := by
      rw [integral_const_mul, integral_map L.continuous.aemeasurable hf.aestronglyMeasurable]
    have e2 : ∫ y, (1 / 3 : ℝ) * f y ∂(ν.map L) = (1 / 3 : ℝ) * ∫ x, f (L x) ∂ν := by
      rw [integral_const_mul, integral_map L.continuous.aemeasurable hf.aestronglyMeasurable]
    rw [e1, e2, ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 3)] at h1
    have := h1.trans hsm
    nlinarith
  have hLc : Continuous L := L.continuous
  have h1 : ∀ μ' : Measure (EuclideanSpace ℝ (Fin p)), IsProbabilityMeasure μ' →
      Integrable (fun x : EuclideanSpace ℝ (Fin p) => Real.cos (L x)) μ' := fun μ' _ =>
    Integrable.of_bound (Real.continuous_cos.comp hLc).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by simpa using Real.abs_cos_le_one _)
  have h2 : ∀ μ' : Measure (EuclideanSpace ℝ (Fin p)), IsProbabilityMeasure μ' →
      Integrable (fun x : EuclideanSpace ℝ (Fin p) => Real.sin (L x)) μ' := fun μ' _ =>
    Integrable.of_bound (Real.continuous_sin.comp hLc).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by simpa using Real.abs_sin_le_one _)
  have kc := key Real.cos Real.continuous_cos hcos (h1 μ inferInstance) (h1 ν inferInstance)
  have ks := key Real.sin Real.continuous_sin hsin (h2 μ inferInstance) (h2 ν inferInstance)
  rw [adjkg_charFun_eq μ t, adjkg_charFun_eq ν t]
  set a₁ : ℝ := ∫ x, Real.cos (L x) ∂μ
  set a₂ : ℝ := ∫ x, Real.cos (L x) ∂ν
  set b₁ : ℝ := ∫ x, Real.sin (L x) ∂μ
  set b₂ : ℝ := ∫ x, Real.sin (L x) ∂ν
  have e : ((a₁ : ℝ) : ℂ) + Complex.I * (b₁ : ℂ) - (((a₂ : ℝ) : ℂ) + Complex.I * (b₂ : ℂ)) =
      ((a₁ - a₂ : ℝ) : ℂ) + Complex.I * ((b₁ - b₂ : ℝ) : ℂ) := by push_cast; ring
  rw [e]
  calc ‖((a₁ - a₂ : ℝ) : ℂ) + Complex.I * ((b₁ - b₂ : ℝ) : ℂ)‖
      ≤ ‖((a₁ - a₂ : ℝ) : ℂ)‖ + ‖Complex.I * ((b₁ - b₂ : ℝ) : ℂ)‖ := norm_add_le _ _
    _ = |a₁ - a₂| + |b₁ - b₂| := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs]
    _ ≤ 3 * c * smoothDist 2 μ ν + 3 * c * smoothDist 2 μ ν := add_le_add kc ks
    _ = 6 * c * smoothDist 2 μ ν := by ring

end HRS.AdjK
