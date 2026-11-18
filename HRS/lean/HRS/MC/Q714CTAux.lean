import HRS.Sections.QuenchFinal

/-!
# Packet 7.14 CT (aux): the cosine test function and the Gaussian cosine expectation
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Q714.CT

/-- `E cos(c X) = exp(-c² E X² / 2)` for a centred real Gaussian `X`. -/
theorem ct_integral_cos {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : HasGaussianLaw X P) (h0 : ∫ ω, X ω ∂P = 0) (c : ℝ) :
    ∫ ω, Real.cos (c * X ω) ∂P = Real.exp (-(c ^ 2 / 2) * ∫ ω, X ω ^ 2 ∂P) := by
  have hm : AEMeasurable X P := hX.aemeasurable
  haveI : IsGaussian (P.map X) := hX.isGaussian_map
  have hμ := IsGaussian.eq_gaussianReal (P.map X) inferInstance
  have hmean : (P.map X)[id] = 0 := by
    rw [integral_map hm aestronglyMeasurable_id]; simpa using h0
  have hvar : Var[id; P.map X] = ∫ ω, X ω ^ 2 ∂P := by
    rw [variance_map aestronglyMeasurable_id.aemeasurable hm]
    exact variance_of_integral_eq_zero hm h0
  have h1 : ∫ ω, Real.cos (c * X ω) ∂P = ∫ x, Real.cos (c * x) ∂(P.map X) := by
    rw [integral_map hm (by fun_prop)]
  have h2 : ∫ x, Real.cos (c * x) ∂(P.map X) = (charFun (P.map X) c).re := by
    rw [charFun_apply_real]
    have hi : Integrable (fun x : ℝ => Complex.exp (↑c * ↑x * Complex.I)) (P.map X) := by
      refine Integrable.of_bound (C := 1) (by fun_prop) ?_
      refine Filter.Eventually.of_forall fun x => ?_
      have : (↑c * ↑x * Complex.I : ℂ) = ((c * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    have := integral_re hi
    simp only [RCLike.re_to_complex] at this
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have : (↑c * ↑x * Complex.I : ℂ) = ((c * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
    simp only [this, Complex.exp_ofReal_mul_I_re]
  have hv0 : 0 ≤ ∫ ω, X ω ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  rw [h1, h2, hμ, charFun_gaussianReal, hmean, hvar]
  have : Complex.exp (↑c * ↑(0 : ℝ) * Complex.I - ↑↑(∫ ω, X ω ^ 2 ∂P).toNNReal * ↑c ^ 2 / 2) =
      ((Real.exp (-(c ^ 2 / 2) * ∫ ω, X ω ^ 2 ∂P) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    rw [Real.coe_toNNReal _ hv0]
    push_cast
    ring
  rw [this, Complex.ofReal_re]

/-- The cosine test function `Φ = (1/6) cos ∘ L`. -/
def ctPhi {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] (L : B →L[ℝ] ℝ) : B → ℝ :=
  fun w => (1 / 6 : ℝ) * Real.cos (L w)

theorem ct_norm_iteratedFDeriv_le {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (L : B →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) (j : ℕ) (w : B) :
    ‖iteratedFDeriv ℝ j (ctPhi L) w‖ ≤ 1 / 6 := by
  have hg : ContDiff ℝ j (fun t : ℝ => (1 / 6 : ℝ) * Real.cos t) :=
    contDiff_const.mul Real.contDiff_cos
  have e : ctPhi L = (fun t : ℝ => (1 / 6 : ℝ) * Real.cos t) ∘ L := rfl
  rw [e, L.iteratedFDeriv_comp_right hg w le_rfl]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h1 : ∏ _i : Fin j, ‖L‖ ≤ 1 := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) hL
  have h2 : ‖iteratedFDeriv ℝ j (fun t : ℝ => (1 / 6 : ℝ) * Real.cos t) (L w)‖ ≤ 1 / 6 := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      iteratedDeriv_const_mul (1 / 6 : ℝ) Real.contDiff_cos.contDiffAt, Real.norm_eq_abs, abs_mul]
    have := Real.abs_iteratedDeriv_cos_le_one j (L w)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 6)]
    nlinarith [abs_nonneg (iteratedDeriv j Real.cos (L w))]
  calc _ ≤ ‖iteratedFDeriv ℝ j (fun t : ℝ => (1 / 6 : ℝ) * Real.cos t) (L w)‖ * 1 :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ ≤ 1 / 6 := by linarith

theorem ct_mem_cbUnitBall {B : Type} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    (L : B →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) : ctPhi L ∈ CbUnitBall B 5 := by
  refine ⟨contDiff_const.mul (Real.contDiff_cos.comp L.contDiff), fun j _ => ?_, ?_⟩
  · exact ⟨1 / 6, by rintro _ ⟨w, rfl⟩; exact ct_norm_iteratedFDeriv_le L hL j w⟩
  · unfold cbNorm
    have : ∀ j ∈ Finset.range (5 + 1), (⨆ z : B, ‖iteratedFDeriv ℝ j (ctPhi L) z‖) ≤ 1 / 6 := by
      intro j _
      exact ciSup_le fun z => ct_norm_iteratedFDeriv_le L hL j z
    calc _ ≤ ∑ _j ∈ Finset.range (5 + 1), (1 / 6 : ℝ) := Finset.sum_le_sum this
      _ = 1 := by simp

end HRS.MC.Q714.CT
