import HRS.MS.S81G_Conv
import HRS.MS.S81G_Mom
import HRS.MS.S81R_Pot
import HRS.MS.GapRefAux2

/-!
# S81R, packet R7d: the rescaled regularised Gibbs law is a `GapRef` reference measure

For `D = Whole.quadraticGradientDyn d s a β`, `k = sb1kM d s M`, `Φ = √β enc : EucConfig d N ≃L Euc (N*d)`:
`s81r_gapref`: there are `ρ, G` on `Euc (N*d)` with `GapRef (N*d) ρ a (∇G)`, `(sb1Gam D k N).map Φ = withDensityReal ρ` and
`-a y + ∇G(y) = √β enc (b_k(Ψ y))`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl HRS.MS.MfeConf HRS.MS.Gap HRS.MS.S81G
open scoped ENNReal NNReal

namespace HRS.MS.S81R

variable {d N : ℕ}

theorem s81r_hc_exists {β : ℝ} (hβ : 0 < β) (d N : ℕ) :
    ∃ c : ℝ≥0, 0 < c ∧ (volume : Measure (Whole.EucConfig d N)).map (s81r_PhiE hβ d N) =
      c • (volume : Measure (Euc (N * d))) := by
  haveI h1 : (volume : Measure (Whole.EucConfig d N)).IsAddHaarMeasure := inferInstance
  haveI h2 : ((volume : Measure (Whole.EucConfig d N)).map (s81r_PhiE hβ d N)).IsAddHaarMeasure :=
    (s81r_PhiE hβ d N).isAddHaarMeasure_map _
  have h := Measure.isAddLeftInvariant_eq_smul
    ((volume : Measure (Whole.EucConfig d N)).map (s81r_PhiE hβ d N))
    (volume : Measure (Euc (N * d)))
  exact ⟨_, Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _, h⟩

theorem s81r_map_withDensity {β : ℝ} (hβ : 0 < β) {c : ℝ≥0}
    (hc : (volume : Measure (Whole.EucConfig d N)).map (s81r_PhiE hβ d N) =
      c • (volume : Measure (Euc (N * d))))
    (f : Whole.EucConfig d N → ℝ≥0∞) (hf : Measurable f) :
    ((volume : Measure (Whole.EucConfig d N)).withDensity f).map (s81r_PhiE hβ d N) =
      (volume : Measure (Euc (N * d))).withDensity
        (fun y => (c : ℝ≥0∞) * f (s81r_Psi β d N y)) := by
  have hemb : MeasurableEmbedding (s81r_PhiE hβ d N) :=
    (s81r_PhiE hβ d N).toHomeomorph.measurableEmbedding
  have hΦm : Measurable (s81r_PhiE hβ d N) := hemb.measurable
  ext A hA
  rw [Measure.map_apply hΦm hA, withDensity_apply' _ (s81r_PhiE hβ d N ⁻¹' A),
    withDensity_apply' _ A]
  have hΨm : Measurable (s81r_Psi β d N) := (s81r_Psi β d N).continuous.measurable
  have h1 := setLIntegral_map (μ := (volume : Measure (Whole.EucConfig d N))) hA
    (hf.comp hΨm) hΦm
  have e : ∀ x, f (s81r_Psi β d N (s81r_PhiE hβ d N x)) = f x := fun x => by
    rw [s81r_PhiE_apply, s81r_Psi_Phi hβ]
  simp only [Function.comp_apply, e] at h1
  rw [← h1, hc, Measure.restrict_smul, lintegral_smul_measure,
    lintegral_const_mul' _ _ ENNReal.coe_ne_top, ENNReal.smul_def, smul_eq_mul]

theorem s81r_norm_Phi_sq {β : ℝ} (hβ : 0 < β) (x : Whole.EucConfig d N) :
    ‖s81r_Phi β d N x‖ ^ 2 ≤ β * N * ‖x‖ ^ 2 := by
  rw [s81r_Phi_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hβ.le,
    s81r_enc_norm_sq]
  have : ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin N, ‖x‖ ^ 2 :=
    Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm x i) 2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  nlinarith

theorem s81r_gapref {s a β : ℝ} (hd : 1 ≤ d) (hs : 0 ≤ s) (ha : 0 < a) (hβ : 0 < β) (M : ℕ) :
    ∃ (ρ G : Euc (N * d) → ℝ), GapRef (N * d) ρ a (gradient G) ∧
      (sb1Gam (Whole.quadraticGradientDyn d s a β) (sb1kM d s M) N).map (s81r_PhiE hβ d N) =
        Whole.withDensityReal ρ ∧
      ∀ y, -a • y + gradient G y = Real.sqrt β • s81r_encFun
        (sb1DriftM (Whole.quadraticGradientDyn d s a β) (sb1kM d s M) N (s81r_Psi β d N y)) := by
  set D := Whole.quadraticGradientDyn d s a β with hD
  set k := sb1kM d s M with hk
  have hker := sb1kM_isKernel (d := d) s hs M
  obtain ⟨B0, hB0⟩ := s81g_pot (d := d) a
  have hβ' : 0 < D.invβ := inv_pos.2 hβ
  have hinv : D.invβ⁻¹ = β := inv_inv β
  have H : S81Hyp D :=
    ⟨hs, hd, hβ', by show Continuous (fun x : Euc d => a * ‖x‖ ^ 2 / 2); fun_prop,
      ⟨a / 2, 0, by positivity, fun x => s81g_conf_lower a x⟩⟩
  obtain ⟨c, hcpos, hc⟩ := s81r_hc_exists hβ d N
  have hZ : 0 < sb1Gz D k N := s81g_reg_gz_pos H M
  have hHm : Measurable (sb1Hs D k N) := s81g_reg_meas H M
  haveI hQp : IsProbabilityMeasure (sb1Gam D k N) := s81g_reg_prob H M
  have hGqm : Measurable (sb1Gq D k N) := (s81g_Gw_meas hHm).div_const _
  have hGq0 : ∀ x, 0 < sb1Gq D k N x := fun x => div_pos (Real.exp_pos _) hZ
  have hΨm : Measurable (s81r_Psi β d N) := (s81r_Psi β d N).continuous.measurable
  set ρ : Euc (N * d) → ℝ := fun y => (c : ℝ) * sb1Gq D k N (s81r_Psi β d N y) with hρdef
  have hρm : Measurable ρ := (hGqm.comp hΨm).const_mul _
  have hρ0 : ∀ y, 0 ≤ ρ y := fun y => mul_nonneg c.coe_nonneg (hGq0 _).le
  set κ : ℝ := Real.log ((c : ℝ) / sb1Gz D k N) with hκ
  set G : Euc (N * d) → ℝ := fun y => s81r_G0 β k N y + κ with hGdef
  have hBd : s81r_Bd G := s81r_Bd_add_const (s81r_Bd_G0 β (s81r_Bd_kM hs M)) κ
  -- the law of the rescaled initial datum
  have hf0 : Measurable (fun x => ENNReal.ofReal (sb1Gq D k N x)) := hGqm.ennreal_ofReal
  have hlaw : (sb1Gam D k N).map (s81r_PhiE hβ d N) = Whole.withDensityReal ρ := by
    unfold sb1Gam sb1Dm Whole.withDensityReal
    rw [s81r_map_withDensity hβ hc _ hf0]
    congr 1
    funext y
    show (c : ℝ≥0∞) * ENNReal.ofReal (sb1Gq D k N (s81r_Psi β d N y)) =
      ENNReal.ofReal ((c : ℝ) * sb1Gq D k N (s81r_Psi β d N y))
    rw [ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  have hmass : ∫⁻ y, ENNReal.ofReal (ρ y) = 1 := by
    have h1 : (Whole.withDensityReal ρ) Set.univ = 1 := by
      rw [← hlaw, Measure.map_apply (s81r_PhiE hβ d N).continuous.measurable MeasurableSet.univ,
        Set.preimage_univ, measure_univ]
    unfold Whole.withDensityReal at h1
    rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1
  have hint : Integrable ρ := by
    refine ⟨hρm.aestronglyMeasurable, ?_⟩
    have hen : ∀ y, ‖ρ y‖ₑ = ENNReal.ofReal (ρ y) := fun y => Real.enorm_eq_ofReal (hρ0 y)
    simp only [HasFiniteIntegral, hen]
    rw [hmass]
    exact ENNReal.one_lt_top
  have hint1 : ∫ y, ρ y = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hρ0) hρm.aestronglyMeasurable,
      hmass]
    simp
  -- second moment
  have hmom : ∫⁻ x, ENNReal.ofReal (‖s81r_Phi β d N x‖ ^ 2) ∂(sb1Gam D k N) < ⊤ := by
    obtain ⟨cV, CV, hcV, hV⟩ := H.conf
    obtain ⟨c0, hc0, hex⟩ := s81g_exp_moment (N := N) H.invβ_pos hHm hker.lower hcV hV
    have hle : ∀ x : Whole.EucConfig d N, ENNReal.ofReal (‖s81r_Phi β d N x‖ ^ 2) ≤
        ENNReal.ofReal (β * N / c0) * ENNReal.ofReal (Real.exp (c0 * ‖x‖ ^ 2)) := by
      intro x
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 := s81r_norm_Phi_sq hβ x
      have h2 : c0 * ‖x‖ ^ 2 ≤ Real.exp (c0 * ‖x‖ ^ 2) := by
        linarith [Real.add_one_le_exp (c0 * ‖x‖ ^ 2)]
      calc ‖s81r_Phi β d N x‖ ^ 2 ≤ β * N * ‖x‖ ^ 2 := h1
        _ = β * N / c0 * (c0 * ‖x‖ ^ 2) := by field_simp
        _ ≤ β * N / c0 * Real.exp (c0 * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
    calc ∫⁻ x, ENNReal.ofReal (‖s81r_Phi β d N x‖ ^ 2) ∂(sb1Gam D k N)
        ≤ ∫⁻ x, ENNReal.ofReal (β * N / c0) * ENNReal.ofReal (Real.exp (c0 * ‖x‖ ^ 2))
            ∂(sb1Gam D k N) := lintegral_mono hle
      _ = ENNReal.ofReal (β * N / c0) * ∫⁻ x, ENNReal.ofReal (Real.exp (c0 * ‖x‖ ^ 2))
            ∂(sb1Gam D k N) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hex
  have hm2 : Integrable (fun y => ‖y‖ ^ 2 * ρ y) := by
    have hm : Measurable (fun y : Euc (N * d) => ‖y‖ ^ 2 * ρ y) :=
      (measurable_norm.pow_const 2).mul hρm
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    have hnn : ∀ y : Euc (N * d), 0 ≤ ‖y‖ ^ 2 * ρ y := fun y => mul_nonneg (sq_nonneg _) (hρ0 y)
    have hen : ∀ y : Euc (N * d), ‖‖y‖ ^ 2 * ρ y‖ₑ = ENNReal.ofReal (‖y‖ ^ 2 * ρ y) :=
      fun y => Real.enorm_eq_ofReal (hnn y)
    simp only [HasFiniteIntegral, hen]
    have hg : Measurable (fun y : Euc (N * d) => ENNReal.ofReal (‖y‖ ^ 2)) :=
      (measurable_norm.pow_const 2).ennreal_ofReal
    have hf : Measurable (fun y : Euc (N * d) => ENNReal.ofReal (ρ y)) := hρm.ennreal_ofReal
    have h1 : ∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2 * ρ y) =
        ∫⁻ y, ENNReal.ofReal (‖y‖ ^ 2) ∂(Whole.withDensityReal ρ) := by
      unfold Whole.withDensityReal
      rw [lintegral_withDensity_eq_lintegral_mul _ hf hg]
      refine lintegral_congr fun y => ?_
      simp only [Pi.mul_apply]
      rw [ENNReal.ofReal_mul (sq_nonneg _), mul_comm]
    rw [h1, ← hlaw, lintegral_map hg (s81r_PhiE hβ d N).continuous.measurable]
    simpa [s81r_PhiE_apply] using hmom
  have hρ : ∀ y, ρ y = Real.exp (-(a / 2) * ‖y‖ ^ 2 + G y) := by
    intro y
    have hcZ : 0 < (c : ℝ) / sb1Gz D k N := div_pos (by exact_mod_cast hcpos) hZ
    have e1 : Real.exp (-D.invβ⁻¹ * sb1Hs D k N (s81r_Psi β d N y)) =
        Real.exp (-(a / 2) * ‖y‖ ^ 2 + s81r_G0 β k N y) := by
      rw [hinv]
      congr 1
      have := s81r_beta_Hs (s := s) (a := a) hβ k (N := N) y
      linarith
    simp only [hρdef, sb1Gq, hGdef, hκ]
    rw [show (-(a / 2) * ‖y‖ ^ 2 + (s81r_G0 β k N y + Real.log ((c : ℝ) / sb1Gz D k N))) =
      (-(a / 2) * ‖y‖ ^ 2 + s81r_G0 β k N y) + Real.log ((c : ℝ) / sb1Gz D k N) by ring,
      Real.exp_add, Real.exp_log hcZ, ← e1]
    field_simp
  have hgrad : ∀ y, gradient G y = gradient (s81r_G0 β k N) y := fun y => by
    simp only [gradient, hGdef]
    rw [fderiv_add_const]
  refine ⟨ρ, G, gap_of_logDensity hBd.1 hBd.2 hρ hint hint1 hm2, hlaw, fun y => ?_⟩
  rw [hgrad y, s81r_grad_G0 hβ hker hB0 y, neg_smul]
  exact neg_add_cancel_left _ _

end HRS.MS.S81R
