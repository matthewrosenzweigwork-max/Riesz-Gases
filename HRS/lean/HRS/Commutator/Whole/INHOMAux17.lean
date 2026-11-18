import HRS.Commutator.Whole.INHOMAux16

/-!
# CMX-INHOM auxiliary 17: `∇g_{>1} * b` for Schwartz `b`; the vanishing of `∇g_{>1} * a₀`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

lemma inhom_norm_le_sum (z : Euc d) : ‖z‖ ≤ ∑ i, |z i| := by
  have h := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr z
  conv_lhs => rw [← h]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_smul, (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.1 i, mul_one,
    EuclideanSpace.basisFun_repr, Real.norm_eq_abs]

lemma inhom_ghi_L1 (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    Integrable (fun z : Euc d => ‖ghiForce s z‖) volume := by
  obtain ⟨c, hc⟩ := inhom_ghi_conv hd hs0 hsd
  have hi : ∀ i : Fin d, Integrable (fun z : Euc d => |ghiForce s z i|) volume := by
    intro i
    have := (hc i).1.norm
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp [Complex.norm_real]
  have hsum : Integrable (fun z : Euc d => ∑ i, |ghiForce s z i|) volume :=
    integrable_finsetSum _ fun i _ => hi i
  refine hsum.mono' ?_ (Eventually.of_forall fun z => ?_)
  · exact (inhom_ghi_measurable hd hs0 hsd (d := d)).norm.aestronglyMeasurable
  · rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact inhom_norm_le_sum _

lemma inhom_conv_integrable (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {b : Euc d → ℝ}
    (hbm : Measurable b) {M : ℝ} (hM : ∀ x, |b x| ≤ M) (x : Euc d) :
    Integrable (fun y => b y • ghiForce s (x - y)) volume := by
  refine ((inhom_ghi_L1 hd hs0 hsd).comp_sub_left x |>.const_mul M).mono' ?_
    (Eventually.of_forall fun y => ?_)
  · exact (hbm.smul ((inhom_ghi_measurable hd hs0 hsd).comp
      (measurable_const.sub measurable_id))).aestronglyMeasurable
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hM y) (norm_nonneg _)

lemma inhom_conv_schwartz (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ c : ℂ, ∀ (i : Fin d) (ψ : SchwartzMap (Euc d) ℂ) (b : Euc d → ℝ),
      (∀ x, ψ x = ((b x : ℝ) : ℂ)) →
      ∃ Θ : SchwartzMap (Euc d) ℂ,
        (∀ x, ((inhom_conv (ghiForce s) b x i : ℝ) : ℂ) = Θ x) ∧
        ∀ ξ, 𝓕 (⇑Θ) ξ = inhom_M d s c i ξ * 𝓕 (⇑ψ) ξ := by
  obtain ⟨c, hc⟩ := inhom_ghi_conv hd hs0 hsd
  refine ⟨c, fun i ψ b hψ => ?_⟩
  obtain ⟨hFi, -, hΘ⟩ := hc i
  obtain ⟨Θ, hΘx, hΘF⟩ := hΘ ψ
  refine ⟨Θ, fun x => ?_, hΘF⟩
  obtain ⟨hbc, -, ⟨M, hM⟩, -, -⟩ := inhom_schw_props hψ
  have hint := inhom_conv_integrable hd hs0 hsd hbc.measurable hM x
  rw [inhom_conv_comp x i hint, hΘx x, ← integral_complex_ofReal]
  have := integral_sub_left_eq_self (fun y : Euc d => ((ghiForce s y i : ℝ) : ℂ) * ψ (x - y))
    volume x
  simp only [sub_sub_cancel] at this
  rw [← this]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [hψ]
  push_cast
  ring

lemma inhom_M_gL (c : ℂ) (i : Fin d) (ξ : Euc d) :
    inhom_M d s c i ξ * cmxFB_gL d (1 / 16) ξ = 0 := by
  unfold inhom_M cmxFB_gL
  by_cases hξ : ‖ξ‖ ≤ 1
  · rw [cmxFB_chi_one hξ]; simp
  · push Not at hξ
    have : chi ((1 / 16 : ℝ)⁻¹ • ξ) = 0 := by
      apply cmxFB_chi_zero
      rw [norm_smul, norm_inv, Real.norm_of_nonneg (by norm_num)]
      linarith
    rw [this]; simp

/-- `∇g_{>1} * a₀ = 0` for the low-frequency part. -/
lemma inhom_conv_ghi_zero (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2)
    {φ φ₀ : SchwartzMap (Euc d) ℂ} {a₀ : Euc d → ℝ} (hφ₀ : ∀ x, φ₀ x = ((a₀ x : ℝ) : ℂ))
    (hF : ∀ ξ, 𝓕 (⇑φ₀) ξ = cmxFB_gL d (1 / 16) ξ * 𝓕 (⇑φ) ξ) (x : Euc d) :
    inhom_conv (ghiForce s) a₀ x = 0 := by
  obtain ⟨c, hc⟩ := inhom_conv_schwartz hd hs0 hsd (s := s)
  ext i
  obtain ⟨Θ, hΘx, hΘF⟩ := hc i φ₀ a₀ hφ₀
  have h0 : ∀ ξ, 𝓕 (⇑Θ) ξ = 0 := by
    intro ξ
    rw [hΘF ξ, hF ξ]
    calc inhom_M d s c i ξ * (cmxFB_gL d (1 / 16) ξ * 𝓕 (⇑φ) ξ)
        = (inhom_M d s c i ξ * cmxFB_gL d (1 / 16) ξ) * 𝓕 (⇑φ) ξ := by ring
      _ = 0 := by rw [inhom_M_gL, zero_mul]
  have hΘ0 : Θ = 0 := by
    have h1 : (𝓕 Θ : SchwartzMap (Euc d) ℂ) = 0 := by
      ext ξ
      have := h0 ξ
      rw [SchwartzMap.fourier_coe] at *
      simpa using this
    have h2 : (𝓕⁻ (𝓕 Θ) : SchwartzMap (Euc d) ℂ) = Θ := FourierTransform.fourierInv_fourier_eq Θ
    rw [← h2, h1]
    simp
  have := hΘx x
  rw [hΘ0] at this
  simpa using this

end HRS.Commutator.Whole
