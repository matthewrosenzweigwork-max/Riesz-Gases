import HRS.Commutator.Whole.LocalAuxSAMP10

/-!
# The multiplier identity `u - ψ * u = K̃ * |∇|^α u` (packet CMX-SAMP, helper file 11)
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff Convolution

noncomputable section

namespace HRS.Commutator.Whole.SAMP1

open HRS HRS.Whole HRS.Commutator.Whole

variable {d : ℕ}

lemma integrable_growth_mul {u : Euc d → ℂ} (hu : AEStronglyMeasurable u volume) {A : ℝ}
    (hA : 0 ≤ A) (huA : ∀ x, ‖u x‖ ≤ A * (1 + ‖x‖)) (θ : SchwartzMap (Euc d) ℂ) :
    Integrable (fun x => u x * θ x) := by
  have hb : Integrable (fun x : Euc d => A * (‖θ x‖ + ‖x‖ ^ 1 * ‖θ x‖)) :=
    ((θ.integrable (μ := (volume : Measure (Euc d)))).norm.add
      (θ.integrable_pow_mul (volume : Measure (Euc d)) 1)).const_mul A
  refine hb.mono' (hu.mul θ.continuous.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  calc ‖u x‖ * ‖θ x‖ ≤ A * (1 + ‖x‖) * ‖θ x‖ := by gcongr; exact huA x
    _ = _ := by ring

theorem key_identity (hd : 1 ≤ d) {α : ℝ} (hα : 1 < α) {K : Euc d → ℝ} (hK : Integrable K)
    (hKF : ∀ ξ : Euc d, 𝓕 (fun x : Euc d => ((K x : ℝ) : ℂ)) ξ =
      (((1 - chi ξ) * (2 * Real.pi * ‖ξ‖) ^ (-α) : ℝ) : ℂ))
    {p : ℝ} (hp : 1 < p) {u wf : Euc d → ℝ} (huc : Continuous u) {A : ℝ}
    (hu : ∀ x, |u x| ≤ A * (1 + ‖x‖)) (hwfm : Measurable wf) (hwfp : ∫⁻ y, ‖wf y‖ₑ ^ p ≠ ⊤)
    (hrep : IsFracDerivRep α u wf) (θ : SchwartzMap (Euc d) ℂ) :
    ∫ x, ((u x - ∫ y, psiL 1 y * u (x - y) : ℝ) : ℂ) * θ x =
      ∫ x, ((∫ y, K (-(x - y)) * wf y : ℝ) : ℂ) * θ x := by
  have hA : 0 ≤ A := by have := hu 0; simp at this; exact (abs_nonneg _).trans this
  set uc : Euc d → ℂ := fun x => ((u x : ℝ) : ℂ) with huc_def
  set wfc : Euc d → ℂ := fun x => ((wf x : ℝ) : ℂ) with hwfc_def
  set Kc : Euc d → ℂ := fun x => ((K x : ℝ) : ℂ) with hKc_def
  have hucm : AEStronglyMeasurable uc volume :=
    (Complex.continuous_ofReal.comp huc).aestronglyMeasurable
  have huA : ∀ x, ‖uc x‖ ≤ A * (1 + ‖x‖) := fun x => by
    simp only [huc_def, Complex.norm_real, Real.norm_eq_abs]; exact hu x
  have hψm : AEStronglyMeasurable (fun y : Euc d => Om d y) volume := (Om d).continuous.aestronglyMeasurable
  have hψ0 : Integrable (fun y : Euc d => ‖Om d y‖) := (Om d).integrable.norm
  have hψ1 : Integrable (fun y : Euc d => ‖y‖ * ‖Om d y‖) := by
    simpa using (Om d).integrable_pow_mul (volume : Measure (Euc d)) 1
  have hθ0 : Integrable (fun x : Euc d => ‖θ x‖) := θ.integrable.norm
  have hθ1 : Integrable (fun x : Euc d => ‖x‖ * ‖θ x‖) := by
    simpa using θ.integrable_pow_mul (volume : Measure (Euc d)) 1
  -- (L2)
  have h1 := integrable_conv_growth hψm hucm θ.continuous.aestronglyMeasurable hψ0 hψ1 hA huA hθ0 hθ1
  obtain ⟨hI1, hI2, hE⟩ := pairing_conv (fun y => Om d y) uc θ h1
  have hev : ∀ x : Euc d, ∫ y, Om d y * θ (x + y) = ∫ y, Om d y * θ (x - y) := by
    intro x
    have := integral_neg_eq_self (fun y : Euc d => Om d y * θ (x - y)) volume
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [Om_apply, cmxFB_psiL_neg, sub_neg_eq_add]
  simp_rw [hev] at hI2 hE
  have hcastu : ∀ x : Euc d, ((∫ y, psiL 1 y * u (x - y) : ℝ) : ℂ) = ∫ y, Om d y * uc (x - y) := by
    intro x
    rw [cast_conv (fun y => psiL 1 y) u x]
    exact integral_congr_ae (Eventually.of_forall fun y => by simp [Om_apply, huc_def])
  have hUθ : Integrable (fun x => uc x * θ x) := integrable_growth_mul hucm hA huA θ
  -- test function S
  obtain ⟨S, hSK, hST⟩ := exists_test_S hK hKF θ
  have hL4 := (hrep S).2.2
  have hL4' : ∫ x, uc x * Tfrac α S x = ∫ x, wfc x * S x := hL4
  have hwfS : Integrable (fun x => wfc x * S x) := cmxHLS_integrable_mul_Lq hp hwfm hwfp S
  -- left side
  have eL : ∫ x, ((u x - ∫ y, psiL 1 y * u (x - y) : ℝ) : ℂ) * θ x =
      ∫ x, uc x * Tfrac α S x := by
    have e1 : ∀ x : Euc d, ((u x - ∫ y, psiL 1 y * u (x - y) : ℝ) : ℂ) * θ x =
        uc x * θ x - (∫ y, Om d y * uc (x - y)) * θ x := by
      intro x
      rw [Complex.ofReal_sub, hcastu x, sub_mul]
    simp_rw [e1]
    rw [integral_sub hUθ hI1, hE]
    have e2 : ∀ x : Euc d, uc x * Tfrac α S x =
        uc x * θ x - uc x * ∫ y, Om d y * θ (x - y) := by
      intro x; rw [hST x, mul_sub]
    simp_rw [e2]
    rw [integral_sub hUθ hI2]
  -- right side
  have hKc0 : Integrable Kc := hK.ofReal
  have hKcm : AEStronglyMeasurable Kc volume := hKc0.1
  have hwfcm : AEStronglyMeasurable wfc volume := (Complex.measurable_ofReal.comp hwfm).aestronglyMeasurable
  have hPm : MemLp wfc (ENNReal.ofReal p) volume := by
    rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ENNReal.ofReal_pos.2 (by linarith)).ne' ENNReal.ofReal_ne_top hwfcm,
      ENNReal.toReal_ofReal (by linarith)]
    simp_rw [hwfc_def, cmxHLS_enorm_ofReal]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hwfp
  haveI := holder_inst hp
  have h5 := integrable_conv_holder (P := ENNReal.ofReal p.conjExponent) (P' := ENNReal.ofReal p)
    hKcm hKc0 θ.continuous.aestronglyMeasurable hwfcm (θ.memLp _) hPm
  obtain ⟨hJ1, hJ2, hJE⟩ := pairing_conv Kc θ wfc h5
  have eR : ∫ x, wfc x * S x = ∫ x, ((∫ y, K (-(x - y)) * wf y : ℝ) : ℂ) * θ x := by
    have e1 : ∀ x : Euc d, wfc x * S x = (∫ y, Kc y * θ (x - y)) * wfc x := by
      intro x; rw [hSK x, mul_comm]
    simp_rw [e1]
    rw [hJE]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [mul_comm]
    congr 1
    have h := integral_add_left_eq_self (μ := (volume : Measure (Euc d))) (fun y : Euc d => Kc (y - x) * wfc y) x
    simp only [add_sub_cancel_left] at h
    rw [← integral_complex_ofReal]
    rw [h]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp [hKc_def, hwfc_def, neg_sub]
  rw [eL, hL4', eR]

/-- **The multiplier identity** `u - ψ * u = K̃ * |∇|^α u` (pointwise, for continuous `u`). -/
theorem scalar_identity (hd : 1 ≤ d) {α : ℝ} (hα : 1 < α) {K : Euc d → ℝ} (hK : Integrable K)
    (hKF : ∀ ξ : Euc d, 𝓕 (fun x : Euc d => ((K x : ℝ) : ℂ)) ξ =
      (((1 - chi ξ) * (2 * Real.pi * ‖ξ‖) ^ (-α) : ℝ) : ℂ))
    {p : ℝ} (hp : 1 < p)
    (hKq : MemLp (fun x : Euc d => K (-x)) (ENNReal.ofReal p.conjExponent) volume)
    {u wf : Euc d → ℝ} (huc : Continuous u) {A : ℝ}
    (hu : ∀ x, |u x| ≤ A * (1 + ‖x‖)) (hUc : Continuous fun x => u x - ∫ y, psiL 1 y * u (x - y))
    (hwm : Measurable wf) (hwp : ∫⁻ y, ‖wf y‖ₑ ^ p ≠ ⊤) (hrep : IsFracDerivRep α u wf)
    (x : Euc d) :
    u x - ∫ y, psiL 1 y * u (x - y) = ∫ y, K (-(x - y)) * wf y := by
  have hP : MemLp wf (ENNReal.ofReal p) volume := by
    rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ENNReal.ofReal_pos.2 (by linarith)).ne' ENNReal.ofReal_ne_top hwm.aestronglyMeasurable,
      ENNReal.toReal_ofReal (by linarith)]
    have hp0 : 0 < p := by linarith
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hwp
  have hGc : Continuous fun x : Euc d => ∫ y, K (-(x - y)) * wf y := by
    have := continuous_conv_Lq hp hKq hP
    simpa [smul_eq_mul] using this
  have hae : (fun x => u x - ∫ y, psiL 1 y * u (x - y)) =ᵐ[volume]
      (fun x => ∫ y, K (-(x - y)) * wf y) := by
    refine ae_eq_of_integral_contDiff_smul_eq hUc.locallyIntegrable hGc.locallyIntegrable ?_
    intro g hg hgs
    have hcs : HasCompactSupport (fun x : Euc d => ((g x : ℝ) : ℂ)) :=
      hgs.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
    have hcd : ContDiff ℝ ∞ (fun x : Euc d => ((g x : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hg
    have key := key_identity hd hα hK hKF hp huc hu hwm hwp hrep (hcs.toSchwartzMap hcd)
    simp only [HasCompactSupport.toSchwartzMap_toFun] at key
    have e1 : ∀ (F : Euc d → ℝ), ∫ x, ((F x : ℝ) : ℂ) * ((g x : ℝ) : ℂ) =
        ((∫ x, g x • F x : ℝ) : ℂ) := by
      intro F
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp [mul_comm]
    rw [e1, e1] at key
    exact_mod_cast key
  exact congrFun ((Continuous.ae_eq_iff_eq volume hUc hGc).1 hae) x

end HRS.Commutator.Whole.SAMP1
