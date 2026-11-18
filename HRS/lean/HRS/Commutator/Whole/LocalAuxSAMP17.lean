import HRS.Commutator.Whole.LocalAuxSAMP16

/-!
# The Bessel representation of `v_{>1}` componentwise (packet CMX-SAMP, helper file 17)
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff Convolution

noncomputable section

namespace HRS.Commutator.Whole.SAMP1

open HRS HRS.Whole HRS.Commutator.Whole

variable {d : ℕ}

theorem bessel_rep_comp (hd1 : 1 ≤ d) {α : ℝ} {K k : Euc d → ℝ} (hK : Integrable K)
    (hk : Integrable k)
    (hKF : ∀ ξ : Euc d, 𝓕 (fun x : Euc d => ((K x : ℝ) : ℂ)) ξ =
      (((1 - chi ξ) * (2 * Real.pi * ‖ξ‖) ^ (-α) : ℝ) : ℂ))
    (hkF : ∀ ξ : Euc d,
      (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (α / 2) * ((1 - chi ξ) * (2 * Real.pi * ‖ξ‖) ^ (-α)) : ℝ) : ℂ) =
        (((1 - chi ξ : ℝ)) : ℂ) + 𝓕 (fun x : Euc d => ((k x : ℝ) : ℂ)) ξ)
    {p : ℝ} (hp : 1 < p) {wf V : Euc d → ℝ} (hwm : Measurable wf)
    (hwp : ∫⁻ y, ‖wf y‖ₑ ^ p ≠ ⊤) (hVc : Continuous V) {M : ℝ} (hVb : ∀ x, |V x| ≤ M)
    (hV : ∀ x, V x = ∫ y, K (-(x - y)) * wf y) :
    IsBesselRep α V (fun x => wf x - (∫ y, psiL 1 y * wf (x - y)) + ∫ y, k (-y) * wf (x - y)) := by
  intro φ
  have hp0 : 0 < p := by linarith
  set P : ℝ≥0∞ := ENNReal.ofReal p with hP
  haveI := holder_inst hp
  set Bφ : Euc d → ℂ := fun x => 𝓕⁻ (fun ξ : Euc d =>
    (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (α / 2) : ℝ) : ℂ) * 𝓕 ⇑φ ξ) x with hBφ
  have hFφ : (⇑(𝓕 φ : SchwartzMap (Euc d) ℂ) : Euc d → ℂ) = 𝓕 ⇑φ := SchwartzMap.fourier_coe φ
  obtain ⟨Sb, hSb⟩ := schwartz_bessel α (𝓕 φ : SchwartzMap (Euc d) ℂ)
  have hSb' : (⇑Sb : Euc d → ℂ) = fun ξ => (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (α / 2) : ℝ) : ℂ) *
      𝓕 ⇑φ ξ := by
    funext ξ; rw [hSb ξ, hFφ]
  set θ : SchwartzMap (Euc d) ℂ := 𝓕⁻ Sb with hθ
  have hBθ : ∀ x, Bφ x = θ x := by
    intro x
    rw [hθ, SchwartzMap.fourierInv_coe, hSb']
  have hBfun : Bφ = ⇑θ := funext hBθ
  -- complex versions
  set wc : Euc d → ℂ := fun y => ((wf y : ℝ) : ℂ) with hwc
  have hwcm : AEStronglyMeasurable wc volume := (Complex.measurable_ofReal.comp hwm).aestronglyMeasurable
  have hPm : MemLp wc P volume := by
    rw [memLp_iff, hP, eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top hwcm, ENNReal.toReal_ofReal hp0.le]
    simp_rw [hwc, cmxHLS_enorm_ofReal]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hwp
  have hφP : MemLp φ (ENNReal.ofReal p.conjExponent) volume := φ.memLp _
  have hθP : MemLp θ (ENNReal.ofReal p.conjExponent) volume := θ.memLp _
  have hKc : Integrable (fun x : Euc d => ((K x : ℝ) : ℂ)) := hK.ofReal
  have hkc : Integrable (fun x : Euc d => ((k x : ℝ) : ℂ)) := hk.ofReal
  have hKrc : Integrable (fun x : Euc d => ((K (-x) : ℝ) : ℂ)) :=
    (hK.comp_neg).ofReal
  have hΩ : Integrable (fun y : Euc d => Om d y) := (Om d).integrable
  haveI hHC : (ENNReal.ofReal p.conjExponent).HolderConjugate P := (holder_inst hp).symm
  have h_wφ : Integrable (fun x => wc x * φ x) :=
    MemLp.integrable_mul (p := P) (q := ENNReal.ofReal p.conjExponent) hPm hφP
  -- (A) the pairing for `K̃ * w`
  have hP1 := integrable_conv_holder (κ := fun y => ((K (-y) : ℝ) : ℂ)) (g := wc) (f := θ)
    hKrc.1 hKrc hwcm θ.continuous.aestronglyMeasurable (P := P)
    (P' := ENNReal.ofReal p.conjExponent) hPm hθP
  obtain ⟨hA1, hA2, hAE⟩ := pairing_conv (fun y => ((K (-y) : ℝ) : ℂ)) wc θ hP1
  have eV : ∀ x, ((V x : ℝ) : ℂ) = ∫ y, ((K (-y) : ℝ) : ℂ) * wc (x - y) := by
    intro x
    have e1 : ∫ y, ((K (-(x - y)) * wf y : ℝ) : ℂ) = ∫ z, ((K (-z) * wf (x - z) : ℝ) : ℂ) := by
      have := integral_sub_left_eq_self (μ := volume)
        (fun z : Euc d => ((K (-z) * wf (x - z) : ℝ) : ℂ)) x
      simpa [sub_sub_cancel] using this
    rw [hV x, ← integral_complex_ofReal, e1]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hwc, Complex.ofReal_mul]
  have hKθ : ∀ x, ∫ y, ((K (-y) : ℝ) : ℂ) * θ (x + y) =
      φ x - (∫ y, Om d y * φ (x - y)) + ∫ y, ((k y : ℝ) : ℂ) * φ (x - y) := by
    intro x
    have e1 := integral_neg_eq_self (fun y : Euc d => ((K y : ℝ) : ℂ) * θ (x - y)) volume
    have e2 : ∫ y, ((K (-y) : ℝ) : ℂ) * θ (x + y) = ∫ y, ((K y : ℝ) : ℂ) * θ (x - y) := by
      rw [← e1]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp [sub_neg_eq_add]
    rw [e2]
    have := K_conv_bessel hK hk hKF hkF φ x
    have hB' : ∀ t : Euc d, 𝓕⁻ (fun ξ : Euc d => (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (α / 2) : ℝ) : ℂ) *
        𝓕 ⇑φ ξ) t = θ t := hBθ
    simp only [hB'] at this
    exact this
  -- (B) the pairings for `ψ * φ` and `k * φ`
  have hP2 := integrable_conv_holder (κ := fun y => Om d y) (g := φ) (f := wc)
    (Om d).continuous.aestronglyMeasurable hΩ φ.continuous.aestronglyMeasurable hwcm
    (P := ENNReal.ofReal p.conjExponent) (P' := P) hφP hPm
  obtain ⟨hB1, hB2, hBE⟩ := pairing_conv (fun y => Om d y) φ wc hP2
  have hP3 := integrable_conv_holder (κ := fun y => ((k y : ℝ) : ℂ)) (g := φ) (f := wc)
    hkc.1 hkc φ.continuous.aestronglyMeasurable hwcm
    (P := ENNReal.ofReal p.conjExponent) (P' := P) hφP hPm
  obtain ⟨hC1, hC2, hCE⟩ := pairing_conv (fun y => ((k y : ℝ) : ℂ)) φ wc hP3
  have eΩ : ∀ x, ∫ y, Om d y * wc (x + y) = ((∫ y, psiL 1 y * wf (x - y) : ℝ) : ℂ) := by
    intro x
    have e1 := integral_neg_eq_self (fun y : Euc d => Om d y * wc (x + y)) volume
    rw [← e1, cast_conv (fun y => psiL 1 y) wf x]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp [Om_apply, cmxFB_psiL_neg, sub_eq_add_neg, hwc]
  have ek : ∀ x, ∫ y, ((k y : ℝ) : ℂ) * wc (x + y) = ((∫ y, k (-y) * wf (x - y) : ℝ) : ℂ) := by
    intro x
    have e1 := integral_neg_eq_self (fun y : Euc d => ((k y : ℝ) : ℂ) * wc (x + y)) volume
    rw [← e1, cast_conv (fun y => k (-y)) wf x]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp [sub_eq_add_neg, hwc]
  -- the pieces in the right order
  have hS2 : Integrable (fun x => wc x * ∫ y, Om d y * φ (x - y)) :=
    hB1.congr (Eventually.of_forall fun x => by simp only; ring)
  have hS3 : Integrable (fun x => wc x * ∫ y, ((k y : ℝ) : ℂ) * φ (x - y)) :=
    hC1.congr (Eventually.of_forall fun x => by simp only; ring)
  have eW : ∀ x : Euc d, ((wf x - (∫ y, psiL 1 y * wf (x - y)) + ∫ y, k (-y) * wf (x - y) : ℝ) : ℂ) *
      φ x = wc x * φ x - φ x * (∫ y, Om d y * wc (x + y)) +
        φ x * (∫ y, ((k y : ℝ) : ℂ) * wc (x + y)) := by
    intro x
    rw [Complex.ofReal_add, Complex.ofReal_sub, ← eΩ x, ← ek x]
    simp only [hwc]
    ring
  have hIW : Integrable (fun x => wc x * φ x - φ x * (∫ y, Om d y * wc (x + y)) +
      φ x * (∫ y, ((k y : ℝ) : ℂ) * wc (x + y))) := by
    have h1 : Integrable (fun x => wc x * φ x - φ x * (∫ y, Om d y * wc (x + y))) := h_wφ.sub hB2
    exact h1.add hC2
  refine ⟨?_, ?_, ?_⟩
  · -- integrability of `V * Bφ`
    show Integrable (fun x => ((V x : ℝ) : ℂ) * Bφ x)
    rw [hBfun]
    exact integrable_mul_bdd θ.integrable (Complex.continuous_ofReal.comp hVc) (M := M)
      (fun x => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hVb x)
  · -- integrability of `W * φ`
    refine hIW.congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [eW x]
  · -- the identity
    show ∫ x, ((V x : ℝ) : ℂ) * Bφ x = _
    rw [hBfun]
    simp_rw [eV]
    rw [hAE]
    have e1 : ∀ x : Euc d, wc x * ∫ y, ((K (-y) : ℝ) : ℂ) * θ (x + y) =
        wc x * φ x - wc x * (∫ y, Om d y * φ (x - y)) +
          wc x * ∫ y, ((k y : ℝ) : ℂ) * φ (x - y) := by
      intro x; rw [hKθ x]; ring
    simp_rw [e1]
    have h1 : Integrable (fun x => wc x * φ x - wc x * ∫ y, Om d y * φ (x - y)) := h_wφ.sub hS2
    rw [integral_add h1 hS3, integral_sub h_wφ hS2]
    have e2 : ∫ x, wc x * ∫ y, Om d y * φ (x - y) = ∫ x, φ x * ∫ y, Om d y * wc (x + y) := by
      rw [← hBE]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
    have e3 : ∫ x, wc x * ∫ y, ((k y : ℝ) : ℂ) * φ (x - y) =
        ∫ x, φ x * ∫ y, ((k y : ℝ) : ℂ) * wc (x + y) := by
      rw [← hCE]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
    rw [e2, e3]
    simp_rw [eW]
    have h2 : Integrable (fun x => wc x * φ x - φ x * ∫ y, Om d y * wc (x + y)) := h_wφ.sub hB2
    rw [integral_add h2 hC2, integral_sub h_wφ hB2]

end HRS.Commutator.Whole.SAMP1
