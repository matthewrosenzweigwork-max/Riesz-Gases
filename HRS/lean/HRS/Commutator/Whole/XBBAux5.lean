import HRS.Commutator.Whole.XBBAux4

/-!
# Packet XBB, part 5: Riesz transform followed by the Hardy–Littlewood–Sobolev bound
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section
namespace HRS.Commutator.Whole.XBB
open HRS.Commutator.Whole HRS.Commutator.Whole.XLI HRS.Commutator.Whole.XNRS
variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma xbb_riesz (hd : 1 ≤ d) {p : ℝ} (hp : 1 < p) (a : Fin d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (u R : 𝓢(𝔼, ℂ)) (ε Rr : ℝ), 0 < ε →
      (∀ ξ : 𝔼, (‖ξ‖ < ε ∨ Rr < ‖ξ‖) → 𝓕 (⇑u) ξ = 0) →
      (∀ ξ : 𝔼, 𝓕 (⇑R) ξ = xbbRm a ξ * 𝓕 (⇑u) ξ) →
      eLpNorm (⇑R) (ENNReal.ofReal p) volume ≤ C * eLpNorm (⇑u) (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, h⟩ := xbb_riesz_lintegral hd hp a
  have hp0 : 0 < p := by linarith
  refine ⟨C ^ (1 / p), ENNReal.rpow_ne_top_of_nonneg (by positivity) hC, fun u R ε Rr hε hu hR => ?_⟩
  have hpne : ENNReal.ofReal p ≠ 0 := by simp [hp0]
  have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne hpt, eLpNorm_eq_lintegral_rpow_enorm_toReal hpne hpt,
    ENNReal.toReal_ofReal hp0.le]
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  · exact ENNReal.rpow_le_rpow (h u R ε Rr hε hu hR) (by positivity)
  all_goals first | exact R.continuous.aestronglyMeasurable | exact u.continuous.aestronglyMeasurable


lemma xbbQ0_gt_of_rel (hd : 1 ≤ d) {β η p : ℝ} (hβ : 0 < β) (hη : 0 < η) (hp : 1 < p)
    (hrel : 1 / p - η / d = β / d) : ENNReal.ofReal p < xbbQ0 d β := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  unfold xbbQ0
  rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  have h1 : β / d < 1 / p := by
    have : 0 < η / d := by positivity
    linarith
  rw [lt_div_iff₀ hβ]
  have hp0 : 0 < p := by linarith
  rw [div_lt_div_iff₀ hdR hp0] at h1
  nlinarith

/-- Riesz transform followed by the Hardy–Littlewood–Sobolev bound (`η > 0`), or the Riesz transform
alone (`η = 0`): `‖Λ^{-η} R_a u‖_{d/β} ≲ ‖u‖_p`, `1/p - η/d = β/d`. -/
lemma xbb_hls_chain (hd : 3 ≤ d) {β η p : ℝ} (hβ : 0 < β) (hη : 0 ≤ η) (hp : 1 < p)
    (hrel : 1 / p - η / d = β / d) (a : Fin d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (u R G : 𝓢(𝔼, ℂ)) (ε Rr : ℝ), 0 < ε →
      (∀ ξ : 𝔼, (‖ξ‖ < ε ∨ Rr < ‖ξ‖) → 𝓕 (⇑u) ξ = 0) →
      (∀ ξ : 𝔼, 𝓕 (⇑R) ξ = xbbRm a ξ * 𝓕 (⇑u) ξ) →
      (∀ ξ : 𝔼, 𝓕 (⇑G) ξ = (((2 * Real.pi * ‖ξ‖) ^ (-η) : ℝ) : ℂ) * 𝓕 (⇑R) ξ) →
      eLpNorm (⇑G) (xbbQ0 d β) volume ≤ C * eLpNorm (⇑u) (ENNReal.ofReal p) volume := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  obtain ⟨CR, hCR, hR⟩ := xbb_riesz hd1 hp a
  rcases hη.eq_or_lt with h0 | hpos
  · -- `η = 0`
    subst h0
    have hq : xbbQ0 d β = ENNReal.ofReal p := by
      unfold xbbQ0
      congr 1
      have : 1 / p = β / d := by simpa using hrel
      field_simp at this ⊢
      linarith
    refine ⟨CR, hCR, fun u R G ε Rr hε hu hRu hG => ?_⟩
    have hGR : G = R := by
      refine xschwartz_ext_fourier fun ξ => ?_
      rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, hG ξ]
      simp
    rw [hq, hGR]
    exact hR u R ε Rr hε hu hRu
  · -- `η > 0`
    have hlt := xbbQ0_gt_of_rel hd1 hβ hpos hp hrel
    have hq0 : (xbbQ0 d β)⁻¹ = (ENNReal.ofReal p)⁻¹ - ENNReal.ofReal (η / d) := by
      have hp0 : 0 < p := by linarith
      unfold xbbQ0
      rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_inv_of_pos hp0,
        ← ENNReal.ofReal_sub _ (by positivity)]
      congr 1
      rw [inv_div]
      rw [one_div] at hrel
      linarith
    obtain ⟨CH, hCH, hH⟩ := cmxHLS_main hd1 η (ENNReal.ofReal p) (xbbQ0 d β)
      (by rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hp) hlt
      ENNReal.ofReal_lt_top hpos hq0
    refine ⟨ENNReal.ofReal CH * CR, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCR,
      fun u R G ε Rr hε hu hRu hG => ?_⟩
    have hR0 : 𝓕 (⇑R) 0 = 0 := by
      rw [hRu 0, hu 0 (Or.inl (by simpa using hε))]; simp
    have hfrac : cmxHLS_frac η G = ⇑R := by
      funext x
      unfold cmxHLS_frac
      have e : (fun ξ : 𝔼 => (((2 * Real.pi * ‖ξ‖) ^ η : ℝ) : ℂ) * 𝓕 (⇑G) ξ) = 𝓕 (⇑R) := by
        funext ξ
        by_cases hξ : ξ = 0
        · subst hξ
          rw [hR0]
          simp [Real.zero_rpow hpos.ne']
        · have hw : 0 < 2 * Real.pi * ‖ξ‖ := by
            have := norm_pos_iff.2 hξ
            positivity
          rw [hG ξ, ← mul_assoc]
          have : (((2 * Real.pi * ‖ξ‖) ^ η : ℝ) : ℂ) * (((2 * Real.pi * ‖ξ‖) ^ (-η) : ℝ) : ℂ) = 1 := by
            rw [← Complex.ofReal_mul, ← Real.rpow_add hw]; simp
          rw [this, one_mul]
      rw [e]
      have h1 : (𝓕⁻ (𝓕 R) : 𝓢(𝔼, ℂ)) = R := FourierTransform.fourierInv_fourier_eq R
      have h2 := congrFun (congrArg (⇑) h1) x
      rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe] at h2
      exact h2
    calc eLpNorm (⇑G) (xbbQ0 d β) volume ≤ ENNReal.ofReal CH * eLpNorm (cmxHLS_frac η G) (ENNReal.ofReal p) volume :=
          hH G
      _ = ENNReal.ofReal CH * eLpNorm (⇑R) (ENNReal.ofReal p) volume := by rw [hfrac]
      _ ≤ ENNReal.ofReal CH * (CR * eLpNorm (⇑u) (ENNReal.ofReal p) volume) := by
          gcongr; exact hR u R ε Rr hε hu hRu
      _ = _ := by ring

end HRS.Commutator.Whole.XBB
