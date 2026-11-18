import HRS.Commutator.Whole.INHOMAux18
import HRS.Commutator.Whole.External

/-!
# CMX-INHOM auxiliary 19: `L²` and `L^{p₂}` norms of `a₀` and of `∇g_{>1} * a₁`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

lemma inhom_eLpNorm_two {ψ : SchwartzMap (Euc d) ℂ} {b : Euc d → ℝ}
    (hψ : ∀ x, ψ x = ((b x : ℝ) : ℂ)) :
    eLpNorm b 2 volume = (∫⁻ x, ‖ψ x‖ₑ ^ 2) ^ ((1 : ℝ) / 2) := by
  have hbc : Continuous b := (inhom_schw_props hψ).1
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) ENNReal.ofNat_ne_top
    hbc.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  have : ∀ x, ‖b x‖ₑ ^ (2 : ℝ) = ‖ψ x‖ₑ ^ 2 := by
    intro x
    rw [ENNReal.rpow_two, hψ x, ← ofReal_norm, ← ofReal_norm, Complex.norm_real]
  simp_rw [this]

lemma inhom_alpha_one (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) : 1 ≤ alphaE d s := by
  unfold alphaE; have : (3 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

lemma inhom_rpow_half_le {X Y : ℝ≥0∞} (c : ℝ) (hc : 0 ≤ c) (h : X ≤ ENNReal.ofReal c * Y) :
    X ^ ((1 : ℝ) / 2) ≤ ENNReal.ofReal (c ^ ((1 : ℝ) / 2)) * Y ^ ((1 : ℝ) / 2) := by
  calc X ^ ((1 : ℝ) / 2) ≤ (ENNReal.ofReal c * Y) ^ ((1 : ℝ) / 2) :=
        ENNReal.rpow_le_rpow h (by norm_num)
    _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg hc (by norm_num)]

lemma inhom_a0_L2 {α : ℝ} (hα : 0 < α) {φ φ₀ : SchwartzMap (Euc d) ℂ} {a₀ : Euc d → ℝ}
    (hφ₀ : ∀ x, φ₀ x = ((a₀ x : ℝ) : ℂ))
    (hF : ∀ ξ, 𝓕 (⇑φ₀) ξ = cmxFB_gL d (1 / 16) ξ * 𝓕 (⇑φ) ξ) :
    eLpNorm a₀ 2 volume ≤ ENNReal.ofReal (((1 + Real.pi ^ 2 / 16) ^ α) ^ ((1 : ℝ) / 2)) *
      inhom_Sob (-α) φ ^ ((1 : ℝ) / 2) := by
  rw [inhom_eLpNorm_two hφ₀]
  exact inhom_rpow_half_le _ (by positivity)
    (inhom_sq_le_of_symbol (m := fun ξ => cmxFB_gL d (1 / 16) ξ) hF (fun ξ => inhom_gL_sq hα ξ))

lemma inhom_M_norm_sq (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (c : ℂ) (i : Fin d)
    (ξ : Euc d) :
    ‖inhom_M d s c i ξ‖ ^ 2 ≤
      ‖c‖ ^ 2 * ((1 + 4 * Real.pi ^ 2) ^ alphaE d s *
        (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-alphaE d s)) := by
  have := inhom_w3 (inhom_alpha_one hd hs0 hsd) c i ξ
  have e : -((d : ℝ) - s) = -(2 * alphaE d s) := by unfold alphaE; ring
  unfold inhom_M cmxMY_hi
  rw [e]
  exact this

/-- `L²` bound of the components of `∇g_{>1} * a₁`. -/
lemma inhom_h_L2 (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ φ₁ : SchwartzMap (Euc d) ℂ) (a₁ : Euc d → ℝ),
      (∀ x, φ₁ x = ((a₁ x : ℝ) : ℂ)) →
      (∀ ξ, 𝓕 (⇑φ₁) ξ = (1 - cmxFB_gL d (1 / 16) ξ) * 𝓕 (⇑φ) ξ) → ∀ i : Fin d,
      eLpNorm (fun x => inhom_conv (ghiForce s) a₁ x i) 2 volume ≤
        ENNReal.ofReal C * inhom_Sob (-alphaE d s) φ ^ ((1 : ℝ) / 2) := by
  obtain ⟨c, hc⟩ := inhom_conv_schwartz hd hs0 hsd (s := s)
  refine ⟨(‖c‖ ^ 2 * (1 + 4 * Real.pi ^ 2) ^ alphaE d s) ^ ((1 : ℝ) / 2), by positivity,
    fun φ φ₁ a₁ hφ₁ hF i => ?_⟩
  obtain ⟨Θ, hΘx, hΘF⟩ := hc i φ₁ a₁ hφ₁
  rw [inhom_eLpNorm_two (ψ := Θ) (fun x => (hΘx x).symm)]
  refine inhom_rpow_half_le _ (by positivity) ?_
  refine inhom_sq_le_of_symbol (m := fun ξ => inhom_M d s c i ξ * (1 - cmxFB_gL d (1 / 16) ξ))
    (fun ξ => ?_) (fun ξ => ?_)
  · rw [hΘF ξ, hF ξ]; ring
  · rw [norm_mul, mul_pow]
    have h1 := inhom_M_norm_sq hd hs0 hsd c i ξ
    have h2 : ‖1 - cmxFB_gL d (1 / 16) ξ‖ ^ 2 ≤ 1 := by
      have := (inhom_one_sub_gL ξ).1
      nlinarith [norm_nonneg (1 - cmxFB_gL d (1 / 16) ξ)]
    have h3 : 0 ≤ (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-alphaE d s) :=
      Real.rpow_nonneg (by positivity) _
    calc ‖inhom_M d s c i ξ‖ ^ 2 * ‖1 - cmxFB_gL d (1 / 16) ξ‖ ^ 2
        ≤ ‖inhom_M d s c i ξ‖ ^ 2 * 1 := by gcongr
      _ ≤ _ := by
        rw [mul_one]
        refine h1.trans (le_of_eq ?_)
        ring

/-- Bernstein for `a₀`: `‖a₀‖_{p₂} ≲ ‖a₀‖_{L²}`. -/
lemma inhom_a0_Lp2 (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Euc d → ℝ) (a₀ : Euc d → ℝ) (φ₀ : SchwartzMap (Euc d) ℂ),
      Continuous a → (∃ M : ℝ, ∀ x, |a x| ≤ M) → (∀ x, a₀ x = Pleq (1 / 16) a x) →
      (∀ x, φ₀ x = ((a₀ x : ℝ) : ℂ)) →
      eLpNorm a₀ (ENNReal.ofReal (p2E d s)) volume ≤ ENNReal.ofReal C * eLpNorm a₀ 2 volume := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have h2le : (2 : ℝ≥0∞) ≤ ENNReal.ofReal (p2E d s) := by
    have : (2 : ℝ) ≤ p2E d s := by
      unfold p2E
      rw [le_div_iff₀ (by linarith)]
      linarith
    calc (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
      _ ≤ _ := ENNReal.ofReal_le_ofReal this
  obtain ⟨C, hC, hbern⟩ := bernstein_Lq (d := d) (by omega) (2 * (1 / 16)) (by norm_num) 2
    (ENNReal.ofReal (p2E d s)) (by norm_num) h2le
  refine ⟨C, hC, fun a a₀ φ₀ hac ⟨M, hM⟩ ha₀ hφ₀ => ?_⟩
  obtain ⟨hc0, -, -, -, ha2⟩ := inhom_schw_props hφ₀
  have hmem : MemLp a₀ 2 volume := (memLp_two_iff_integrable_sq hc0.aestronglyMeasurable).2 ha2
  have hfs : FourierSuppIn (2 * (1 / 16)) a₀ := by
    have : a₀ = Pleq (1 / 16) a := funext ha₀
    rw [this]
    exact Pleq_fourierSupp (by omega) (1 / 16) (by norm_num) a |M| (fun x => by
      have : 0 ≤ |M| := abs_nonneg _
      calc |a x| ≤ |M| := (hM x).trans (le_abs_self M)
        _ ≤ |M| * (1 + ‖x‖) := by nlinarith [norm_nonneg x]) hac.measurable
  exact (hbern a₀ hmem hfs).2

end HRS.Commutator.Whole
