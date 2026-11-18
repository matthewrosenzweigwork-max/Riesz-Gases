import HRS.Commutator.Whole.XBBAux9

/-!
# Packet XBB, part 10: the `L^p` bound for the band chain and the band kernel

`xbb_band_chain`: Riesz transform, HLS and Young's inequality for `g = ∂_aΛ^{-α}P_band w_k`.
`xbbPhi`: the Schwartz kernel of `∂_aΛ^{-α}P_band`; `xbb_cv_holder`: Hölder bound for convolutions.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section
namespace HRS.Commutator.Whole.XBB
open HRS.Commutator.Whole HRS.Commutator.Whole.XLI HRS.Commutator.Whole.XNRS
variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- Schwartz function with prescribed smooth compactly supported symbol, as a multiplier -/
def xbbMul {θ : 𝔼 → ℂ} (hθ : ContDiff ℝ ∞ θ) (hcs : HasCompactSupport θ) (φ : 𝓢(𝔼, ℂ)) : 𝓢(𝔼, ℂ) :=
  mulS θ (hcs.hasTemperateGrowth hθ) φ

lemma fourier_xbbMul {θ : 𝔼 → ℂ} (hθ : ContDiff ℝ ∞ θ) (hcs : HasCompactSupport θ) (φ : 𝓢(𝔼, ℂ)) (ξ : 𝔼) :
    𝓕 (⇑(xbbMul hθ hcs φ)) ξ = θ ξ * 𝓕 (⇑φ) ξ := by
  unfold xbbMul; rw [fourier_mulS]

lemma xbb_fourier_sub (f g : 𝓢(𝔼, ℂ)) (ξ : 𝔼) : 𝓕 (⇑(f - g)) ξ = 𝓕 (⇑f) ξ - 𝓕 (⇑g) ξ := by
  have h : (𝓕 (f - g) : 𝓢(𝔼, ℂ)) = 𝓕 f - 𝓕 g := by
    have := (SchwartzMap.fourierTransformCLM ℂ (E := ℂ) (V := 𝔼)).map_sub f g
    simpa only [SchwartzMap.fourierTransformCLM_apply] using this
  rw [← SchwartzMap.fourier_coe, h, SchwartzMap.sub_apply, SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]

/-- the `L^p` bound for the band chain: for a band `[2^{j₀}, 2^{j+1}]` and any Schwartz `w_k`,
`g = ∂_aΛ^{-α} P_band w_k` has a companion `G` with `‖G‖_{d/β} ≲ ‖w_k‖_p`. -/
lemma xbb_band_chain (hd : 3 ≤ d) {β η p α : ℝ} (hβ : 0 < β) (hη : 0 ≤ η) (hp : 1 < p)
    (hrel : 1 / p - η / d = β / d) (hα : α = β + η + 1) (a : Fin d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (j j₀ : ℤ) (h : j₀ ≤ j) (wk : 𝓢(𝔼, ℂ)),
      ∃ G : 𝓢(𝔼, ℂ), XComp β (xbbMul (xbbSS_prop a α h).1 (xbbSS_prop a α h).2 wk) G ∧
        eLpNorm (⇑G) (xbbQ0 d β) volume ≤ C * eLpNorm (⇑wk) (ENNReal.ofReal p) volume := by
  obtain ⟨CH, hCH, hH⟩ := xbb_hls_chain hd hβ hη hp hrel a
  obtain ⟨A, hA, hAK⟩ := xbbK_lintegral_le d
  refine ⟨CH * (A + A), ENNReal.mul_ne_top hCH (ENNReal.add_ne_top.2 ⟨hA, hA⟩), fun j j₀ h wk => ?_⟩
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le
  set u1 : 𝓢(𝔼, ℂ) := xbbMul (xbbTheta_contDiff j j₀) (xbbTheta_cs j j₀) wk with hu1
  set R : 𝓢(𝔼, ℂ) := xbbMul (xbbSR_prop a h).1 (xbbSR_prop a h).2 wk with hR
  set G : 𝓢(𝔼, ℂ) := xbbMul (xbbSG_prop a η h).1 (xbbSG_prop a η h).2 wk with hG
  refine ⟨G, ?_, ?_⟩
  · intro ξ
    rw [hG, fourier_xbbMul, fourier_xbbMul, xbbSG_eq a hα j j₀ ξ]
    simp only [xbbPow]
    ring
  · have hr0 : 0 < (2 : ℝ) ^ j₀ := zpow_pos (by norm_num) j₀
    have hchain := hH u1 R G ((2 : ℝ) ^ j₀) ((2 : ℝ) ^ (j + 1)) hr0
      (fun ξ hξ => by
        rw [hu1, fourier_xbbMul]
        rcases hξ with hξ | hξ
        · rw [xbbTheta_zero_low h hξ.le, zero_mul]
        · rw [xbbTheta_zero_high h hξ.le, zero_mul])
      (fun ξ => by
        rw [hR, hu1, fourier_xbbMul, fourier_xbbMul]
        simp only [xbbSR]
        ring)
      (fun ξ => by
        rw [hG, hR, fourier_xbbMul, fourier_xbbMul]
        simp only [xbbSG, xbbSR, xbbPow]
        ring)
    refine hchain.trans ?_
    rw [mul_assoc]
    gcongr
    -- Young's inequality for the two dyadic low-pass kernels
    have hsub : u1 = (xbbMul (symbol_contDiff cutC_contDiff j) (symbol_cs cutC_cs j) wk) -
        (xbbMul (symbol_contDiff cutC_contDiff j₀) (symbol_cs cutC_cs j₀) wk) := by
      refine xschwartz_ext_fourier fun ξ => ?_
      rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, xbb_fourier_sub, hu1, fourier_xbbMul,
        fourier_xbbMul, fourier_xbbMul]
      simp only [xbbTheta]
      ring
    have hK1 : ∀ i : ℤ, eLpNorm (⇑(xbbMul (symbol_contDiff cutC_contDiff i) (symbol_cs cutC_cs i) wk))
        (ENNReal.ofReal p) volume ≤ A * eLpNorm (⇑wk) (ENNReal.ofReal p) volume := by
      intro i
      have e : ⇑(xbbMul (symbol_contDiff cutC_contDiff i) (symbol_cs cutC_cs i) wk) =
          cv ⇑(xbbK i) ⇑wk := by
        rw [xbbK_coe, cv_symK_eq_mulS cutC_contDiff cutC_cs wk i]
        rfl
      rw [e]
      refine (eLpNorm_cv_le (xbbK i).continuous.measurable wk.continuous.measurable hp1).trans ?_
      gcongr
      exact hAK i
    rw [hsub]
    calc eLpNorm (⇑(xbbMul (symbol_contDiff cutC_contDiff j) (symbol_cs cutC_cs j) wk -
          xbbMul (symbol_contDiff cutC_contDiff j₀) (symbol_cs cutC_cs j₀) wk)) (ENNReal.ofReal p) volume
        ≤ eLpNorm (⇑(xbbMul (symbol_contDiff cutC_contDiff j) (symbol_cs cutC_cs j) wk))
            (ENNReal.ofReal p) volume +
          eLpNorm (⇑(xbbMul (symbol_contDiff cutC_contDiff j₀) (symbol_cs cutC_cs j₀) wk))
            (ENNReal.ofReal p) volume := eLpNorm_sub_le hp1
      _ ≤ A * eLpNorm (⇑wk) (ENNReal.ofReal p) volume + A * eLpNorm (⇑wk) (ENNReal.ofReal p) volume :=
          add_le_add (hK1 j) (hK1 j₀)
      _ = _ := by ring


/-- the Schwartz kernel `Φ = 𝓕⁻[2πiξ_a (2π|ξ|)^{-α} θ]` of the band operator `∂_aΛ^{-α}P_band` -/
def xbbPhi (a : Fin d) (α : ℝ) {j j₀ : ℤ} (h : j₀ ≤ j) : 𝓢(𝔼, ℂ) :=
  𝓕⁻ ((xbbSS_prop a α h).2.toSchwartzMap (xbbSS_prop a α h).1)

lemma xbbPhi_fourier (a : Fin d) (α : ℝ) {j j₀ : ℤ} (h : j₀ ≤ j) (ξ : 𝔼) :
    𝓕 (⇑(xbbPhi a α h)) ξ = xbbSS a α j j₀ ξ := by
  have h1 : (𝓕 (𝓕⁻ ((xbbSS_prop a α h).2.toSchwartzMap (xbbSS_prop a α h).1)) : 𝓢(𝔼, ℂ)) =
      (xbbSS_prop a α h).2.toSchwartzMap (xbbSS_prop a α h).1 :=
    FourierTransform.fourier_fourierInv_eq _
  have h2 := congrFun (congrArg (⇑) h1) ξ
  rw [SchwartzMap.fourier_coe] at h2
  unfold xbbPhi
  exact h2

lemma xbbPhi_coe (a : Fin d) (α : ℝ) {j j₀ : ℤ} (h : j₀ ≤ j) :
    ⇑(xbbPhi a α h) = symK (xbbSS a α j j₀ : 𝔼 → ℂ) 0 := by
  funext x
  unfold xbbPhi symK
  rw [SchwartzMap.fourierInv_coe]
  simp only [zpow_zero, inv_one, one_smul]
  rfl

lemma xbbPhi_cv (a : Fin d) (α : ℝ) {j j₀ : ℤ} (h : j₀ ≤ j) (wk : 𝓢(𝔼, ℂ)) :
    ⇑(xbbMul (xbbSS_prop a α h).1 (xbbSS_prop a α h).2 wk) = cv ⇑(xbbPhi a α h) ⇑wk := by
  rw [xbbPhi_coe, cv_symK_eq_mulS (xbbSS_prop a α h).1 (xbbSS_prop a α h).2 wk 0]
  unfold xbbMul
  congr 1
  refine mulS_congr ?_ _ _ _
  funext ξ
  simp

/-- Hölder bound for a convolution against an `L^{q}` kernel -/
lemma xbb_cv_holder {Φ h : 𝔼 → ℂ} (hΦ : Measurable Φ) (hh : Measurable h) {p q : ℝ}
    (hpq : p.HolderConjugate q) (x : 𝔼) :
    ‖cv Φ h x‖ₑ ≤ eLpNorm Φ (ENNReal.ofReal q) volume * eLpNorm h (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  refine (enorm_cv_le Φ h x).trans ?_
  have hh' : Measurable (fun y => ‖h (x - y)‖ₑ) :=
    (hh.comp (measurable_const.sub measurable_id)).enorm
  have := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq.symm (f := fun y => ‖Φ y‖ₑ)
    (g := fun y => ‖h (x - y)‖ₑ) hΦ.enorm.aemeasurable hh'.aemeasurable
  refine this.trans (le_of_eq ?_)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp [hq0]) ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp [hp0]) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq0.le, ENNReal.toReal_ofReal hp0.le]
  congr 2
  have : ∫⁻ y, ‖h (x - y)‖ₑ ^ p = ∫⁻ y, ‖h y‖ₑ ^ p := by
    simpa using lintegral_sub_left_eq_self (fun y : 𝔼 => ‖h y‖ₑ ^ p) x
  exact this
  all_goals first | exact hΦ.aestronglyMeasurable | exact hh.aestronglyMeasurable

end HRS.Commutator.Whole.XBB
