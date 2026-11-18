import HRS.Commutator.Whole.XBBAux11

/-!
# Packet XBB, part 12: the band part `(K_j - K_{j₀}) ⋆ ∂_a v_c` (T2)

Schwartz approximants `w_k → w_c` in `L^p`; the Kato–Ponce pair estimate for `g_k = ∂_aΛ^{-α}P_band w_k`
with companion `G_k = Λ^{-η}R_a P_band w_k` (Riesz + HLS + Young), then Fatou in `k`.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section
namespace HRS.Commutator.Whole.XBB
open HRS.Commutator.Whole HRS.Commutator.Whole.XLI HRS.Commutator.Whole.XNRS
variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma xbb_kernel_diff_le {A : ℝ≥0∞} (hA : A ≠ ⊤) (hAK : ∀ j : ℤ, ∫⁻ y : 𝔼, ‖xbbK j y‖ₑ ≤ A) (j j₀ : ℤ) :
    ∫⁻ y : 𝔼, ‖(xbbK j - xbbK j₀ : 𝓢(𝔼, ℂ)) y‖ₑ ≤ ENNReal.ofReal (2 * A.toReal) := by
  have hAr : ENNReal.ofReal A.toReal = A := ENNReal.ofReal_toReal hA
  calc ∫⁻ y : 𝔼, ‖(xbbK j - xbbK j₀ : 𝓢(𝔼, ℂ)) y‖ₑ ≤ ∫⁻ y : 𝔼, (‖xbbK j y‖ₑ + ‖xbbK j₀ y‖ₑ) := by
        refine lintegral_mono fun y => ?_
        rw [SchwartzMap.sub_apply]
        exact enorm_sub_le
    _ = (∫⁻ y : 𝔼, ‖xbbK j y‖ₑ) + ∫⁻ y : 𝔼, ‖xbbK j₀ y‖ₑ :=
        lintegral_add_left (xbbK j).continuous.measurable.enorm _
    _ ≤ A + A := add_le_add (hAK j) (hAK j₀)
    _ = ENNReal.ofReal (2 * A.toReal) := by
        rw [ENNReal.ofReal_mul (by norm_num), hAr]; simp [two_mul]


lemma xbbN_ne_top {β : ℝ} (hβ : 0 ≤ β) (Γ : 𝓢(𝔼, ℂ)) : xbbN β ⇑Γ ≠ ⊤ := by
  unfold xbbN
  rw [xbbQ_eq_ofReal_xhom hβ]
  exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top

/-- **T2**: the band part `(K_j - K_{j₀}) ⋆ ∂_a v_c` satisfies the Kato–Ponce estimate against `Γ`. -/
lemma xbb_T2 (hd : 3 ≤ d) {β η p α : ℝ} (hβ : 0 < β) (hη : 0 ≤ η) (hp : 1 < p)
    (hrel : 1 / p - η / d = β / d) (hα : α = β + η + 1) (hβd : 2 * β < d) (a : Fin d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (c : Fin d) {v : 𝔼 → 𝔼}, XTVF v → ∀ {L F : ℝ}, 0 ≤ L → 0 ≤ F →
      (∀ z, |xw v a c z| ≤ L) → ∀ {wc : 𝔼 → ℝ}, Measurable wc →
      eLpNorm (fun z => ((wc z : ℝ) : ℂ)) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal F →
      HRS.Whole.IsFracDerivRep α (fun x => v x c) wc →
      ∀ (j₀ j : ℤ), j₀ ≤ j → ∀ (Γ GΓ : 𝓢(𝔼, ℂ)), XComp β Γ GΓ →
        (∀ ξ : 𝔼, ‖ξ‖ < (2 : ℝ) ^ j₀ → 𝓕 (⇑Γ) ξ = 0) →
        xbbN β (fun x => cv ⇑(xbbK j - xbbK j₀ : 𝓢(𝔼, ℂ)) (fun z => ((xw v a c z : ℝ) : ℂ)) x * Γ x) ≤
          C * (ENNReal.ofReal F + ENNReal.ofReal L) * xbbN β ⇑Γ := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  obtain ⟨CP, hCP, hP⟩ := xbb_pair_high_scaled hd hβ hβd
  obtain ⟨Cch, hCch, hch⟩ := xbb_band_chain hd hβ hη hp hrel hα a
  obtain ⟨A, hA, hAK⟩ := xbbK_lintegral_le d
  obtain ⟨Cs, hCs, hS⟩ := xbb_sobolev hd1 hβ hβd
  refine ⟨CP * (Cch * ENNReal.ofReal Cs + (A + A)), ?_, ?_⟩
  · exact ENNReal.mul_ne_top hCP (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hCch ENNReal.ofReal_ne_top,
      ENNReal.add_ne_top.2 ⟨hA, hA⟩⟩)
  intro c v hv L F hL hF hb wc hwm hwp hrep j₀ j hj Γ GΓ hGΓ hΓ
  have hα0 : 0 < α := by rw [hα]; linarith
  set Wc : 𝔼 → ℂ := fun z => ((xw v a c z : ℝ) : ℂ) with hWc
  set fc : 𝔼 → ℂ := fun z => ((wc z : ℝ) : ℂ) with hfc
  have hbW : ∀ z, ‖Wc z‖ ≤ L := fun z => by
    simp only [hWc, Complex.norm_real, Real.norm_eq_abs]; exact hb z
  set ϖ : 𝓢(𝔼, ℂ) := xbbK j - xbbK j₀ with hϖ
  set Φ : 𝓢(𝔼, ℂ) := xbbPhi a α hj with hΦ
  -- the identification `ϖ ⋆ ∂_a v_c = Φ ⋆ w_c`
  have hΦF : ∀ ξ : 𝔼, 𝓕 (⇑Φ) ξ = (2 * Real.pi * Complex.I * ((ξ a : ℝ) : ℂ)) *
      (((2 * Real.pi * ‖ξ‖) ^ (-α) : ℝ) : ℂ) * 𝓕 (⇑ϖ) ξ := by
    intro ξ
    have h1 : 𝓕 (⇑ϖ) ξ = xbbTheta j j₀ ξ := by
      rw [hϖ, xbb_fourier_sub, fourier_xbbK, fourier_xbbK]; rfl
    rw [hΦ, xbbPhi_fourier, h1]
    unfold xbbSS xbbPow
    ring
  have hident : ∀ x, cv ⇑ϖ Wc x = cv ⇑Φ fc x := by
    intro x
    rw [xbb_cv_eq_int, xbb_cv_eq_int]
    exact xbb_ident hv a c hα0 hrep ϖ Φ hΦF x
  have hBj : ∀ x, ‖cv ⇑ϖ Wc x‖ ≤ 2 * A.toReal * L := fun x =>
    xbb_norm_cv_le ϖ.continuous.measurable hL (by positivity) (xbb_kernel_diff_le hA hAK j j₀) hbW x
  -- approximants
  have hfcm : Measurable fc := Complex.measurable_ofReal.comp hwm
  have hMemLp : MemLp fc (ENNReal.ofReal p) volume := lt_of_le_of_lt hwp ENNReal.ofReal_lt_top
  obtain ⟨wk, hwk⟩ := xbb_approx_wc hp hMemLp
  set δ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hδ
  have hδ0 : ∀ k, 0 ≤ δ k := fun k => by simp only [hδ]; positivity
  have hδ1 : ∀ k, δ k ≤ 1 := fun k => by
    simp only [hδ]
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hwkF : ∀ k, eLpNorm (⇑(wk k)) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal F + ENNReal.ofReal (δ k) :=
    fun k => xbb_wk_norm hp hwp (wk k) (hwk k)
  choose Gk hGk using fun k => hch j j₀ hj (wk k)
  set gk : ℕ → 𝓢(𝔼, ℂ) := fun k => xbbMul (xbbSS_prop a α hj).1 (xbbSS_prop a α hj).2 (wk k) with hgk
  set cΦ : ℝ := (eLpNorm (⇑Φ) (ENNReal.ofReal p.conjExponent) volume).toReal with hcΦ
  have hcΦ0 : 0 ≤ cΦ := ENNReal.toReal_nonneg
  have hgkcv : ∀ k x, gk k x = cv ⇑Φ ⇑(wk k) x := fun k x => congrFun (xbbPhi_cv a α hj (wk k)) x
  have hgkB : ∀ k x, ‖gk k x - cv ⇑ϖ Wc x‖ ≤ cΦ * δ k := by
    intro k x
    rw [hgkcv, hident]
    exact xbb_cv_approx_bound hp hfcm hMemLp (wk k) (hδ0 k) (hwk k) x
  have hgkbound : ∀ k x, ‖gk k x‖ ≤ 2 * A.toReal * L + cΦ * δ k := by
    intro k x
    calc ‖gk k x‖ = ‖(gk k x - cv ⇑ϖ Wc x) + cv ⇑ϖ Wc x‖ := by rw [sub_add_cancel]
      _ ≤ ‖gk k x - cv ⇑ϖ Wc x‖ + ‖cv ⇑ϖ Wc x‖ := norm_add_le _ _
      _ ≤ cΦ * δ k + 2 * A.toReal * L := add_le_add (hgkB k x) (hBj x)
      _ = _ := by ring
  -- the pair estimate for each approximant
  have hμ : 0 < (2 : ℝ) ^ (j₀ - 1) := zpow_pos (by norm_num) _
  have hμ2 : (2 : ℝ) * (2 : ℝ) ^ (j₀ - 1) = (2 : ℝ) ^ j₀ := by
    rw [zpow_sub₀ (by norm_num), zpow_one]; field_simp
  have hμlt : (2 : ℝ) ^ (j₀ - 1) < (2 : ℝ) ^ j₀ := by
    rw [← hμ2]; linarith
  have hgkF : ∀ k, ∀ ξ : 𝔼, ‖ξ‖ < 2 * (2 : ℝ) ^ (j₀ - 1) → 𝓕 (⇑(gk k)) ξ = 0 := by
    intro k ξ hξ
    rw [hμ2] at hξ
    rw [hgk, fourier_xbbMul]
    simp only [xbbSS]
    rw [xbbTheta_zero_low hj hξ.le]
    simp
  have hN1 : eLpNorm (⇑Γ) (xbbQ1 d β) volume ≤ ENNReal.ofReal Cs * xbbN β ⇑Γ := hS Γ GΓ hGΓ
  have hNΓ : xbbN β ⇑Γ ≠ ⊤ := xbbN_ne_top hβ.le Γ
  set M : ℕ → ℝ≥0∞ := fun k => CP * (Cch * (ENNReal.ofReal F + ENNReal.ofReal (δ k)) *
      (ENNReal.ofReal Cs * xbbN β ⇑Γ) + ENNReal.ofReal (2 * A.toReal * L + cΦ * δ k) * xbbN β ⇑Γ) with hM
  have hbound : ∀ k, xbbN β (fun x => gk k x * Γ x) ≤ M k := by
    intro k
    have h1 := hP ((2 : ℝ) ^ (j₀ - 1)) hμ (gk k) (Gk k) Γ (hGk k).1 (hgkF k)
      (fun ξ hξ => hΓ ξ (hξ.trans hμlt)) (2 * A.toReal * L + cΦ * δ k)
      (by have := hδ0 k; positivity) (hgkbound k)
    refine h1.trans ?_
    simp only [hM]
    gcongr
    · exact ((hGk k).2).trans (by gcongr; exact hwkF k)
  -- the limit `k → ∞` (Fatou)
  have hlimpt : ∀ x, Tendsto (fun k => gk k x) atTop (𝓝 (cv ⇑ϖ Wc x)) := by
    intro x
    refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => hgkB k x) ?_
    simpa using hδlim.const_mul cΦ
  have hFlim : ∀ ξ : 𝔼, Tendsto (fun k => 𝓕 (fun x => gk k x * Γ x) ξ) atTop
      (𝓝 (𝓕 (fun x => cv ⇑ϖ Wc x * Γ x) ξ)) := fun ξ =>
    xbb_fourier_tendsto (M := 2 * A.toReal * L + cΦ) (fun k => (gk k).continuous.aestronglyMeasurable)
      (fun k x => (hgkbound k x).trans (by
        have := mul_le_of_le_one_right hcΦ0 (hδ1 k); linarith)) hlimpt ξ
  have hMlim : Tendsto M atTop (𝓝 (CP * (Cch * (ENNReal.ofReal F + ENNReal.ofReal 0) *
      (ENNReal.ofReal Cs * xbbN β ⇑Γ) + ENNReal.ofReal (2 * A.toReal * L + cΦ * 0) * xbbN β ⇑Γ))) := by
    have h1 : Tendsto (fun k => ENNReal.ofReal (δ k)) atTop (𝓝 (ENNReal.ofReal 0)) :=
      ENNReal.tendsto_ofReal hδlim
    have h2 : Tendsto (fun k => ENNReal.ofReal (2 * A.toReal * L + cΦ * δ k)) atTop
        (𝓝 (ENNReal.ofReal (2 * A.toReal * L + cΦ * 0))) :=
      ENNReal.tendsto_ofReal (tendsto_const_nhds.add (hδlim.const_mul cΦ))
    have hCsN : ENNReal.ofReal Cs * xbbN β ⇑Γ ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hNΓ
    have h3 := ENNReal.Tendsto.const_mul (tendsto_const_nhds.add h1 :
      Tendsto (fun k => ENNReal.ofReal F + ENNReal.ofReal (δ k)) atTop (𝓝 (ENNReal.ofReal F + ENNReal.ofReal 0)))
      (Or.inr hCch)
    have h4 := ENNReal.Tendsto.mul_const h3 (Or.inr hCsN)
    have h5 := ENNReal.Tendsto.mul_const h2 (Or.inr hNΓ)
    exact ENNReal.Tendsto.const_mul (h4.add h5) (Or.inr hCP)
  have hFat := xbbN_fatou β (fun k => (prodS (gk k) Γ).integrable) hFlim hbound hMlim
  refine hFat.trans ?_
  have hAr : ENNReal.ofReal A.toReal = A := ENNReal.ofReal_toReal hA
  have hAL : ENNReal.ofReal (2 * A.toReal * L + cΦ * 0) = (A + A) * ENNReal.ofReal L := by
    rw [mul_zero, add_zero, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num), hAr]
    simp [two_mul]
  rw [hAL, ENNReal.ofReal_zero, add_zero]
  set N := xbbN β ⇑Γ
  set F' := ENNReal.ofReal F
  set L' := ENNReal.ofReal L
  set Cs' := ENNReal.ofReal Cs
  calc CP * (Cch * F' * (Cs' * N) + (A + A) * L' * N)
      ≤ CP * (Cch * F' * (Cs' * N) + (A + A) * L' * N) + CP * (Cch * Cs' * L' * N + (A + A) * F' * N) :=
        le_self_add
    _ = CP * (Cch * Cs' + (A + A)) * (F' + L') * N := by ring

end HRS.Commutator.Whole.XBB
