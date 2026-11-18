import HRS.Commutator.Whole.LOWVAux10

/-!
# CMX-LOWV auxiliary 11: the limit `Λ ↓ 4`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole HRS.Commutator.Whole.SAMP2

variable {d : ℕ}

theorem lowv_homSqE_eq (t : ℝ) (L : ℝ) (F : Euc d → ℂ) :
    homSqE t (lowFreq L F) = ∫⁻ ξ, ENNReal.ofReal ((2 * Real.pi * ‖ξ‖) ^ (2 * t) *
      ‖lowFreq L F ξ‖ ^ 2) := by
  unfold homSqE
  refine lintegral_congr fun ξ => ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem lowv_limit (hd : 1 ≤ d) (t : ℝ) (ht : t ≤ 0) (σ : SMeas d) (hσ : IsAdmissible σ)
    (X : ℝ≥0∞) (c0 : ℝ)
    (h : ∀ Λ : ℝ, 4 < Λ → Λ < 5 →
      X ≤ ENNReal.ofReal c0 * homSqE t (lowFreq Λ σ.fourier)) :
    X ≤ ENNReal.ofReal c0 * homSqE t (lowFreq 4 σ.fourier) := by
  obtain ⟨hp, hn⟩ := hσ.1
  haveI := hp
  haveI := hn
  have hcont : Continuous σ.fourier := (contDiff_sfourier σ hσ).continuous
  by_cases hc : ENNReal.ofReal c0 = 0
  · have := h 4.5 (by norm_num) (by norm_num)
    rw [hc, zero_mul] at this
    rw [hc, zero_mul]; exact this
  by_cases hH : homSqE t (lowFreq 4 σ.fourier) = ⊤
  · rw [hH, ENNReal.mul_top hc]; exact le_top
  -- the sequence
  set Ls : ℕ → ℝ := fun n => 4 + 1 / (2 * ((n : ℝ) + 1)) with hLs
  have hLs4 : ∀ n, 4 < Ls n := by
    intro n
    simp only [hLs]
    have : (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)) := by positivity
    linarith
  have hLs5 : ∀ n, Ls n < 5 := fun n => by
    simp only [hLs]
    have : 1 / (2 * ((n : ℝ) + 1)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    linarith
  have hLt : Tendsto Ls atTop (𝓝 4) := by
    have h1 : Tendsto (fun n : ℕ => 1 / (2 * ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 2 : ℝ)
      simp only [mul_zero] at this
      refine this.congr fun n => ?_
      field_simp
    have := h1.const_add 4
    rw [add_zero] at this
    exact this
  set w : Euc d → ℝ := fun ξ => (2 * Real.pi * ‖ξ‖) ^ (2 * t) with hw
  set Fn : ℕ → Euc d → ℝ≥0∞ := fun n ξ => ENNReal.ofReal (w ξ * ‖lowFreq (Ls n) σ.fourier ξ‖ ^ 2)
    with hFn
  set F4 : Euc d → ℝ≥0∞ := fun ξ => ENNReal.ofReal (w ξ * ‖lowFreq 4 σ.fourier ξ‖ ^ 2) with hF4
  have hFn_eq : ∀ n, homSqE t (lowFreq (Ls n) σ.fourier) = ∫⁻ ξ, Fn n ξ := fun n =>
    lowv_homSqE_eq t (Ls n) σ.fourier
  have hF4_eq : homSqE t (lowFreq 4 σ.fourier) = ∫⁻ ξ, F4 ξ := lowv_homSqE_eq t 4 σ.fourier
  have hwm : Measurable w := (measurable_const.mul measurable_norm).pow_const _
  have hlc : ∀ L : ℝ, Continuous (lowFreq L σ.fourier : Euc d → ℂ) := fun L =>
    (Complex.continuous_ofReal.comp
      (cmxFB_chi_contDiff.continuous.comp (continuous_const_smul _))).mul hcont
  have hFnm : ∀ n, Measurable (Fn n) := fun n =>
    ENNReal.measurable_ofReal.comp (hwm.mul ((hlc (Ls n)).norm.measurable.pow_const 2))
  have hF4m : Measurable F4 :=
    ENNReal.measurable_ofReal.comp (hwm.mul ((hlc 4).norm.measurable.pow_const 2))
  set m : ℝ := σ.pos.real Set.univ + σ.neg.real Set.univ with hm
  have hm0 : 0 ≤ m := by positivity
  have hσb : ∀ ξ, ‖σ.fourier ξ‖ ≤ m := fun ξ => by
    have e : σ.fourier ξ = fm σ.pos ξ - fm σ.neg ξ := rfl
    rw [e]
    exact (norm_sub_le _ _).trans (add_le_add (norm_fm_le _ _) (norm_fm_le _ _))
  set cB : ℝ := (8 * Real.pi) ^ (2 * t) * m ^ 2 with hcB
  set G : Euc d → ℝ≥0∞ := fun ξ => (closedBall (0 : Euc d) 4).indicator F4 ξ +
    (closedBall (0 : Euc d) 10).indicator (fun _ => ENNReal.ofReal cB) ξ with hG
  have hchi1 : ∀ (L : ℝ) (ξ : Euc d), 0 < L → ‖ξ‖ ≤ L → chi (L⁻¹ • ξ) = 1 := by
    intro L ξ hL hξ
    apply cmxFB_chi_one
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hL.le, inv_mul_le_iff₀ hL, mul_one]
    exact hξ
  have hchi0 : ∀ (L : ℝ) (ξ : Euc d), 0 < L → 2 * L ≤ ‖ξ‖ → chi (L⁻¹ • ξ) = 0 := by
    intro L ξ hL hξ
    apply cmxFB_chi_zero
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hL.le, inv_mul_eq_div, le_div_iff₀ hL]
    linarith
  have hbound : ∀ n, ∀ᵐ ξ ∂(volume : Measure (Euc d)), Fn n ξ ≤ G ξ := by
    intro n
    refine Eventually.of_forall fun ξ => ?_
    have hL0 : 0 < Ls n := by linarith [hLs4 n]
    by_cases h4 : ‖ξ‖ ≤ 4
    · have e1 : lowFreq (Ls n) σ.fourier ξ = lowFreq 4 σ.fourier ξ := by
        unfold lowFreq
        rw [hchi1 (Ls n) ξ hL0 (by linarith [hLs4 n]), hchi1 4 ξ (by norm_num) h4]
      have : Fn n ξ = F4 ξ := by simp only [hFn, hF4, e1]
      rw [this]
      simp only [hG]
      rw [Set.indicator_of_mem (by simpa using h4)]
      exact le_self_add
    · push Not at h4
      by_cases h2 : 2 * Ls n ≤ ‖ξ‖
      · have : lowFreq (Ls n) σ.fourier ξ = 0 := by
          unfold lowFreq; rw [hchi0 _ ξ hL0 h2]; simp
        simp only [hFn, this]
        simp
      · push Not at h2
        have hmem : ξ ∈ closedBall (0 : Euc d) 10 := by
          rw [mem_closedBall_zero_iff]; linarith [hLs5 n]
        have hwle : w ξ ≤ (8 * Real.pi) ^ (2 * t) := by
          simp only [hw]
          apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
          nlinarith [Real.pi_pos]
        have hlow : ‖lowFreq (Ls n) σ.fourier ξ‖ ≤ m := by
          unfold lowFreq
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (cmxFB_chi_nonneg _)]
          calc chi ((Ls n)⁻¹ • ξ) * ‖σ.fourier ξ‖ ≤ 1 * ‖σ.fourier ξ‖ := by
                gcongr; exact cmxFB_chi_le_one _
            _ ≤ m := by rw [one_mul]; exact hσb ξ
        have hw0 : 0 ≤ w ξ := by simp only [hw]; positivity
        have : w ξ * ‖lowFreq (Ls n) σ.fourier ξ‖ ^ 2 ≤ cB := by
          calc w ξ * ‖lowFreq (Ls n) σ.fourier ξ‖ ^ 2 ≤ (8 * Real.pi) ^ (2 * t) * m ^ 2 := by
                gcongr
            _ = cB := rfl
        simp only [hFn, hG]
        rw [Set.indicator_of_mem hmem]
        exact le_add_left (ENNReal.ofReal_le_ofReal this)
  have hGfin : ∫⁻ ξ, G ξ ≠ ⊤ := by
    simp only [hG]
    rw [lintegral_add_left (hF4m.indicator measurableSet_closedBall),
      lintegral_indicator_const measurableSet_closedBall]
    refine ENNReal.add_ne_top.2 ⟨?_, ?_⟩
    · have hle : ∫⁻ ξ, (closedBall (0 : Euc d) 4).indicator F4 ξ ≤ ∫⁻ ξ, F4 ξ :=
        lintegral_mono fun ξ => Set.indicator_le_self _ _ _
      rw [← hF4_eq] at hle
      exact ne_top_of_le_ne_top hH hle
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne
  have hlim : ∀ ξ : Euc d, Tendsto (fun n => Fn n ξ) atTop (𝓝 (F4 ξ)) := by
    intro ξ
    have h1 : Tendsto (fun n => chi ((Ls n)⁻¹ • ξ)) atTop (𝓝 (chi ((4 : ℝ)⁻¹ • ξ))) :=
      (cmxFB_chi_contDiff.continuous.tendsto _).comp ((hLt.inv₀ (by norm_num)).smul_const ξ)
    have h2 : Tendsto (fun n => lowFreq (Ls n) σ.fourier ξ) atTop (𝓝 (lowFreq 4 σ.fourier ξ)) := by
      unfold lowFreq
      exact ((Complex.continuous_ofReal.tendsto _).comp h1).mul_const _
    have h3 : Tendsto (fun n => w ξ * ‖lowFreq (Ls n) σ.fourier ξ‖ ^ 2) atTop
        (𝓝 (w ξ * ‖lowFreq 4 σ.fourier ξ‖ ^ 2)) :=
      (h2.norm.pow 2).const_mul _
    exact (ENNReal.tendsto_ofReal h3)
  have hL := tendsto_lintegral_of_dominated_convergence G hFnm hbound hGfin
    (Eventually.of_forall hlim)
  have hL' : Tendsto (fun n => homSqE t (lowFreq (Ls n) σ.fourier)) atTop
      (𝓝 (homSqE t (lowFreq 4 σ.fourier))) := by
    rw [hF4_eq]
    simp_rw [hFn_eq]
    exact hL
  exact ge_of_tendsto' (ENNReal.Tendsto.const_mul hL' (Or.inr ENNReal.ofReal_ne_top))
    fun n => h (Ls n) (hLs4 n) (hLs5 n)

end HRS.Commutator.Whole
