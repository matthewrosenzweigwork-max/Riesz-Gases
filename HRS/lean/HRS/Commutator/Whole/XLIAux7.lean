import HRS.Commutator.Whole.XLIAux6

/-!
# X-LI part 7: cutoffs, dyadic kernels of smooth symbols
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- scaling of the Fourier transform -/
lemma fourier_comp_smul' (f : 𝔼 → ℂ) {c : ℝ} (hc : 0 < c) (ξ : 𝔼) :
    𝓕 (fun x => f (c • x)) ξ = ((c ^ d)⁻¹ : ℝ) • 𝓕 f (c⁻¹ • ξ) := by
  simp only [Real.fourier_eq]
  have h := MeasureTheory.Measure.integral_comp_smul (μ := (volume : Measure 𝔼))
    (fun y : 𝔼 => (𝐞 (-inner ℝ y (c⁻¹ • ξ)) : Circle) • f y) c
  have e : ∀ x : 𝔼, (fun y : 𝔼 => (𝐞 (-inner ℝ y (c⁻¹ • ξ)) : Circle) • f y) (c • x)
      = (𝐞 (-inner ℝ x ξ) : Circle) • f (c • x) := by
    intro x
    simp only [inner_smul_left, inner_smul_right, RCLike.conj_to_real]
    congr 3
    field_simp
  simp_rw [e] at h
  rw [h]
  simp [finrank_euclideanSpace, abs_of_pos, hc]

lemma schwartz_of_cs {s : 𝔼 → ℂ} (hs : ContDiff ℝ ∞ s) (hcs : HasCompactSupport s) :
    Continuous (𝓕⁻ s) ∧ Integrable (𝓕⁻ s) ∧ 𝓕 (𝓕⁻ s) = s := by
  set S : SchwartzMap 𝔼 ℂ := hcs.toSchwartzMap hs with hS
  have hSθ : (⇑S : 𝔼 → ℂ) = s := rfl
  set T : SchwartzMap 𝔼 ℂ := 𝓕⁻ S with hT
  have h1 : (⇑T : 𝔼 → ℂ) = 𝓕⁻ s := by
    rw [← hSθ]; exact SchwartzMap.fourierInv_coe S
  refine ⟨?_, ?_, ?_⟩
  · rw [← h1]; exact T.continuous
  · rw [← h1]; exact T.integrable
  · have h : (𝓕 T : SchwartzMap 𝔼 ℂ) = S := FourierTransform.fourier_fourierInv_eq S
    have h2 : (⇑(𝓕 T : SchwartzMap 𝔼 ℂ) : 𝔼 → ℂ) = 𝓕 (⇑T) := SchwartzMap.fourier_coe T
    rw [← h1, ← h2]
    exact congrArg (⇑) h

/-- scaling of the inverse Fourier transform of a dilated symbol -/
lemma fourierInv_scale (θ : 𝔼 → ℂ) {c : ℝ} (hc : 0 < c) (x : 𝔼) :
    𝓕⁻ (fun ξ => θ (c⁻¹ • ξ)) x = ((c ^ d : ℝ)) • 𝓕⁻ θ (c • x) := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_neg]
  have := fourier_comp_smul' θ (c := c⁻¹) (inv_pos.2 hc) (-x)
  rw [this]
  simp only [inv_inv, smul_neg, inv_pow, inv_inv]

/-- Schwartz decay of the kernel of a smooth compactly supported symbol -/
lemma decay_fourierInv {θ : 𝔼 → ℂ} (hθ : ContDiff ℝ ∞ θ) (hcs : HasCompactSupport θ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : 𝔼, ‖𝓕⁻ θ y‖ * (1 + ‖y‖) ^ (d + 1) ≤ M := by
  set S : SchwartzMap 𝔼 ℂ := hcs.toSchwartzMap hθ with hS
  set T : SchwartzMap 𝔼 ℂ := 𝓕⁻ S with hT
  have h1 : (⇑T : 𝔼 → ℂ) = 𝓕⁻ θ := SchwartzMap.fourierInv_coe S
  obtain ⟨C0, hC0, h0⟩ := T.decay 0 0
  obtain ⟨C1, hC1, h1'⟩ := T.decay (d + 1) 0
  refine ⟨2 ^ (d + 1) * (C0 + C1), by positivity, fun y => ?_⟩
  have e0 := h0 y
  have e1 := h1' y
  simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul] at e0 e1
  rw [← h1]
  have hb : (1 + ‖y‖) ^ (d + 1) ≤ 2 ^ (d + 1) * (1 + ‖y‖ ^ (d + 1)) := by
    rcases le_total ‖y‖ 1 with h | h
    · have : (1 + ‖y‖) ^ (d + 1) ≤ 2 ^ (d + 1) := pow_le_pow_left₀ (by positivity) (by linarith) _
      nlinarith [pow_nonneg (norm_nonneg y) (d + 1), pow_pos (by norm_num : (0:ℝ) < 2) (d + 1)]
    · have : (1 + ‖y‖) ^ (d + 1) ≤ (2 * ‖y‖) ^ (d + 1) := pow_le_pow_left₀ (by positivity) (by linarith) _
      rw [mul_pow] at this
      nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) (d + 1)]
  calc ‖T y‖ * (1 + ‖y‖) ^ (d + 1) ≤ ‖T y‖ * (2 ^ (d + 1) * (1 + ‖y‖ ^ (d + 1))) := by gcongr
    _ = 2 ^ (d + 1) * (‖T y‖ + ‖y‖ ^ (d + 1) * ‖T y‖) := by ring
    _ ≤ 2 ^ (d + 1) * (C0 + C1) := by gcongr

lemma memLp_two_of_lintegral {f : 𝔼 → ℂ} (hf : AEStronglyMeasurable f volume)
    (h : ∫⁻ x, ‖f x‖ₑ ^ 2 < ⊤) : MemLp f 2 volume := by
  have hlt : eLpNorm f 2 volume < ⊤ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
    simp only [ENNReal.toReal_ofNat]
    have : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) = ∫⁻ x, ‖f x‖ₑ ^ 2 := by
      refine lintegral_congr fun x => ?_
      rw [ENNReal.rpow_two]
    rw [this]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) h.ne
  exact hlt

/-! ### Dyadic kernels of symbols -/

/-- the dyadic kernel with symbol `θ(2^{-j} ·)` -/
def symK (θ : 𝔼 → ℂ) (j : ℤ) : 𝔼 → ℂ := 𝓕⁻ (fun ξ => θ (((2 : ℝ) ^ j)⁻¹ • ξ))

lemma symK_eq (θ : 𝔼 → ℂ) (j : ℤ) (x : 𝔼) :
    symK θ j x = ((((2 : ℝ) ^ j) ^ d : ℝ)) • 𝓕⁻ θ (((2 : ℝ) ^ j) • x) :=
  fourierInv_scale θ (zpow_pos (by norm_num) j) x

lemma symbol_contDiff {θ : 𝔼 → ℂ} (hθ : ContDiff ℝ ∞ θ) (j : ℤ) :
    ContDiff ℝ ∞ (fun ξ : 𝔼 => θ (((2 : ℝ) ^ j)⁻¹ • ξ)) :=
  hθ.comp (contDiff_const_smul _)

lemma symbol_cs {θ : 𝔼 → ℂ} (hcs : HasCompactSupport θ) (j : ℤ) :
    HasCompactSupport (fun ξ : 𝔼 => θ (((2 : ℝ) ^ j)⁻¹ • ξ)) := by
  have hc : ((2 : ℝ) ^ j)⁻¹ ≠ 0 := inv_ne_zero (zpow_ne_zero _ (by norm_num))
  exact hcs.comp_isClosedEmbedding (Homeomorph.smulOfNeZero ((2 : ℝ) ^ j)⁻¹ hc).isClosedEmbedding

lemma symK_fourier {θ : 𝔼 → ℂ} (hθ : ContDiff ℝ ∞ θ) (hcs : HasCompactSupport θ) (j : ℤ) (ξ : 𝔼) :
    𝓕 (symK θ j) ξ = θ (((2 : ℝ) ^ j)⁻¹ • ξ) := by
  have := (schwartz_of_cs (symbol_contDiff hθ j) (symbol_cs hcs j)).2.2
  unfold symK
  rw [this]

lemma symK_continuous {θ : 𝔼 → ℂ} (hθ : ContDiff ℝ ∞ θ) (hcs : HasCompactSupport θ) (j : ℤ) :
    Continuous (symK θ j) :=
  (schwartz_of_cs (symbol_contDiff hθ j) (symbol_cs hcs j)).1

lemma symK_integrable {θ : 𝔼 → ℂ} (hθ : ContDiff ℝ ∞ θ) (hcs : HasCompactSupport θ) (j : ℤ) :
    Integrable (symK θ j) :=
  (schwartz_of_cs (symbol_contDiff hθ j) (symbol_cs hcs j)).2.1

lemma symK_dec {θ : 𝔼 → ℂ} (hθ : ContDiff ℝ ∞ θ) (hcs : HasCompactSupport θ) :
    ∃ A : ℝ≥0∞, A ≠ ⊤ ∧ ∀ j, DecK A j (symK θ j) := by
  obtain ⟨M, hM0, hM⟩ := decay_fourierInv hθ hcs
  refine ⟨ENNReal.ofReal M, ENNReal.ofReal_ne_top, fun j x => ?_⟩
  have hs0 : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hn : ‖((2 : ℝ) ^ j) • x‖ = (2 : ℝ) ^ j * ‖x‖ := by
    rw [norm_smul, Real.norm_of_nonneg hs0.le]
  have h1 := hM (((2 : ℝ) ^ j) • x)
  rw [hn] at h1
  have hpos : 0 < (1 + (2 : ℝ) ^ j * ‖x‖) ^ (d + 1) := by positivity
  have h2 : ‖𝓕⁻ θ (((2 : ℝ) ^ j) • x)‖ ≤ M * ((1 + (2 : ℝ) ^ j * ‖x‖) ^ (d + 1))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]; exact h1
  have h3 : ‖symK θ j x‖ ≤ M * (((2 : ℝ) ^ j) ^ d * ((1 + (2 : ℝ) ^ j * ‖x‖) ^ (d + 1))⁻¹) := by
    rw [symK_eq, norm_smul, Real.norm_of_nonneg (by positivity)]
    calc ((2 : ℝ) ^ j) ^ d * ‖𝓕⁻ θ (((2 : ℝ) ^ j) • x)‖
        ≤ ((2 : ℝ) ^ j) ^ d * (M * ((1 + (2 : ℝ) ^ j * ‖x‖) ^ (d + 1))⁻¹) := by gcongr
      _ = _ := by ring
  rw [← ofReal_norm]
  unfold Phi
  rw [← ENNReal.ofReal_mul hM0]
  exact ENNReal.ofReal_le_ofReal h3

/-- crude `L²` bound for a convolution with a dominated kernel -/
lemma lintegral_cv_sq_le {A : ℝ≥0∞} {j : ℤ} {K u : 𝔼 → ℂ} (hK : DecK A j K) (hKm : Measurable K)
    (hu : Measurable u) :
    ∫⁻ x, ‖cv K u x‖ₑ ^ 2 ≤ (A * KP d) * (A * KP d) * ∫⁻ x, ‖u x‖ₑ ^ 2 := by
  have hH : Measurable (fun y => ‖u y‖ₑ ^ 2) := hu.enorm.pow_const 2
  calc ∫⁻ x, ‖cv K u x‖ₑ ^ 2 ≤ ∫⁻ x, (A * KP d) * (A * CvP j (fun y => ‖u y‖ₑ ^ 2) x) :=
        lintegral_mono fun x => enorm_cv_sq_le hK hKm hu x
    _ = (A * KP d) * (A * ∫⁻ x, CvP j (fun y => ‖u y‖ₑ ^ 2) x) := by
        rw [lintegral_const_mul _ ((CvP_measurable j hH).const_mul _),
          lintegral_const_mul _ (CvP_measurable j hH)]
    _ ≤ (A * KP d) * (A * (KP d * ∫⁻ x, ‖u x‖ₑ ^ 2)) := by
        refine mul_le_mul_right (mul_le_mul_right ?_ _) _
        have h1 := lintegral_CvP_mul j (H := fun y => ‖u y‖ₑ ^ 2) (w := fun _ => (1 : ℝ≥0∞)) hH
          measurable_const
        simp only [mul_one] at h1
        rw [h1]
        calc ∫⁻ z, ‖u z‖ₑ ^ 2 * CvP j (fun _ => (1 : ℝ≥0∞)) z ≤ ∫⁻ z, ‖u z‖ₑ ^ 2 * KP d :=
              lintegral_mono fun z => mul_le_mul_right (CvP_one_le j z) _
          _ = _ := by rw [lintegral_mul_const _ hH, mul_comm]
    _ = _ := by ring

/-- the orthogonality property of a family of kernels with symbols `θ(2^{-j}·)` -/
lemma symK_orth {θ : 𝔼 → ℂ} (hθ : ContDiff ℝ ∞ θ) (hcs : HasCompactSupport θ) {A : ℝ≥0∞}
    (hA : A ≠ ⊤) (hdec : ∀ j, DecK A j (symK θ j)) {M : ℝ≥0∞}
    (hM : ∀ ξ : 𝔼, ∑' j : ℤ, ‖θ (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ ^ 2 ≤ M) :
    ∀ u : 𝔼 → ℂ, Measurable u → Integrable u → ∫⁻ x, ‖u x‖ₑ ^ 2 < ⊤ →
      ∑' j, ∫⁻ x, ‖cv (symK θ j) u x‖ₑ ^ 2 ≤ M * ∫⁻ x, ‖u x‖ₑ ^ 2 := by
  intro u hu hui hufin
  have hu2 : MemLp u 2 volume := memLp_two_of_lintegral hu.aestronglyMeasurable hufin
  have hKm : ∀ j, Measurable (symK θ j) := fun j => (symK_continuous hθ hcs j).measurable
  have hFu : Continuous (𝓕 u) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by exact continuous_inner) hui
  have hpl : ∀ j, ∫⁻ x, ‖cv (symK θ j) u x‖ₑ ^ 2 =
      ∫⁻ ξ, ‖θ (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ ^ 2 * ‖𝓕 u ξ‖ₑ ^ 2 := by
    intro j
    have hvm : Measurable (cv (symK θ j) u) := measurable_cv (hKm j) hu
    have hvint : Integrable (cv (symK θ j) u) :=
      Integrable.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) (symK_integrable hθ hcs j) hui
    have hv2 : MemLp (cv (symK θ j) u) 2 volume := by
      refine memLp_two_of_lintegral hvm.aestronglyMeasurable ?_
      refine lt_of_le_of_lt (lintegral_cv_sq_le (hdec j) (hKm j) hu) ?_
      exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top hA.lt_top KP_ne_top.lt_top)
        (ENNReal.mul_lt_top hA.lt_top KP_ne_top.lt_top)) hufin
    rw [← plancherel_L1L2 hvint hv2]
    refine lintegral_congr fun ξ => ?_
    have := Real.fourier_mul_convolution_eq (symK_integrable hθ hcs j) hui ξ
    rw [show cv (symK θ j) u = (symK θ j ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] u) from rfl, this,
      symK_fourier hθ hcs, enorm_mul, mul_pow]
  calc ∑' j : ℤ, ∫⁻ x, ‖cv (symK θ j) u x‖ₑ ^ 2
      = ∑' j : ℤ, ∫⁻ ξ, ‖θ (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ ^ 2 * ‖𝓕 u ξ‖ₑ ^ 2 := tsum_congr hpl
    _ = ∫⁻ ξ, ∑' j : ℤ, ‖θ (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ ^ 2 * ‖𝓕 u ξ‖ₑ ^ 2 := by
        rw [lintegral_tsum]
        intro j
        exact (((hθ.continuous.comp (continuous_const_smul _)).measurable.enorm.pow_const 2).mul
          (hFu.measurable.enorm.pow_const 2)).aemeasurable
    _ ≤ ∫⁻ ξ, M * ‖𝓕 u ξ‖ₑ ^ 2 := by
        refine lintegral_mono fun ξ => ?_
        rw [ENNReal.tsum_mul_right]
        exact mul_le_mul_left (hM ξ) _
    _ = M * ∫⁻ ξ, ‖𝓕 u ξ‖ₑ ^ 2 := lintegral_const_mul _ (hFu.measurable.enorm.pow_const 2)
    _ = M * ∫⁻ x, ‖u x‖ₑ ^ 2 := by rw [plancherel_L1L2 hui hu2]

lemma symK_bdd {θ : 𝔼 → ℂ} (hθ : ContDiff ℝ ∞ θ) (hcs : HasCompactSupport θ) (j : ℤ) :
    ∃ B : ℝ, ∀ x, ‖symK θ j x‖ ≤ B := by
  obtain ⟨M, hM0, hM⟩ := decay_fourierInv hθ hcs
  refine ⟨((2 : ℝ) ^ j) ^ d * M, fun x => ?_⟩
  rw [symK_eq, norm_smul, Real.norm_of_nonneg (by positivity)]
  have := hM (((2 : ℝ) ^ j) • x)
  have h1 : ‖𝓕⁻ θ (((2 : ℝ) ^ j) • x)‖ ≤ M := by
    calc ‖𝓕⁻ θ (((2 : ℝ) ^ j) • x)‖ = ‖𝓕⁻ θ (((2 : ℝ) ^ j) • x)‖ * 1 := by ring
      _ ≤ ‖𝓕⁻ θ (((2 : ℝ) ^ j) • x)‖ * (1 + ‖((2 : ℝ) ^ j) • x‖) ^ (d + 1) := by
          gcongr; exact one_le_pow₀ (by linarith [norm_nonneg (((2 : ℝ) ^ j) • x)])
      _ ≤ M := this
  gcongr

/-- the convolution of two dyadic kernels is the dyadic kernel of the product symbol -/
lemma symK_conv {θ θ' : 𝔼 → ℂ} (hθ : ContDiff ℝ ∞ θ) (hcs : HasCompactSupport θ)
    (hθ' : ContDiff ℝ ∞ θ') (hcs' : HasCompactSupport θ') (j : ℤ) :
    cv (symK θ j) (symK θ' j) = symK (fun ξ => θ ξ * θ' ξ) j := by
  have hψ : ContDiff ℝ ∞ (fun ξ => θ ξ * θ' ξ) := hθ.mul hθ'
  have hψc : HasCompactSupport (fun ξ => θ ξ * θ' ξ) := hcs.mul_right
  funext x
  set C := cv (symK θ j) (symK θ' j) with hC
  have hCi : Integrable C :=
    Integrable.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) (symK_integrable hθ hcs j)
      (symK_integrable hθ' hcs' j)
  have hF : 𝓕 C = fun ξ => (fun ξ => θ ξ * θ' ξ) (((2 : ℝ) ^ j)⁻¹ • ξ) := by
    funext ξ
    have := Real.fourier_mul_convolution_eq (symK_integrable hθ hcs j) (symK_integrable hθ' hcs' j) ξ
    rw [hC]
    show 𝓕 (symK θ j ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] symK θ' j) ξ = _
    rw [this, symK_fourier hθ hcs, symK_fourier hθ' hcs']
  have hFint : Integrable (𝓕 C) := by
    rw [hF]
    exact (symbol_contDiff hψ j).continuous.integrable_of_hasCompactSupport (symbol_cs hψc j)
  obtain ⟨B, hB⟩ := symK_bdd hθ' hcs' j
  have hcont : Continuous C := by
    refine BddAbove.continuous_convolution_right_of_integrable (ContinuousLinearMap.mul ℂ ℂ)
      ?_ (symK_integrable hθ hcs j) (symK_continuous hθ' hcs' j)
    exact ⟨B, by rintro _ ⟨y, rfl⟩; exact hB y⟩
  have := Integrable.fourierInv_fourier_eq hCi hFint hcont.continuousAt (v := x)
  rw [hF] at this
  rw [← this]
  rfl

lemma cv_assoc_bdd {L K F : 𝔼 → ℂ} (hL : Integrable L) (hK : Integrable K) (hKm : Measurable K)
    (hF : Measurable F)
    {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) (x : 𝔼) :
    cv (cv L K) F x = cv L (cv K F) x := by
  have hmulassoc : ∀ (a b c : ℂ), (ContinuousLinearMap.mul ℂ ℂ) ((ContinuousLinearMap.mul ℂ ℂ) a b) c =
      (ContinuousLinearMap.mul ℂ ℂ) a ((ContinuousLinearMap.mul ℂ ℂ) b c) := fun a b c => by
    simp [mul_assoc]
  have hKF : ∀ y, ConvolutionExistsAt (fun t => ‖K t‖) (fun t => ‖F t‖) y
      (ContinuousLinearMap.mul ℝ ℝ) volume := by
    intro y
    have : Integrable (fun t => ‖K t‖ * ‖F (y - t)‖) := by
      refine Integrable.mul_bdd (c := B) hK.norm ?_ (Eventually.of_forall fun t => ?_)
      · exact (hF.comp (measurable_const.sub measurable_id)).norm.aestronglyMeasurable
      · simpa using hB (y - t)
    exact this
  refine MeasureTheory.convolution_assoc (ContinuousLinearMap.mul ℂ ℂ) (ContinuousLinearMap.mul ℂ ℂ)
    (ContinuousLinearMap.mul ℂ ℂ) (ContinuousLinearMap.mul ℂ ℂ) hmulassoc hL.aestronglyMeasurable
    hK.aestronglyMeasurable hF.aestronglyMeasurable (hL.ae_convolution_exists _ hK)
    (Eventually.of_forall hKF) ?_
  -- the remaining integrability condition
  set G : 𝔼 → ℝ := fun y => ((fun t => ‖K t‖) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
    (fun t => ‖F t‖)) y with hG
  have hGeq : ∀ y, G y = ∫ t, ‖K t‖ * ‖F (y - t)‖ := fun y => by
    simp only [hG, convolution_def]; rfl
  have hGm : Measurable G := by
    have hm : Measurable (fun p : 𝔼 × 𝔼 => ‖K p.2‖ * ‖F (p.1 - p.2)‖) :=
      (hKm.comp measurable_snd).norm.mul ((hF.comp (measurable_fst.sub measurable_snd)).norm)
    have : G = fun y => ∫ t, ‖K t‖ * ‖F (y - t)‖ := funext hGeq
    rw [this]
    exact (hm.stronglyMeasurable.integral_prod_right').measurable
  have hGb : ∀ y, ‖G y‖ ≤ (∫ t, ‖K t‖) * B := by
    intro y
    rw [hGeq, Real.norm_of_nonneg (integral_nonneg fun t => by positivity)]
    calc ∫ t, ‖K t‖ * ‖F (y - t)‖ ≤ ∫ t, ‖K t‖ * B := by
          refine integral_mono ?_ (hK.norm.mul_const B) fun t => ?_
          · refine Integrable.mul_bdd (c := B) hK.norm ?_ (Eventually.of_forall fun t => ?_)
            · exact (hF.comp (measurable_const.sub measurable_id)).norm.aestronglyMeasurable
            · simpa using hB (y - t)
          · exact mul_le_mul_of_nonneg_left (hB (y - t)) (norm_nonneg _)
      _ = _ := by rw [integral_mul_const]
  show Integrable (fun t => ((ContinuousLinearMap.mul ℝ ℝ) ‖L t‖) (G (x - t))) volume
  simp only [ContinuousLinearMap.mul_apply']
  refine Integrable.mul_bdd (c := (∫ t, ‖K t‖) * B) hL.norm ?_ (Eventually.of_forall fun t => ?_)
  · exact (hGm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  · exact hGb (x - t)

lemma symK_rep {θ θ' : 𝔼 → ℂ} (hθ : ContDiff ℝ ∞ θ) (hcs : HasCompactSupport θ)
    (hθ' : ContDiff ℝ ∞ θ') (hcs' : HasCompactSupport θ') (hrep : ∀ ξ, θ' ξ * θ ξ = θ ξ)
    {F : 𝔼 → ℂ} (hF : Measurable F) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) (j : ℤ) (x : 𝔼) :
    cv (symK θ j) F x = cv (symK θ' j) (cv (symK θ j) F) x := by
  have h1 := symK_conv hθ' hcs' hθ hcs j
  have h2 : (fun ξ => θ' ξ * θ ξ) = θ := funext hrep
  rw [h2] at h1
  rw [← cv_assoc_bdd (symK_integrable hθ' hcs' j) (symK_integrable hθ hcs j)
    (symK_continuous hθ hcs j).measurable hF hB x, h1]

/-! ### The cutoff and the dyadic annuli -/

/-- the smooth cutoff, `1` on `B(0,1)` and `0` outside `B(0,2)` -/
def cutB (d : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) := ⟨1, 2, one_pos, one_lt_two⟩

/-- the cutoff function -/
def cut {d : ℕ} (ξ : EuclideanSpace ℝ (Fin d)) : ℝ := cutB d ξ

lemma cut_contDiff : ContDiff ℝ ∞ (cut : 𝔼 → ℝ) := (cutB d).contDiff

lemma cut_one {ξ : 𝔼} (h : ‖ξ‖ ≤ 1) : cut ξ = 1 :=
  (cutB d).one_of_mem_closedBall (by simpa [cutB] using h)

lemma cut_zero {ξ : 𝔼} (h : 2 ≤ ‖ξ‖) : cut ξ = 0 :=
  (cutB d).zero_of_le_dist (by simpa [cutB, dist_zero_right] using h)

lemma cut_nonneg (ξ : 𝔼) : 0 ≤ cut ξ := (cutB d).nonneg

lemma cut_le_one (ξ : 𝔼) : cut ξ ≤ 1 := (cutB d).le_one

/-- the annulus symbol `ρ = cut - cut(2 ·)` -/
def rho (η : 𝔼) : ℂ := (((cut η - cut ((2 : ℝ) • η) : ℝ)) : ℂ)

/-- the fattened annulus symbol `ρ̃ = cut(·/2) - cut(4 ·)` (equal to `1` on the support of `ρ`) -/
def rhoT (η : 𝔼) : ℂ := (((cut ((1 / 2 : ℝ) • η) - cut ((4 : ℝ) • η) : ℝ)) : ℂ)

lemma rho_contDiff : ContDiff ℝ ∞ (rho : 𝔼 → ℂ) :=
  Complex.ofRealCLM.contDiff.comp (cut_contDiff.sub (cut_contDiff.comp (contDiff_const_smul _)))

lemma rhoT_contDiff : ContDiff ℝ ∞ (rhoT : 𝔼 → ℂ) :=
  Complex.ofRealCLM.contDiff.comp (cut_contDiff.comp (contDiff_const_smul _) |>.sub
    (cut_contDiff.comp (contDiff_const_smul _)))

lemma rho_eq_zero_of_le {η : 𝔼} (h : ‖η‖ ≤ 1 / 2) : rho η = 0 := by
  unfold rho
  rw [cut_one (by linarith), cut_one (by rw [norm_smul]; norm_num; linarith)]; simp

lemma rho_eq_zero_of_ge {η : 𝔼} (h : 2 ≤ ‖η‖) : rho η = 0 := by
  unfold rho
  rw [cut_zero h, cut_zero (by rw [norm_smul]; norm_num; linarith)]; simp

lemma rhoT_eq_zero_of_ge {η : 𝔼} (h : 4 ≤ ‖η‖) : rhoT η = 0 := by
  unfold rhoT
  rw [cut_zero (by rw [norm_smul]; norm_num; linarith), cut_zero (by rw [norm_smul]; norm_num; linarith)]
  simp

lemma rho_cs : HasCompactSupport (rho : 𝔼 → ℂ) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : 𝔼) 2) ?_
  intro η hη
  by_contra h
  exact hη (rho_eq_zero_of_ge (by
    rw [mem_closedBall_zero_iff, not_le] at h; exact h.le))

lemma rhoT_cs : HasCompactSupport (rhoT : 𝔼 → ℂ) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : 𝔼) 4) ?_
  intro η hη
  by_contra h
  exact hη (rhoT_eq_zero_of_ge (by
    rw [mem_closedBall_zero_iff, not_le] at h; exact h.le))

lemma rhoT_mul_rho (η : 𝔼) : rhoT η * rho η = rho η := by
  by_cases h1 : ‖η‖ ≤ 1 / 2
  · rw [rho_eq_zero_of_le h1]; simp
  by_cases h2 : 2 ≤ ‖η‖
  · rw [rho_eq_zero_of_ge h2]; simp
  push_neg at h1 h2
  have : rhoT η = 1 := by
    unfold rhoT
    rw [cut_one (by rw [norm_smul]; norm_num; linarith),
      cut_zero (by rw [norm_smul]; norm_num; linarith)]
    simp
  rw [this, one_mul]

lemma norm_rho_le_one (η : 𝔼) : ‖rho η‖ ≤ 1 := by
  unfold rho
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [cut_nonneg η, cut_le_one η, cut_nonneg ((2 : ℝ) • η),
    cut_le_one ((2 : ℝ) • η)]

lemma rho_sq_sum_le (ξ : 𝔼) : ∑' j : ℤ, ‖rho (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ ^ 2 ≤ 2 := by
  by_cases hξ : ξ = 0
  · subst hξ
    have : ∀ j : ℤ, ‖rho (((2 : ℝ) ^ j)⁻¹ • (0 : 𝔼))‖ₑ ^ 2 = 0 := fun j => by
      rw [smul_zero, rho_eq_zero_of_le (by simp)]; simp
    calc ∑' j : ℤ, ‖rho (((2 : ℝ) ^ j)⁻¹ • (0 : 𝔼))‖ₑ ^ 2 = ∑' j : ℤ, (0 : ℝ≥0∞) := tsum_congr this
      _ = 0 := tsum_zero
      _ ≤ 2 := zero_le
  have hξ0 : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  obtain ⟨J, hJ1, hJ2⟩ := _root_.exists_mem_Ico_zpow hξ0 (one_lt_two : (1 : ℝ) < 2)
  -- the support is contained in `{J, J+1}`
  have hsupp : ∀ j : ℤ, j ∉ ({J, J + 1} : Finset ℤ) → ‖rho (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ ^ 2 = 0 := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    have hnorm : ‖((2 : ℝ) ^ j)⁻¹ • ξ‖ = ((2 : ℝ) ^ j)⁻¹ * ‖ξ‖ := by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg (zpow_pos (by norm_num) j).le]
    have hs0 : 0 < (2 : ℝ) ^ j := zpow_pos (by norm_num) j
    suffices rho (((2 : ℝ) ^ j)⁻¹ • ξ) = 0 by rw [this]; simp
    rcases lt_or_gt_of_ne hj.1 with hlt | hgt
    · -- j < J : the scaled norm is `≥ 2`
      apply rho_eq_zero_of_ge
      rw [hnorm]
      have : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ J := zpow_le_zpow_right₀ (by norm_num) (by omega)
      rw [zpow_add₀ (by norm_num), zpow_one] at this
      rw [← div_eq_inv_mul, le_div_iff₀ hs0]
      nlinarith
    · -- j > J + 1 : the scaled norm is `≤ 1/2`
      apply rho_eq_zero_of_le
      rw [hnorm]
      have : (2 : ℝ) ^ (J + 1) * 2 ≤ (2 : ℝ) ^ j := by
        have h := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show J + 2 ≤ j by omega)
        calc (2 : ℝ) ^ (J + 1) * 2 = (2 : ℝ) ^ (J + 2) := by
              rw [zpow_add₀ (by norm_num), zpow_add₀ (by norm_num)]; norm_num; ring
          _ ≤ _ := h
      rw [← div_eq_inv_mul, div_le_iff₀ hs0]
      nlinarith
  rw [tsum_eq_sum hsupp]
  calc ∑ j ∈ ({J, J + 1} : Finset ℤ), ‖rho (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ ^ 2
      ≤ ∑ j ∈ ({J, J + 1} : Finset ℤ), (1 : ℝ≥0∞) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have : ‖rho (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ ≤ 1 := by
          calc ‖rho (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ = ENNReal.ofReal ‖rho (((2 : ℝ) ^ j)⁻¹ • ξ)‖ :=
                (ofReal_norm _).symm
            _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal (norm_rho_le_one _)
            _ = 1 := ENNReal.ofReal_one
        calc ‖rho (((2 : ℝ) ^ j)⁻¹ • ξ)‖ₑ ^ 2 ≤ 1 ^ 2 := by gcongr
          _ = 1 := by simp
    _ = 2 := by
        rw [Finset.sum_const, Finset.card_pair (by omega)]; simp

/-- the Littlewood–Paley kernels `Δ_j = 𝓕⁻[ρ(2^{-j}·)]` form a reproducing LP family -/
lemma isLPRep_rho : IsLPRep (fun j => symK (rho : 𝔼 → ℂ) j) := by
  obtain ⟨A, hA, hdec⟩ := symK_dec rho_contDiff rho_cs
  obtain ⟨A', hA', hdec'⟩ := symK_dec rhoT_contDiff rhoT_cs
  refine ⟨⟨fun j => (symK_continuous rho_contDiff rho_cs j).measurable, ⟨A, hA, hdec⟩,
    ⟨2, by simp, symK_orth rho_contDiff rho_cs hA hdec rho_sq_sum_le⟩⟩, ?_⟩
  refine ⟨fun j => symK (rhoT : 𝔼 → ℂ) j, A', hA', hdec',
    fun j => (symK_continuous rhoT_contDiff rhoT_cs j).measurable, ?_⟩
  intro F hF B hB hFB j x
  have hBr : ∀ x, ‖F x‖ ≤ B.toReal := fun x => by
    have := hFB x
    rw [← ofReal_norm] at this
    exact (ENNReal.ofReal_le_iff_le_toReal hB).1 this
  exact symK_rep rho_contDiff rho_cs rhoT_contDiff rhoT_cs rhoT_mul_rho hF hBr j x

end HRS.Commutator.Whole.XLI
