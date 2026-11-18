import HRS.MS.SobMul
import HRS.Commutator.Whole.Energy

/-!
# TC-3 (part 1): `L¹ * L²` convolution and the generic Sobolev gain

Namespace `HRS.MS.Tc3`.  `convFun G f x = ∫ G(x-y) f(y) dy` (`HRS.Whole.HRS.Whole.convFun`).

* `tc3_young`, `tc3_memLp_conv`: `G ∈ L¹` measurable, `f ∈ L²` gives `G * f ∈ L²` with
  `‖G * f‖₂ ≤ ‖G‖₁ ‖f‖₂` (and the integral defining `G * f(x)` converges for a.e. `x`).
* `tc3_fourierL2_conv`: the convolution theorem `\widehat{G * f} = Ĝ f̂` a.e. (`L²` Fourier
  transform `fourierL2` of the real function, `Ĝ = 𝓕 (complexification of G)`).  Proof: continuous
  compactly supported `f` (then `L¹ ∩ L²`, Mathlib's `Real.fourier_smul_convolution_eq`), then density.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform Convolution

namespace HRS.MS.Tc3
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.Whole HRS.MS.SobMul

variable {d : ℕ}

/-- `HRS.Whole.convFun G f = f ⋆ G` for the real multiplication. -/
theorem tc3_convFun_eq_conv (G f : Euc d → ℝ) :
    HRS.Whole.convFun G f = f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] G := by
  funext x
  unfold HRS.Whole.convFun
  rw [convolution_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [mul_comm]

theorem tc3_aesm_conv {G f : Euc d → ℝ} (hG : AEStronglyMeasurable G volume)
    (hf : AEStronglyMeasurable f volume) : AEStronglyMeasurable (HRS.Whole.convFun G f) volume := by
  rw [tc3_convFun_eq_conv]
  exact hf.convolution _ hG

theorem tc3_young {G f : Euc d → ℝ} (hGm : Measurable G) (hG : Integrable G) (hf : MemLp f 2 volume) :
    (∀ᵐ x ∂(volume : Measure (Euc d)), Integrable (fun y => G (x - y) * f y)) ∧
    eLpNorm (HRS.Whole.convFun G f) 2 volume ≤ ENNReal.ofReal (∫ x, ‖G x‖) * eLpNorm f 2 volume := by
  set f' := hf.aestronglyMeasurable.mk f with hf'def
  have hf'm : Measurable f' := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hff' : f =ᵐ[volume] f' := hf.aestronglyMeasurable.ae_eq_mk
  set A : Euc d → ℝ≥0∞ := fun x => ‖G x‖ₑ with hA
  set B : Euc d → ℝ≥0∞ := fun y => ‖f' y‖ₑ with hB
  have hAm : Measurable A := hGm.enorm
  have hBm : Measurable B := hf'm.enorm
  have hY := sobmul_young hAm hBm
  have hAint : ∫⁻ x, A x = ENNReal.ofReal (∫ x, ‖G x‖) :=
    (ofReal_integral_norm_eq_lintegral_enorm hG).symm
  have hBint : (∫⁻ y, B y ^ 2) = eLpNorm f 2 volume ^ 2 := by
    have h1 : eLpNorm f 2 volume = eLpNorm f' 2 volume := eLpNorm_congr_ae hff'
    rw [h1, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf'm.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
    rfl
  set H : Euc d → ℝ≥0∞ := fun x => ∫⁻ y, A (x - y) * B y with hH
  have hBfin : eLpNorm f 2 volume < ⊤ := memLp_iff.1 hf
  have hAfin : ∫⁻ x, A x < ⊤ := by rw [hAint]; exact ENNReal.ofReal_lt_top
  have hpt : ∀ x, ‖HRS.Whole.convFun G f x‖ₑ ≤ H x := by
    intro x
    have e1 : HRS.Whole.convFun G f x = ∫ y, G (x - y) * f' y := by
      unfold HRS.Whole.convFun
      refine integral_congr_ae ?_
      filter_upwards [hff'] with y hy
      rw [hy]
    rw [e1]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun y => ?_
    rw [enorm_mul]
  have hHm : Measurable H := by
    have := ((hAm.comp (measurable_fst.sub measurable_snd)).mul
      (hBm.comp measurable_snd)).lintegral_prod_right' (ν := (volume : Measure (Euc d)))
    exact this
  have hH2fin : ∫⁻ x, H x ^ 2 < ⊤ := by
    refine lt_of_le_of_lt hY ?_
    rw [hBint]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top hAfin) (ENNReal.pow_lt_top hBfin)
  have hHae : ∀ᵐ x ∂(volume : Measure (Euc d)), H x < ⊤ := by
    have h1 : ∀ᵐ x ∂(volume : Measure (Euc d)), H x ^ 2 < ⊤ :=
      ae_lt_top (hHm.pow_const 2) hH2fin.ne
    filter_upwards [h1] with x hx
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    rw [hcon] at hx
    simp at hx
  refine ⟨?_, ?_⟩
  · filter_upwards [hHae] with x hx
    refine ⟨?_, ?_⟩
    · exact ((hGm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable).mul hf.aestronglyMeasurable
    · unfold HasFiniteIntegral
      refine lt_of_le_of_lt (le_of_eq ?_) hx
      refine lintegral_congr_ae ?_
      filter_upwards [hff'] with y hy
      rw [enorm_mul, hy]
  · have hconv_aesm := tc3_aesm_conv hGm.aestronglyMeasurable hf.aestronglyMeasurable
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hconv_aesm]
    simp only [ENNReal.toReal_ofNat]
    have h3 : ∫⁻ x, ‖HRS.Whole.convFun G f x‖ₑ ^ (2 : ℝ) ≤ ∫⁻ x, H x ^ 2 := by
      refine lintegral_mono fun x => ?_
      rw [ENNReal.rpow_two]
      exact pow_le_pow_left' (hpt x) 2
    have h4 : (∫⁻ x, ‖HRS.Whole.convFun G f x‖ₑ ^ (2 : ℝ)) ≤
        (ENNReal.ofReal (∫ x, ‖G x‖) * eLpNorm f 2 volume) ^ 2 := by
      refine h3.trans (hY.trans ?_)
      rw [hAint, hBint, mul_pow]
    calc (∫⁻ x, ‖HRS.Whole.convFun G f x‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
        ≤ ((ENNReal.ofReal (∫ x, ‖G x‖) * eLpNorm f 2 volume) ^ 2) ^ (1 / (2 : ℝ)) := by
          gcongr
      _ = _ := by
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          norm_num

theorem tc3_memLp_conv {G f : Euc d → ℝ} (hGm : Measurable G) (hG : Integrable G)
    (hf : MemLp f 2 volume) : MemLp (HRS.Whole.convFun G f) 2 volume := by
  refine memLp_iff.2 (lt_of_le_of_lt (tc3_young hGm hG hf).2 ?_)
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (memLp_iff.1 hf)

theorem tc3_eLpNorm_fourierL2 {u : Euc d → ℝ} (hu : MemLp u 2 volume) :
    eLpNorm (fourierL2 u) 2 volume = eLpNorm u 2 volume := by
  rw [fourierL2_eq hu, ← Lp.enorm_def (FT d (ofRealLp hu)) ]
  have h1 : ‖FT d (ofRealLp hu)‖ₑ = ‖ofRealLp hu‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, (FT d).norm_map]
  rw [h1, Lp.enorm_def]
  rw [eLpNorm_congr_ae (ofRealLp_coe hu)]
  exact eLpNorm_congr_enorm_ae (Complex.continuous_ofReal.comp_aestronglyMeasurable hu.aestronglyMeasurable)
    hu.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      show ‖((u x : ℝ) : ℂ)‖ₑ = ‖u x‖ₑ
      rw [← ofReal_norm, ← ofReal_norm, Complex.norm_real])

/-- the Fourier transform of `G`, complexified -/
def tc3_Ghat (G : Euc d → ℝ) : Euc d → ℂ := 𝓕 (fun x : Euc d => ((G x : ℝ) : ℂ))

theorem tc3_Ghat_continuous {G : Euc d → ℝ} (hG : Integrable G) : Continuous (tc3_Ghat G) := by
  have hi : Integrable (fun x : Euc d => ((G x : ℝ) : ℂ)) := hG.ofReal
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hi

theorem tc3_Ghat_norm_le {G : Euc d → ℝ} (ξ : Euc d) : ‖tc3_Ghat G ξ‖ ≤ ∫ x, ‖G x‖ := by
  unfold tc3_Ghat
  rw [Real.fourier_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp

theorem tc3_fourierL2_conv_cc {G g : Euc d → ℝ} (hGm : Measurable G) (hG : Integrable G)
    (hgc : Continuous g) (hgs : HasCompactSupport g) :
    fourierL2 (HRS.Whole.convFun G g) =ᵐ[volume] fun ξ => tc3_Ghat G ξ * fourierL2 g ξ := by
  have hg1 : Integrable g := hgc.integrable_of_hasCompactSupport hgs
  have hg2 : MemLp g 2 volume := hgc.memLp_of_hasCompactSupport hgs
  have hc2 := tc3_memLp_conv hGm hG hg2
  have hGc : Integrable (fun x : Euc d => ((G x : ℝ) : ℂ)) := hG.ofReal
  have hgc' : Integrable (fun x : Euc d => ((g x : ℝ) : ℂ)) := hg1.ofReal
  have hconv : (fun x => ((HRS.Whole.convFun G g x : ℝ) : ℂ)) =
      (fun x : Euc d => ((g x : ℝ) : ℂ)) ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume]
        (fun x : Euc d => ((G x : ℝ) : ℂ)) := by
    funext x
    unfold HRS.Whole.convFun
    rw [convolution_def, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp [mul_comm]
  have hc1 : Integrable (HRS.Whole.convFun G g) volume := by
    rw [tc3_convFun_eq_conv]
    exact hg1.integrable_convolution _ hG
  have h1 := HRS.Commutator.Whole.energyAux_fourierL2_eq (HRS.Whole.convFun G g) hc1 hc2
  have h2 := HRS.Commutator.Whole.energyAux_fourierL2_eq g hg1 hg2
  filter_upwards [h1, h2] with ξ a b
  rw [a, b]
  show 𝓕 (fun x => ((HRS.Whole.convFun G g x : ℝ) : ℂ)) ξ = _
  rw [hconv, Real.fourier_smul_convolution_eq hgc' hGc ξ]
  simp [tc3_Ghat, mul_comm]

theorem tc3_conv_sub_ae {G f g : Euc d → ℝ} (hGm : Measurable G) (hG : Integrable G)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    HRS.Whole.convFun G (fun x => f x - g x) =ᵐ[volume]
      fun x => HRS.Whole.convFun G f x - HRS.Whole.convFun G g x := by
  filter_upwards [(tc3_young hGm hG hf).1, (tc3_young hGm hG hg).1] with x h1 h2
  unfold HRS.Whole.convFun
  rw [← integral_sub h1 h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [mul_sub]

/-- The convolution theorem on `L¹ * L²`: `\widehat{G * f} = Ĝ f̂` a.e. -/
theorem tc3_fourierL2_conv {G f : Euc d → ℝ} (hGm : Measurable G) (hG : Integrable G)
    (hf : MemLp f 2 volume) :
    fourierL2 (HRS.Whole.convFun G f) =ᵐ[volume] fun ξ => tc3_Ghat G ξ * fourierL2 f ξ := by
  set M : ℝ := ∫ x, ‖G x‖ with hM
  have hM0 : 0 ≤ M := integral_nonneg fun x => norm_nonneg _
  have hcf := tc3_memLp_conv hGm hG hf
  have hFm : AEStronglyMeasurable (fourierL2 (HRS.Whole.convFun G f)) volume :=
    aestronglyMeasurable_fourierL2 hcf
  have hPm : AEStronglyMeasurable (fun ξ => tc3_Ghat G ξ * fourierL2 f ξ) volume :=
    (tc3_Ghat_continuous hG).aestronglyMeasurable.mul (aestronglyMeasurable_fourierL2 hf)
  have key : ∀ ε : ℝ≥0∞, ε ≠ 0 →
      eLpNorm (fun ξ => fourierL2 (HRS.Whole.convFun G f) ξ - tc3_Ghat G ξ * fourierL2 f ξ) 2
        volume ≤ 2 * (ENNReal.ofReal M * ε) := by
    intro ε hε
    obtain ⟨g, hgs, hgε, hgc, hg2⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) hε
    have hu : MemLp (fun x => f x - g x) 2 volume := hf.sub hg2
    have hgε' : eLpNorm (fun x => f x - g x) 2 volume ≤ ε := hgε
    have hcg := tc3_memLp_conv hGm hG hg2
    have hcu := tc3_memLp_conv hGm hG hu
    have hcc := tc3_fourierL2_conv_cc hGm hG hgc hgs
    have A1 : (fun ξ => fourierL2 (HRS.Whole.convFun G f) ξ - fourierL2 (HRS.Whole.convFun G g) ξ)
        =ᵐ[volume] fourierL2 (HRS.Whole.convFun G (fun x => f x - g x)) := by
      have e1 := fourierL2_sub hcf hcg
      have e2 : fourierL2 (fun x => HRS.Whole.convFun G f x - HRS.Whole.convFun G g x) =
          fourierL2 (HRS.Whole.convFun G (fun x => f x - g x)) :=
        fourierL2_congr_ae (tc3_conv_sub_ae hGm hG hf hg2).symm
      exact e1.symm.trans (Filter.Eventually.of_forall fun ξ => congrFun e2 ξ)
    have B1 : eLpNorm (fun ξ => fourierL2 (HRS.Whole.convFun G f) ξ -
        fourierL2 (HRS.Whole.convFun G g) ξ) 2 volume ≤ ENNReal.ofReal M * ε := by
      rw [eLpNorm_congr_ae A1, tc3_eLpNorm_fourierL2 hcu]
      exact (tc3_young hGm hG hu).2.trans (by gcongr)
    have A2 : ∀ᵐ ξ ∂(volume : Measure (Euc d)),
        ‖tc3_Ghat G ξ * fourierL2 g ξ - tc3_Ghat G ξ * fourierL2 f ξ‖ ≤
          M * ‖fourierL2 (fun x => f x - g x) ξ‖ := by
      filter_upwards [fourierL2_sub hf hg2] with ξ h
      rw [h, ← mul_sub, norm_mul, ← norm_neg (fourierL2 f ξ - fourierL2 g ξ), neg_sub]
      exact mul_le_mul_of_nonneg_right (tc3_Ghat_norm_le ξ) (norm_nonneg _)
    have B2 : eLpNorm (fun ξ => tc3_Ghat G ξ * fourierL2 g ξ - tc3_Ghat G ξ * fourierL2 f ξ) 2
        volume ≤ ENNReal.ofReal M * ε := by
      have hm : AEStronglyMeasurable
          (fun ξ => tc3_Ghat G ξ * fourierL2 g ξ - tc3_Ghat G ξ * fourierL2 f ξ) volume :=
        ((tc3_Ghat_continuous hG).aestronglyMeasurable.mul (aestronglyMeasurable_fourierL2 hg2)).sub
          hPm
      refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm A2 2).trans ?_
      rw [tc3_eLpNorm_fourierL2 hu]
      gcongr
    have A3 : (fun ξ => fourierL2 (HRS.Whole.convFun G f) ξ - tc3_Ghat G ξ * fourierL2 f ξ)
        =ᵐ[volume] ((fun ξ => fourierL2 (HRS.Whole.convFun G f) ξ -
            fourierL2 (HRS.Whole.convFun G g) ξ) +
          (fun ξ => tc3_Ghat G ξ * fourierL2 g ξ - tc3_Ghat G ξ * fourierL2 f ξ)) := by
      filter_upwards [hcc] with ξ h
      simp only [Pi.add_apply]
      rw [h]
      ring
    have hm1 : AEStronglyMeasurable (fun ξ => fourierL2 (HRS.Whole.convFun G f) ξ -
        fourierL2 (HRS.Whole.convFun G g) ξ) volume :=
      hFm.sub (aestronglyMeasurable_fourierL2 hcg)
    rw [eLpNorm_congr_ae A3]
    refine (eLpNorm_add_le (p := 2) (by norm_num)).trans ?_
    calc _ ≤ ENNReal.ofReal M * ε + ENNReal.ofReal M * ε := add_le_add B1 B2
      _ = 2 * (ENNReal.ofReal M * ε) := by rw [two_mul]
  have hz : eLpNorm (fun ξ => fourierL2 (HRS.Whole.convFun G f) ξ - tc3_Ghat G ξ * fourierL2 f ξ) 2
      volume = 0 := by
    refine le_antisymm ?_ bot_le
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hpos : (0 : ℝ) < ((ε : ℝ≥0) : ℝ) / (2 * (M + 1)) := by
      have : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
      positivity
    refine (key (ENNReal.ofReal (((ε : ℝ≥0) : ℝ) / (2 * (M + 1)))) (by simpa using hpos)).trans ?_
    rw [zero_add, ← ENNReal.ofReal_mul hM0, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    rw [← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : (0 : ℝ) < M + 1 := by linarith
    have : 2 * (M * ((ε : ℝ) / (2 * (M + 1)))) = (ε : ℝ) * (M / (M + 1)) := by
      field_simp
    rw [this]
    have h2 : M / (M + 1) ≤ 1 := by rw [div_le_one h1]; linarith
    nlinarith [NNReal.coe_nonneg ε, h2]
  have := (eLpNorm_eq_zero_iff (p := 2) (by norm_num)).1 hz
  · filter_upwards [this] with ξ h
    simpa [sub_eq_zero] using h

/-- **Generic Sobolev gain.**  If `G ∈ L¹` is measurable with `|Ĝ(ξ)| ≤ A ⟨ξ⟩^{-α}`
(`⟨ξ⟩² = wt ξ = 1 + 4π²|ξ|²`), then `f ∈ H^t` implies `G * f ∈ H^{t+α}` with
`‖G * f‖²_{H^{t+α}} ≤ A² ‖f‖²_{H^t}` (any real `t`). -/
theorem tc3_sobolev_gain {G : Euc d → ℝ} (hGm : Measurable G) (hG : Integrable G) {α A : ℝ}
    (hFG : ∀ ξ : Euc d, ‖tc3_Ghat G ξ‖ ≤ A * wt ξ ^ (-α / 2)) {t : ℝ} {f : Euc d → ℝ}
    (hf : HRS.PDE.ToolboxRd.MemSobolev t f) :
    HRS.PDE.ToolboxRd.MemSobolev (t + α) (HRS.Whole.convFun G f) ∧
      HRS.PDE.ToolboxRd.sobolevNormSq (t + α) (HRS.Whole.convFun G f) ≤ A ^ 2 * HRS.PDE.ToolboxRd.sobolevNormSq t f := by
  have hcf := tc3_memLp_conv hGm hG hf.1
  have hconv := tc3_fourierL2_conv hGm hG hf.1
  have hpt : ∀ ξ : Euc d, wt ξ ^ (t + α) * ‖tc3_Ghat G ξ * fourierL2 f ξ‖ ^ 2 ≤
      A ^ 2 * (wt ξ ^ t * ‖fourierL2 f ξ‖ ^ 2) := by
    intro ξ
    have hw := wt_pos (d := d) ξ
    have h1 : ‖tc3_Ghat G ξ‖ ^ 2 ≤ (A * wt ξ ^ (-α / 2)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hFG ξ) 2
    have h2 : (wt ξ ^ (-α / 2)) ^ 2 = wt ξ ^ (-α) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hw.le]
      norm_num
    have h3 : wt ξ ^ (t + α) * wt ξ ^ (-α) = wt ξ ^ t := by
      rw [← Real.rpow_add hw]; ring_nf
    rw [norm_mul, mul_pow]
    calc wt ξ ^ (t + α) * (‖tc3_Ghat G ξ‖ ^ 2 * ‖fourierL2 f ξ‖ ^ 2)
        ≤ wt ξ ^ (t + α) * ((A * wt ξ ^ (-α / 2)) ^ 2 * ‖fourierL2 f ξ‖ ^ 2) := by
          gcongr
      _ = A ^ 2 * (wt ξ ^ (t + α) * wt ξ ^ (-α)) * ‖fourierL2 f ξ‖ ^ 2 := by
          rw [mul_pow, h2]; ring
      _ = _ := by rw [h3]; ring
  have hint : Integrable (fun ξ => wt ξ ^ (t + α) * ‖fourierL2 (HRS.Whole.convFun G f) ξ‖ ^ 2)
      volume := by
    refine Integrable.mono' (hf.2.const_mul (A ^ 2))
      (aesm_wt_mul (aestronglyMeasurable_fourierL2 hcf) (t + α)) ?_
    filter_upwards [hconv] with ξ h
    rw [h]
    have h0 : 0 ≤ wt ξ ^ (t + α) * ‖tc3_Ghat G ξ * fourierL2 f ξ‖ ^ 2 := by
      have := wt_pos (d := d) ξ; positivity
    rw [Real.norm_of_nonneg h0]
    exact hpt ξ
  refine ⟨⟨hcf, hint⟩, ?_⟩
  rw [sobolevNormSq_eq, sobolevNormSq_eq, ← integral_const_mul]
  refine integral_mono_ae hint (hf.2.const_mul (A ^ 2)) ?_
  filter_upwards [hconv] with ξ h
  rw [h]
  exact hpt ξ

/-- Extended-norm form of `tc3_sobolev_gain`, for `A > 0`: no hypothesis on `f` (the norm is `⊤`
unless `f ∈ H^t`). -/
theorem tc3_sobolevNormE_gain {G : Euc d → ℝ} (hGm : Measurable G) (hG : Integrable G)
    {α A : ℝ} (hA : 0 < A) (hFG : ∀ ξ : Euc d, ‖tc3_Ghat G ξ‖ ≤ A * wt ξ ^ (-α / 2)) (t : ℝ)
    (f : Euc d → ℝ) :
    HRS.Whole.sobolevNormE (t + α) (HRS.Whole.convFun G f) ≤
      ENNReal.ofReal A * HRS.Whole.sobolevNormE t f := by
  by_cases hf : HRS.PDE.ToolboxRd.MemSobolev t f
  · obtain ⟨h1, h2⟩ := tc3_sobolev_gain hGm hG hFG hf
    unfold HRS.Whole.sobolevNormE
    rw [if_pos hf, if_pos h1, ← ENNReal.ofReal_mul hA.le]
    apply ENNReal.ofReal_le_ofReal
    calc Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (t + α) (HRS.Whole.convFun G f))
        ≤ Real.sqrt (A ^ 2 * HRS.PDE.ToolboxRd.sobolevNormSq t f) := Real.sqrt_le_sqrt h2
      _ = A * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq t f) := by
          rw [Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq hA.le]
  · unfold HRS.Whole.sobolevNormE
    rw [if_neg hf, ENNReal.mul_top (by simp; exact hA)]
    exact le_top

end HRS.MS.Tc3
