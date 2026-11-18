import HRS.Commutator.Whole.XLIAux1

/-!
# X-LI part 2: Plancherel on `L¹ ∩ L²`, dyadic kernels of symbols
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution ComplexInnerProductSpace SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- Plancherel for `L¹ ∩ L²`: the pointwise Fourier integral is the `L²` Fourier transform. -/
lemma plancherel_L1L2 {u : 𝔼 → ℂ} (h1 : Integrable u) (h2 : MemLp u 2 volume) :
    ∫⁻ ξ, ‖𝓕 u ξ‖ₑ ^ 2 = ∫⁻ x, ‖u x‖ₑ ^ 2 := by
  set uL : Lp ℂ 2 (volume : Measure 𝔼) := h2.toLp u with huL
  set vL : Lp ℂ 2 (volume : Measure 𝔼) := 𝓕 uL with hvL
  have hnorm : ‖vL‖ = ‖uL‖ := Lp.norm_fourier_eq uL
  -- identify `vL` with the pointwise Fourier integral
  have hident : (vL : 𝔼 → ℂ) =ᵐ[volume] 𝓕 u := by
    have hv_loc : LocallyIntegrable (fun x => (vL : 𝔼 → ℂ) x) volume :=
      (Lp.memLp vL).locallyIntegrable (by norm_num)
    have hF_loc : LocallyIntegrable (𝓕 u) volume :=
      (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (by exact continuous_inner) h1).locallyIntegrable
    have hf : LocallyIntegrable (fun x => (vL : 𝔼 → ℂ) x - 𝓕 u x) volume := hv_loc.sub hF_loc
    have hzero : ∀ g : 𝔼 → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
        ∫ x, g x • ((vL : 𝔼 → ℂ) x - 𝓕 u x) = 0 := by
      intro g hg hgc
      have hgc' : HasCompactSupport (fun x => ((g x : ℝ) : ℂ)) :=
        hgc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
      have hsm : ContDiff ℝ ∞ (fun x => ((g x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
      let ψ : SchwartzMap 𝔼 ℂ := hgc'.toSchwartzMap hsm
      have hψ : ∀ x, ψ x = ((g x : ℝ) : ℂ) := fun x => rfl
      have hdist : ∫ x, ψ x • (vL : 𝔼 → ℂ) x = ∫ x, (𝓕 ψ) x • u x := by
        have h := congrArg (fun T : 𝓢'(𝔼, ℂ) => T ψ) (Lp.fourier_toTemperedDistribution_eq uL)
        simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply] at h
        rw [← h]
        refine integral_congr_ae ?_
        filter_upwards [h2.coeFn_toLp] with x hx
        rw [hx]
      have hFb : Continuous (𝓕 u) :=
        VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
          (by exact continuous_inner) h1
      have hflip : ∫ x, (𝓕 u x) * ψ x = ∫ x, u x * (𝓕 ψ) x := by
        have := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ 𝔼)
          (μ := (volume : Measure 𝔼)) (ν := (volume : Measure 𝔼)) Real.continuous_fourierChar
          (by exact continuous_inner) h1 ψ.integrable
        simp only [smul_eq_mul] at this
        rw [SchwartzMap.fourier_coe]
        convert this using 3
        simp [Real.fourier_eq, VectorFourier.fourierIntegral]
      have hI1 : Integrable (fun x => ψ x * (vL : 𝔼 → ℂ) x) :=
        (ψ.memLp 2).integrable_mul (Lp.memLp vL)
      have hbd : ∀ x, ‖𝓕 u x‖ ≤ ∫ y, ‖u y‖ := fun x => by
        have := VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ 𝔼) u x
        simpa [Real.fourier_eq, VectorFourier.fourierIntegral] using this
      have hI2 : Integrable (fun x => ψ x * 𝓕 u x) := by
        have := Integrable.bdd_mul (ψ.integrable (μ := (volume : Measure 𝔼))) hFb.aestronglyMeasurable
          (Eventually.of_forall hbd)
        simpa [mul_comm] using this
      have e1 : ∫ x, g x • ((vL : 𝔼 → ℂ) x - 𝓕 u x)
          = (∫ x, ψ x * (vL : 𝔼 → ℂ) x) - ∫ x, ψ x * 𝓕 u x := by
        rw [← integral_sub hI1 hI2]
        congr 1; ext x
        rw [Complex.real_smul, hψ]
        ring
      have e2 : ∫ x, ψ x * (vL : 𝔼 → ℂ) x = ∫ x, (𝓕 ψ) x * u x := by
        simpa only [smul_eq_mul] using hdist
      have e3 : ∫ x, ψ x * 𝓕 u x = ∫ x, (𝓕 ψ) x * u x := by
        have : ∫ x, ψ x * 𝓕 u x = ∫ x, 𝓕 u x * ψ x := by
          congr 1; ext x; ring
        rw [this, hflip]
        congr 1; ext x; ring
      rw [e1, e2, e3, sub_self]
    have hF := ae_eq_zero_of_integral_contDiff_smul_eq_zero hf hzero
    filter_upwards [hF] with y hy
    exact sub_eq_zero.1 hy
  -- conclude with the `L²` norms
  have hF2 : eLpNorm (𝓕 u) 2 volume = eLpNorm (vL : 𝔼 → ℂ) 2 volume := (eLpNorm_congr_ae hident).symm
  have hu2 : eLpNorm u 2 volume = eLpNorm (uL : 𝔼 → ℂ) 2 volume :=
    (eLpNorm_congr_ae h2.coeFn_toLp).symm
  have hn : eLpNorm (vL : 𝔼 → ℂ) 2 volume = eLpNorm (uL : 𝔼 → ℂ) 2 volume := by
    rw [Lp.norm_def, Lp.norm_def] at hnorm
    exact (ENNReal.toReal_eq_toReal_iff' (Lp.memLp vL).eLpNorm_ne_top (Lp.memLp uL).eLpNorm_ne_top).1 hnorm
  have key : eLpNorm (𝓕 u) 2 volume = eLpNorm u 2 volume := by rw [hF2, hn, hu2]
  have hsq : ∀ f : 𝔼 → ℂ, AEStronglyMeasurable f volume →
      ∫⁻ x, ‖f x‖ₑ ^ 2 = eLpNorm f 2 volume ^ 2 := by
    intro f hf
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
    simp only [ENNReal.toReal_ofNat]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hFm : AEStronglyMeasurable (𝓕 u) volume :=
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by exact continuous_inner) h1).aestronglyMeasurable
  rw [hsq _ hFm, hsq _ h2.aestronglyMeasurable, key]

/-! ### Convolution and the majorant kernels -/

/-- the convolution `K ⋆ u` -/
abbrev cv (K u : 𝔼 → ℂ) : 𝔼 → ℂ := K ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] u

lemma cv_apply (K u : 𝔼 → ℂ) (x : 𝔼) : cv K u x = ∫ y, K y * u (x - y) := by
  show (K ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] u) x = _
  rw [convolution_def]; rfl

lemma enorm_cv_le (K u : 𝔼 → ℂ) (x : 𝔼) :
    ‖cv K u x‖ₑ ≤ ∫⁻ y, ‖K y‖ₑ * ‖u (x - y)‖ₑ := by
  rw [cv_apply]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  refine lintegral_congr fun y => ?_
  simp [enorm_mul]

/-- Cauchy–Schwarz for lintegrals against a nonnegative weight -/
lemma sq_lintegral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, f a * g a ∂μ) ^ 2 ≤ (∫⁻ a, f a ∂μ) * ∫⁻ a, f a * g a ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (Real.HolderConjugate.two_two)
    (f := fun a => f a ^ (1 / 2 : ℝ)) (g := fun a => f a ^ (1 / 2 : ℝ) * g a)
    (hf.pow_const _) ((hf.pow_const _).mul hg)
  have e1 : ∀ a, f a ^ (1 / 2 : ℝ) * (f a ^ (1 / 2 : ℝ) * g a) = f a * g a := by
    intro a
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have e2 : ∀ a, (f a ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = f a := by
    intro a; rw [← ENNReal.rpow_mul]; norm_num
  have e3 : ∀ a, (f a ^ (1 / 2 : ℝ) * g a) ^ (2 : ℝ) = f a * g a ^ 2 := by
    intro a
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), e2]
    norm_cast
  simp only [Pi.mul_apply, e1, e2, e3] at h
  have h2 : (∫⁻ a, f a * g a ∂μ) ≤ (∫⁻ a, f a ∂μ) ^ (1 / 2 : ℝ) *
      (∫⁻ a, f a * g a ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
    simpa using h
  calc (∫⁻ a, f a * g a ∂μ) ^ 2 ≤ ((∫⁻ a, f a ∂μ) ^ (1 / 2 : ℝ) *
      (∫⁻ a, f a * g a ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = _ := by
      rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
        ← ENNReal.rpow_mul]
      norm_num

/-- `K` is dominated by `A * Phi j` -/
def DecK (A : ℝ≥0∞) (j : ℤ) (K : 𝔼 → ℂ) : Prop := ∀ y, ‖K y‖ₑ ≤ A * Phi j y

lemma Md_one_le (x : 𝔼) : cmxHLS_Md (fun _ => (1 : ℝ≥0∞)) x ≤ 1 := by
  unfold cmxHLS_Md
  refine iSup_le fun j => ?_
  have h0 := cmxHLS_vol_closedBall_ne_zero x (zpow_pos (by norm_num : (0 : ℝ) < 2) j)
  have h1 := cmxHLS_vol_closedBall_ne_top x ((2 : ℝ) ^ j)
  rw [setLIntegral_const, mul_comm]
  simp only [one_mul]
  rw [ENNReal.mul_inv_cancel h0 h1]

lemma lintegral_Phi_le_KP (j : ℤ) : ∫⁻ y : 𝔼, Phi j y ≤ KP d := by
  have h := lintegral_Phi_le (d := d) j (G := fun _ : 𝔼 => (1 : ℝ≥0∞)) measurable_const (0 : 𝔼)
  simp only [mul_one] at h
  exact h.trans (by simpa using mul_le_mul_right (Md_one_le (0 : 𝔼)) (KP d))

lemma lintegral_enorm_le_of_dec {A : ℝ≥0∞} {j : ℤ} {K : 𝔼 → ℂ} (hK : DecK A j K) :
    ∫⁻ y, ‖K y‖ₑ ≤ A * KP d := by
  calc ∫⁻ y, ‖K y‖ₑ ≤ ∫⁻ y, A * Phi j y := lintegral_mono hK
    _ = A * ∫⁻ y, Phi j y := lintegral_const_mul _ (Phi_measurable j)
    _ ≤ A * KP d := by gcongr; exact lintegral_Phi_le_KP j

/-- pointwise Cauchy–Schwarz bound for a convolution with a dominated kernel -/
lemma enorm_cv_sq_le {A : ℝ≥0∞} {j : ℤ} {K u : 𝔼 → ℂ} (hK : DecK A j K) (hKm : Measurable K)
    (hu : Measurable u) (x : 𝔼) :
    ‖cv K u x‖ₑ ^ 2 ≤ (A * KP d) * (A * CvP j (fun y => ‖u y‖ₑ ^ 2) x) := by
  have h1 := enorm_cv_le K u x
  have hm : AEMeasurable (fun y => ‖u (x - y)‖ₑ) volume :=
    (hu.comp (measurable_const.sub measurable_id)).enorm.aemeasurable
  have hKm' : AEMeasurable (fun y => ‖K y‖ₑ) volume := hKm.enorm.aemeasurable
  calc ‖cv K u x‖ₑ ^ 2 ≤ (∫⁻ y, ‖K y‖ₑ * ‖u (x - y)‖ₑ) ^ 2 := by gcongr
    _ ≤ (∫⁻ y, ‖K y‖ₑ) * ∫⁻ y, ‖K y‖ₑ * ‖u (x - y)‖ₑ ^ 2 := sq_lintegral_le volume hKm' hm
    _ ≤ (A * KP d) * (A * CvP j (fun y => ‖u y‖ₑ ^ 2) x) := by
        refine mul_le_mul' (lintegral_enorm_le_of_dec hK) ?_
        unfold CvP
        have hmeas : Measurable (fun y : 𝔼 => Phi j y * ‖u (x - y)‖ₑ ^ 2) :=
          (Phi_measurable j).mul ((hu.comp (measurable_const.sub measurable_id)).enorm.pow_const 2)
        show ∫⁻ y, ‖K y‖ₑ * ‖u (x - y)‖ₑ ^ 2 ≤ A * ∫⁻ y, Phi j y * ‖u (x - y)‖ₑ ^ 2
        rw [← lintegral_const_mul _ hmeas]
        refine lintegral_mono fun y => ?_
        rw [← mul_assoc]
        exact mul_le_mul_left (hK y) _

/-- the square of the `ℓ²`-norm of a sequence of functions -/
def sqS (f : ℤ → 𝔼 → ℂ) (x : 𝔼) : ℝ≥0∞ := ∑' j, ‖f j x‖ₑ ^ 2

lemma sqS_measurable {f : ℤ → 𝔼 → ℂ} (hf : ∀ j, Measurable (f j)) : Measurable (sqS f) := by
  unfold sqS
  exact Measurable.ennreal_tsum fun j => (hf j).enorm.pow_const 2

/-- vector-valued Fefferman–Stein for dominated convolution kernels, exponent `p/2 = s > 1` -/
lemma E3_ge (hd : 1 ≤ d) {s : ℝ} (hs : 1 < s) :
    ∃ C : ℝ≥0, ∀ (A : ℝ≥0∞), A ≠ ⊤ → ∀ (K h : ℤ → 𝔼 → ℂ), (∀ j, DecK A j (K j)) →
      (∀ j, Measurable (K j)) → (∀ j, Measurable (h j)) →
      ∫⁻ x, sqS (fun j => cv (K j) (h j)) x ^ s ≤
        ((A * A * KP d) ^ s * C) * ∫⁻ x, sqS h x ^ s := by
  have hs0 : 0 < s := by linarith
  obtain ⟨C, hC⟩ := conv_pos_strong hd hs
  refine ⟨C, fun A hA K h hK hKm hh => ?_⟩
  set H : ℤ → 𝔼 → ℝ≥0∞ := fun j y => ‖h j y‖ₑ ^ 2 with hH
  have hHm : ∀ j, Measurable (H j) := fun j => (hh j).enorm.pow_const 2
  have hpt : ∀ x, sqS (fun j => cv (K j) (h j)) x ≤ (A * A * KP d) * ∑' j, CvP j (H j) x := by
    intro x
    unfold sqS
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun j => ?_
    calc ‖cv (K j) (h j) x‖ₑ ^ 2 ≤ (A * KP d) * (A * CvP j (fun y => ‖h j y‖ₑ ^ 2) x) :=
          enorm_cv_sq_le (hK j) (hKm j) (hh j) x
      _ = _ := by ring
  calc ∫⁻ x, sqS (fun j => cv (K j) (h j)) x ^ s
      ≤ ∫⁻ x, ((A * A * KP d) * ∑' j, CvP j (H j) x) ^ s :=
        lintegral_mono fun x => ENNReal.rpow_le_rpow (hpt x) hs0.le
    _ = ∫⁻ x, (A * A * KP d) ^ s * (∑' j, CvP j (H j) x) ^ s :=
        lintegral_congr fun x => ENNReal.mul_rpow_of_nonneg _ _ hs0.le
    _ = (A * A * KP d) ^ s * ∫⁻ x, (∑' j, CvP j (H j) x) ^ s :=
        lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hs0.le
          (ENNReal.mul_ne_top (ENNReal.mul_ne_top hA hA) KP_ne_top))
    _ ≤ (A * A * KP d) ^ s * (C * ∫⁻ x, (∑' j, H j x) ^ s) := by
        gcongr
        exact hC H hHm
    _ = _ := by
        rw [← mul_assoc]
        rfl

end HRS.Commutator.Whole.XLI
