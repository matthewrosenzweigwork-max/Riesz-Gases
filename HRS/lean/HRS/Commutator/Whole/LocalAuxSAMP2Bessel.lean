import HRS.Commutator.Whole.LocalAuxSAMP2Cube

/-!
# CMX-SAMP (`usample`), part 2: Young `L¹ * L^p`, the representation `u = K ⋆ u`, the Bessel kernel

* `eLpNorm_conv_le`: `‖K ⋆ a‖_{L^p} ≤ ‖K‖_{L¹} ‖a‖_{L^p}` (Hölder with the weight `|K|`, Tonelli).
* `repr_everywhere`: a continuous `L^p` function with `supp â ⊂ B̄(0,2)` satisfies `a = K ⋆ a` at
  every point (`K` Schwartz with `K̂ = 1` on `B(0,3)`).
* `bessel_rep`: for such `a`, `⟨∇⟩^α a` is represented by `B_α ⋆ a`, `B_α = 𝓕⁻[(1+4π²|ξ|²)^{α/2} χ(ξ/3)]`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

namespace HRS.Commutator.Whole.SAMP2

variable {d : ℕ}

/-! ### Young's inequality `L¹ * L^p` -/

lemma conv_lintegral_le {p : ℝ} (hp : 1 < p) {K a : Euc d → ℝ} (hK : Measurable K)
    (ha : Measurable a) (hκ : ∫⁻ t, ‖K t‖ₑ ≠ ⊤) :
    ∫⁻ y, (∫⁻ t, ‖K t‖ₑ * ‖a (y + t)‖ₑ) ^ p ≤ (∫⁻ t, ‖K t‖ₑ) ^ p * ∫⁻ y, ‖a y‖ₑ ^ p := by
  have hp0 : 0 < p := by linarith
  have hw : Measurable fun t => ‖K t‖ₑ := hK.enorm
  set κ := ∫⁻ t, ‖K t‖ₑ with hκdef
  have hsh : Measurable (fun q : Euc d × Euc d => a (q.1 + q.2)) :=
    ha.comp (measurable_fst.add measurable_snd)
  have hF : Measurable (Function.uncurry fun (y t : Euc d) => ‖K t‖ₑ * ‖a (y + t)‖ₑ ^ p) := by
    have h1 : Measurable (fun q : Euc d × Euc d => ‖K q.2‖ₑ) := hw.comp measurable_snd
    have h2 : Measurable (fun q : Euc d × Euc d => ‖a (q.1 + q.2)‖ₑ ^ p) :=
      (hsh.enorm).pow_const p
    exact h1.mul h2
  have h1 : ∀ y, (∫⁻ t, ‖K t‖ₑ * ‖a (y + t)‖ₑ) ^ p ≤
      κ ^ (p - 1) * ∫⁻ t, ‖K t‖ₑ * ‖a (y + t)‖ₑ ^ p := by
    intro y
    exact lintegral_weight_rpow_le volume hp hw.aemeasurable
      (ha.comp (measurable_const.add measurable_id)).enorm.aemeasurable
  have hκp : κ ^ (p - 1) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by linarith) hκ
  calc ∫⁻ y, (∫⁻ t, ‖K t‖ₑ * ‖a (y + t)‖ₑ) ^ p
      ≤ ∫⁻ y, κ ^ (p - 1) * ∫⁻ t, ‖K t‖ₑ * ‖a (y + t)‖ₑ ^ p := lintegral_mono h1
    _ = κ ^ (p - 1) * ∫⁻ y, ∫⁻ t, ‖K t‖ₑ * ‖a (y + t)‖ₑ ^ p := lintegral_const_mul' _ _ hκp
    _ = κ ^ (p - 1) * ∫⁻ t, ∫⁻ y, ‖K t‖ₑ * ‖a (y + t)‖ₑ ^ p := by
        rw [lintegral_lintegral_swap hF.aemeasurable]
    _ = κ ^ (p - 1) * ∫⁻ t, ‖K t‖ₑ * ∫⁻ y, ‖a y‖ₑ ^ p := by
        congr 1
        refine lintegral_congr fun t => ?_
        have hmeas : Measurable (fun y : Euc d => ‖a (y + t)‖ₑ ^ p) := by
          have := ha.comp (measurable_id.add_const t)
          exact this.enorm.pow_const p
        rw [lintegral_const_mul _ hmeas]
        congr 1
        exact lintegral_add_right_eq_self (fun y => ‖a y‖ₑ ^ p) t
    _ = κ ^ (p - 1) * (κ * ∫⁻ y, ‖a y‖ₑ ^ p) := by
        rw [lintegral_mul_const _ hw]
    _ = κ ^ p * ∫⁻ y, ‖a y‖ₑ ^ p := by
        rw [← mul_assoc]
        congr 1
        have hp1 : 0 ≤ p - 1 := by linarith
        calc κ ^ (p - 1) * κ = κ ^ (p - 1) * κ ^ (1 : ℝ) := by rw [ENNReal.rpow_one]
          _ = κ ^ (p - 1 + 1) := (ENNReal.rpow_add_of_nonneg _ _ hp1 zero_le_one).symm
          _ = κ ^ p := by congr 1; ring

lemma conv_aestronglyMeasurable {K a : Euc d → ℝ} (hK : Measurable K) (ha : Measurable a) :
    AEStronglyMeasurable (fun y : Euc d => ∫ t, K t * a (y + t)) volume := by
  have hF : Measurable (fun q : Euc d × Euc d => K q.2 * a (q.1 + q.2)) :=
    (hK.comp measurable_snd).mul (ha.comp (measurable_fst.add measurable_snd))
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable

lemma eLpNorm_conv_le {p : ℝ} (hp : 1 < p) {K a : Euc d → ℝ} (hK : Measurable K)
    (ha : Measurable a) (hκ : ∫⁻ t, ‖K t‖ₑ ≠ ⊤) :
    eLpNorm (fun y => ∫ t, K t * a (y + t)) (ENNReal.ofReal p) volume ≤
      (∫⁻ t, ‖K t‖ₑ) * eLpNorm a (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := by linarith
  have hP0 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
  have hPt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPt (conv_aestronglyMeasurable hK ha),
    eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPt ha.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le]
  have hpt : ∀ y, ‖∫ t, K t * a (y + t)‖ₑ ≤ ∫⁻ t, ‖K t‖ₑ * ‖a (y + t)‖ₑ := by
    intro y
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    simp_rw [enorm_mul]
  have h1 : ∫⁻ y, ‖∫ t, K t * a (y + t)‖ₑ ^ p ≤ ∫⁻ y, (∫⁻ t, ‖K t‖ₑ * ‖a (y + t)‖ₑ) ^ p :=
    lintegral_mono fun y => ENNReal.rpow_le_rpow (hpt y) hp0.le
  calc (∫⁻ y, ‖∫ t, K t * a (y + t)‖ₑ ^ p) ^ (1 / p)
      ≤ ((∫⁻ t, ‖K t‖ₑ) ^ p * ∫⁻ y, ‖a y‖ₑ ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (h1.trans (conv_lintegral_le hp hK ha hκ)) (by positivity)
    _ = (∫⁻ t, ‖K t‖ₑ) * (∫⁻ y, ‖a y‖ₑ ^ p) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

/-! ### The representation `a = K ⋆ a` at every point -/

lemma bound_of_ae_continuous {f : Euc d → ℝ} (hf : Continuous f) {M : ℝ}
    (h : ∀ᵐ y ∂(volume : Measure (Euc d)), ‖f y‖ ≤ M) : ∀ y, ‖f y‖ ≤ M := by
  by_contra hcon
  push Not at hcon
  obtain ⟨y0, hy0⟩ := hcon
  have hopen : IsOpen {y : Euc d | M < ‖f y‖} := isOpen_lt continuous_const hf.norm
  have hzero : volume {y : Euc d | M < ‖f y‖} = 0 := by
    have := ae_iff.1 h
    simpa [not_le] using this
  have := (hopen.measure_eq_zero_iff volume).1 hzero
  exact (Set.eq_empty_iff_forall_notMem.1 this) y0 hy0

lemma repr_everywhere {p : ℝ} (hp : 1 < p) (K : SchwartzMap (Euc d) ℂ)
    (hK : ∀ ξ : Euc d, ‖ξ‖ < 2 + 1 → 𝓕 (⇑K) ξ = 1) {a : Euc d → ℝ} (hac : Continuous a)
    (ha : MemLp a (ENNReal.ofReal p) volume) (hsupp : FourierSuppIn 2 a) (y : Euc d) :
    ((a y : ℝ) : ℂ) = ∫ t, K t * ((a (y + t) : ℝ) : ℂ) := by
  have hP1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  haveI hH : (ENNReal.ofReal p).HolderConjugate (ENNReal.conjExponent (ENNReal.ofReal p)) :=
    ENNReal.HolderConjugate.conjExponent hP1
  have hacm : MemLp (fun x => ((a x : ℝ) : ℂ)) (ENNReal.ofReal p) volume := ha.ofReal
  have hae := ae_repr_complex (p' := ENNReal.conjExponent (ENNReal.ofReal p)) hP1 K hK hacm
    (fun G hG => hsupp G hG)
  set M : ℝ≥0∞ := eLpNorm (fun x => ((a x : ℝ) : ℂ)) (ENNReal.ofReal p) volume *
    eLpNorm K (ENNReal.conjExponent (ENNReal.ofReal p)) volume with hM
  have hMtop : M ≠ ⊤ :=
    (ENNReal.mul_lt_top hacm.eLpNorm_lt_top (K.memLp _).eLpNorm_lt_top).ne
  -- boundedness of `a`
  have hbd : ∀ y, ‖a y‖ ≤ M.toReal := by
    refine bound_of_ae_continuous hac ?_
    filter_upwards [hae] with z hz
    have h1 := enorm_conv_le (p' := ENNReal.conjExponent (ENNReal.ofReal p)) hacm K z
    rw [← hz] at h1
    have h2 : ENNReal.ofReal ‖a z‖ ≤ M := by
      rw [ofReal_norm]
      rw [enorm_ofReal_c] at h1
      exact h1
    exact (ENNReal.ofReal_le_iff_le_toReal hMtop).1 h2
  -- continuity of the right-hand side
  set aC : Euc d → ℂ := fun x => ((a x : ℝ) : ℂ) with haC
  have haCc : Continuous aC := Complex.continuous_ofReal.comp hac
  set K' : Euc d → ℂ := fun t => K (-t) with hK'
  have hK'i : Integrable K' := K.integrable.comp_neg
  have hconv : Continuous (K' ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] aC) := by
    refine BddAbove.continuous_convolution_right_of_integrable (ContinuousLinearMap.mul ℂ ℂ)
      ⟨M.toReal, ?_⟩ hK'i haCc
    rintro _ ⟨x, rfl⟩
    simpa [haC] using hbd x
  have hg : (fun y => ∫ t, K t * ((a (y + t) : ℝ) : ℂ)) =
      (K' ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] aC) := by
    funext y
    rw [convolution_def]
    simp only [ContinuousLinearMap.mul_apply', hK', haC]
    rw [← integral_neg_eq_self (fun t => K t * ((a (y + t) : ℝ) : ℂ)) volume]
    congr 1
  have hcont : Continuous (fun y => ∫ t, K t * ((a (y + t) : ℝ) : ℂ)) := by
    rw [hg]; exact hconv
  have heq := (Continuous.ae_eq_iff_eq (volume : Measure (Euc d)) haCc hcont).1
    (by filter_upwards [hae] with y hy; exact hy)
  exact congrFun heq y

/-! ### The Bessel kernel -/

/-- The Bessel multiplier `m(ξ) = (1+4π²|ξ|²)^{α/2}` (complex valued). -/
def bsym (α : ℝ) (ξ : Euc d) : ℂ := (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (α / 2) : ℝ) : ℂ)

lemma bsym_temperate (α : ℝ) : (bsym α : Euc d → ℂ).HasTemperateGrowth := by
  have h1 := Function.hasTemperateGrowth_one_add_norm_sq_rpow (Euc d) (α / 2)
  have h2 : (fun ξ : Euc d => (2 * Real.pi) • ξ).HasTemperateGrowth :=
    ((2 * Real.pi) • ContinuousLinearMap.id ℝ (Euc d)).hasTemperateGrowth
  have h3 := h1.comp h2
  have h4 := Complex.hasTemperateGrowth_ofReal.comp h3
  convert h4 using 1
  funext ξ
  simp only [bsym, Function.comp, norm_smul, Real.norm_eq_abs, abs_mul, abs_two,
    abs_of_pos Real.pi_pos]
  congr 2
  ring

/-- `m(ξ) χ(ξ/3)`. -/
def bsymCut (α : ℝ) (ξ : Euc d) : ℂ := bsym α ξ * cmxFB_gL d 3 ξ

lemma bsymCut_contDiff (α : ℝ) : ContDiff ℝ ∞ (bsymCut α : Euc d → ℂ) :=
  (bsym_temperate α).1.mul (cmxFB_gL_contDiff 3)

lemma bsymCut_compact (α : ℝ) : HasCompactSupport (bsymCut α : Euc d → ℂ) :=
  (cmxFB_gL_compact (d := d) (by norm_num : (0 : ℝ) < 3)).mul_left

/-- The cut-off symbol as a Schwartz function. -/
def bsymS (α : ℝ) : SchwartzMap (Euc d) ℂ := (bsymCut_compact α).toSchwartzMap (bsymCut_contDiff α)

lemma bsymS_apply (α : ℝ) (ξ : Euc d) : bsymS (d := d) α ξ = bsymCut α ξ := rfl

/-- The kernel `B_α = 𝓕⁻[m χ(·/3)]`. -/
def Bker (α : ℝ) : SchwartzMap (Euc d) ℂ := 𝓕⁻ (bsymS (d := d) α)

lemma fourier_Bker (α : ℝ) : 𝓕 (Bker (d := d) α) = bsymS α :=
  FourierTransform.fourier_fourierInv_eq _

lemma finv_conj_self (n : Euc d → ℝ) (hn : ∀ ξ, n (-ξ) = n ξ) (x : Euc d) :
    (starRingEnd ℂ) (𝓕⁻ (fun ξ : Euc d => ((n ξ : ℝ) : ℂ)) x) =
      𝓕⁻ (fun ξ : Euc d => ((n ξ : ℝ) : ℂ)) x := by
  rw [Real.fourierInv_eq', ← integral_conj]
  have h : ∀ v : Euc d, (starRingEnd ℂ) (Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I) •
      ((n v : ℝ) : ℂ)) =
      (fun w : Euc d => Complex.exp (↑(2 * Real.pi * inner ℝ (-w) x) * Complex.I) •
        ((n (-w) : ℝ) : ℂ)) v := by
    intro v
    simp only [smul_eq_mul, map_mul, Complex.conj_ofReal, hn, inner_neg_left]
    congr 1
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  simp_rw [h]
  exact integral_neg_eq_self (fun w : Euc d =>
    Complex.exp (↑(2 * Real.pi * inner ℝ w x) * Complex.I) • ((n w : ℝ) : ℂ)) volume

/-- The real part of `B_α`. -/
def Br (α : ℝ) (x : Euc d) : ℝ := (Bker (d := d) α x).re

lemma Bker_eq_ofReal (α : ℝ) (x : Euc d) : Bker (d := d) α x = ((Br α x : ℝ) : ℂ) := by
  set n : Euc d → ℝ := fun ξ => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (α / 2) * chi ((3 : ℝ)⁻¹ • ξ) with hn
  have hcoe : (fun ξ : Euc d => bsymS (d := d) α ξ) = fun ξ => ((n ξ : ℝ) : ℂ) := by
    funext ξ
    rw [bsymS_apply]
    simp only [bsymCut, bsym, cmxFB_gL, hn]
    push_cast
    rfl
  have hB : Bker (d := d) α x = 𝓕⁻ (fun ξ : Euc d => ((n ξ : ℝ) : ℂ)) x := by
    unfold Bker
    rw [SchwartzMap.fourierInv_coe]
    exact congrArg (fun f : Euc d → ℂ => 𝓕⁻ f x) hcoe
  have hev : ∀ ξ : Euc d, n (-ξ) = n ξ := by
    intro ξ
    show (1 + 4 * Real.pi ^ 2 * ‖-ξ‖ ^ 2) ^ (α / 2) * chi ((3 : ℝ)⁻¹ • -ξ) =
      (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (α / 2) * chi ((3 : ℝ)⁻¹ • ξ)
    rw [norm_neg, smul_neg, cmxFB_chi_neg]
  have h := finv_conj_self n hev x
  rw [← hB] at h
  unfold Br
  exact ((Complex.conj_eq_iff_re).1 h).symm

lemma Br_continuous (α : ℝ) : Continuous (Br (d := d) α) :=
  Complex.continuous_re.comp (Bker (d := d) α).continuous

lemma Br_integrable (α : ℝ) : Integrable (Br (d := d) α) := by
  have := (Bker (d := d) α).integrable (μ := (volume : Measure (Euc d)))
  exact (Complex.reCLM.integrable_comp this)

lemma lintegral_enorm_Br_ne_top (α : ℝ) : ∫⁻ t, ‖Br (d := d) α t‖ₑ ≠ ⊤ :=
  (Br_integrable α).2.ne

lemma vanish_disjoint {G : SchwartzMap (Euc d) ℂ} (h : ∀ ξ : Euc d, ‖ξ‖ < 2 + 1 → 𝓕 (⇑G) ξ = 0) :
    Disjoint (tsupport (𝓕 (⇑G))) (closedBall (0 : Euc d) 2) := by
  rw [Set.disjoint_left]
  intro ξ hξ hball
  have hsub : tsupport (𝓕 (⇑G)) ⊆ {η : Euc d | 2 + 1 ≤ ‖η‖} := by
    apply closure_minimal _ (isClosed_le continuous_const continuous_norm)
    intro η hη
    show 2 + 1 ≤ ‖η‖
    by_contra hlt
    push Not at hlt
    exact Function.mem_support.1 hη (h η hlt)
  have h1 : 2 + 1 ≤ ‖ξ‖ := hsub hξ
  have h2 := mem_closedBall_zero_iff.1 hball
  linarith

/-- `⟨∇⟩^α a` is represented by `B_α ⋆ a` for band-limited `a ∈ L^p`. -/
theorem bessel_rep {p : ℝ} (hp : 1 < p) (α : ℝ) {a : Euc d → ℝ} (hac : Continuous a)
    (ha : MemLp a (ENNReal.ofReal p) volume) (hsupp : FourierSuppIn 2 a) :
    IsBesselRep α a (fun y => ∫ t, Br (d := d) α t * a (y + t)) := by
  have hP1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  haveI hH : (ENNReal.ofReal p).HolderConjugate (ENNReal.conjExponent (ENNReal.ofReal p)) :=
    ENNReal.HolderConjugate.conjExponent hP1
  have hacm : MemLp (fun x => ((a x : ℝ) : ℂ)) (ENNReal.ofReal p) volume := ha.ofReal
  have hUm : MemLp (fun y => ∫ t, Br (d := d) α t * a (y + t)) (ENNReal.ofReal p) volume := by
    refine lt_of_le_of_lt (eLpNorm_conv_le hp (Br_continuous α).measurable hac.measurable
      (lintegral_enorm_Br_ne_top α)) ?_
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 (lintegral_enorm_Br_ne_top α)) ha.eLpNorm_lt_top
  have hUc : MemLp (fun y => (((∫ t, Br (d := d) α t * a (y + t) : ℝ)) : ℂ)) (ENNReal.ofReal p)
      volume := hUm.ofReal
  intro φ
  -- the Schwartz function `T φ`
  set Tφ : SchwartzMap (Euc d) ℂ := 𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (bsym α) (𝓕 φ)) with hTφ
  have hTapp : ∀ x, Tφ x = 𝓕⁻ (fun ξ : Euc d => (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (α / 2) : ℝ) : ℂ) *
      𝓕 (⇑φ) ξ) x := by
    intro x
    rw [hTφ, SchwartzMap.fourierInv_coe]
    have : ⇑(SchwartzMap.smulLeftCLM ℂ (bsym α) (𝓕 φ)) = fun ξ : Euc d =>
        (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (α / 2) : ℝ) : ℂ) * 𝓕 (⇑φ) ξ := by
      funext ξ
      rw [SchwartzMap.smulLeftCLM_apply_apply (bsym_temperate α), smul_eq_mul,
        SchwartzMap.fourier_coe]
      rfl
    rw [this]
  have hFT : ∀ ξ : Euc d, 𝓕 (⇑Tφ) ξ = bsym α ξ * 𝓕 (⇑φ) ξ := by
    intro ξ
    have h1 : (𝓕 Tφ : SchwartzMap (Euc d) ℂ) = SchwartzMap.smulLeftCLM ℂ (bsym α) (𝓕 φ) :=
      FourierTransform.fourier_fourierInv_eq _
    have h2 := congrArg (fun T : SchwartzMap (Euc d) ℂ => T ξ) h1
    simp only [SchwartzMap.fourier_coe] at h2
    rw [h2, SchwartzMap.smulLeftCLM_apply_apply (bsym_temperate α), smul_eq_mul,
      SchwartzMap.fourier_coe]
  -- the cut-off part
  set Θ : SchwartzMap (Euc d) ℂ :=
    SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (Bker (d := d) α) φ with hΘ
  have hFΘ : ∀ ξ : Euc d, 𝓕 (⇑Θ) ξ = bsymCut α ξ * 𝓕 (⇑φ) ξ := by
    intro ξ
    rw [hΘ, fourier_conv_kernel]
    have : 𝓕 (⇑(Bker (d := d) α)) ξ = bsymCut α ξ := by
      rw [← SchwartzMap.fourier_coe, fourier_Bker]
      rfl
    rw [this]
  set G : SchwartzMap (Euc d) ℂ := Tφ - Θ with hG
  have hFG : ∀ ξ : Euc d, 𝓕 (⇑G) ξ = 𝓕 (⇑Tφ) ξ - 𝓕 (⇑Θ) ξ := by
    intro ξ
    rw [← SchwartzMap.fourier_coe, hG, sub_eq_add_neg, FourierAdd.fourier_add,
      FourierTransform.fourier_neg, add_apply, neg_apply,
      SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
    ring
  have hGvan : ∀ ξ : Euc d, ‖ξ‖ < 2 + 1 → 𝓕 (⇑G) ξ = 0 := by
    intro ξ hξ
    rw [hFG, hFT, hFΘ]
    have h3 : cmxFB_gL d 3 ξ = 1 := by
      have : ‖(3 : ℝ)⁻¹ • ξ‖ ≤ 1 := by
        rw [norm_smul, norm_inv, Real.norm_of_nonneg (by norm_num)]
        have : ‖ξ‖ < 3 := by linarith
        rw [inv_mul_le_iff₀ (by norm_num)]
        linarith
      simp [cmxFB_gL, cmxFB_chi_one this]
    simp [bsymCut, h3]
  have hGint : ∫ x, ((a x : ℝ) : ℂ) * G x = 0 := hsupp G (vanish_disjoint hGvan)
  have hI1 : Integrable (fun x => ((a x : ℝ) : ℂ) * Tφ x) := hacm.integrable_mul (Tφ.memLp (ENNReal.conjExponent (ENNReal.ofReal p)))
  have hI2 : Integrable (fun x => ((a x : ℝ) : ℂ) * Θ x) := hacm.integrable_mul (Θ.memLp (ENNReal.conjExponent (ENNReal.ofReal p)))
  have hI3 : Integrable (fun x => (((∫ t, Br (d := d) α t * a (x + t) : ℝ)) : ℂ) * φ x) :=
    hUc.integrable_mul (φ.memLp (ENNReal.conjExponent (ENNReal.ofReal p)))
  refine ⟨?_, hI3, ?_⟩
  · refine hI1.congr (Eventually.of_forall fun x => ?_)
    simp only [hTapp]
  · have hTexp : ∀ x, 𝓕⁻ (fun ξ : Euc d => (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (α / 2) : ℝ) : ℂ) *
        𝓕 (⇑φ) ξ) x = Tφ x := fun x => (hTapp x).symm
    simp_rw [hTexp]
    have hsplit : ∫ x, ((a x : ℝ) : ℂ) * Tφ x =
        (∫ x, ((a x : ℝ) : ℂ) * Θ x) + ∫ x, ((a x : ℝ) : ℂ) * G x := by
      have hI4 : Integrable (fun x => ((a x : ℝ) : ℂ) * G x) := hacm.integrable_mul (G.memLp (ENNReal.conjExponent (ENNReal.ofReal p)))
      rw [← integral_add hI2 hI4]
      congr 1
      funext x
      have : Tφ x = Θ x + G x := by simp [hG]
      rw [this]
      ring
    rw [hsplit, hGint, add_zero]
    have hpair := pairing_identity (p' := ENNReal.conjExponent (ENNReal.ofReal p)) hacm
      (Bker (d := d) α) φ
    have hΘx : ∀ x, Θ x = ∫ t, Bker (d := d) α t * φ (x - t) := fun x => conv_kernel_apply _ _ x
    simp_rw [hΘx]
    rw [hpair]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    rw [mul_comm]
    congr 1
    simp_rw [Bker_eq_ofReal]
    rw [← integral_complex_ofReal]
    congr 1
    funext t
    push_cast
    ring

/-! ### Assembly -/

theorem usample_core (hd : 1 ≤ d) (α : ℝ) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : Euc d → Euc d, Continuous u →
      MemLp (fun x => ‖u x‖) (ENNReal.ofReal p) volume →
      (∀ i, FourierSuppIn 2 (fun x => u x i)) →
      ∃ U : Euc d → Euc d,
        (∀ i, IsBesselRep α (fun x => u x i) (fun x => U x i)) ∧
        eLpNorm (fun x => ‖U x‖) (ENNReal.ofReal p) volume + cubeSupNorm p u ≤
          ENNReal.ofReal C * eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal p) volume := by
  obtain ⟨K, hK⟩ := exists_kernel_fourier_one (d := d) (2 + 1) (by norm_num)
  obtain ⟨S, hS, hcube⟩ := cubeSup_le hd hp K
  set κ : ℝ≥0∞ := ∫⁻ t, ‖Br (d := d) α t‖ₑ with hκ
  have hκt : κ ≠ ⊤ := lintegral_enorm_Br_ne_top α
  set E : ℝ≥0∞ := (d : ℝ≥0∞) * κ + (d : ℝ≥0∞) * S with hE
  have hEt : E ≠ ⊤ := by
    rw [hE]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by simp) hκt, ENNReal.mul_ne_top (by simp) hS⟩
  refine ⟨E.toReal + 1, by positivity, fun u hu hmem hsupp => ?_⟩
  have hP1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  have hcomp_mem : ∀ i : Fin d, MemLp (fun x => u x i) (ENNReal.ofReal p) volume := by
    intro i
    refine hmem.mono ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp hu).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    simp only [norm_norm]
    simpa using PiLp.norm_apply_le (u x) i
  have hcomp_cont : ∀ i : Fin d, Continuous (fun x => u x i) := fun i =>
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp hu
  set Ui : Fin d → Euc d → ℝ := fun i y => ∫ t, Br (d := d) α t * u (y + t) i with hUi
  set U : Euc d → Euc d := fun y => WithLp.toLp 2 (fun i => Ui i y) with hU
  have hUapp : ∀ i y, U y i = Ui i y := fun i y => by simp [hU]
  refine ⟨U, fun i => ?_, ?_⟩
  · have := bessel_rep hp α (hcomp_cont i) (hcomp_mem i) (hsupp i)
    simpa [hUapp, hUi] using this
  · -- the norm bound
    have hrep : ∀ (i : Fin d) (y : Euc d), ((u y i : ℝ) : ℂ) = ∫ t, K t * ((u (y + t) i : ℝ) : ℂ) :=
      fun i y => repr_everywhere hp K hK (hcomp_cont i) (hcomp_mem i) (hsupp i) y
    have h1 := hcube u hu hrep
    have hUm : ∀ i : Fin d, AEStronglyMeasurable (fun y => Ui i y) volume := fun i =>
      conv_aestronglyMeasurable (Br_continuous α).measurable (hcomp_cont i).measurable
    have hUi_le : ∀ i : Fin d, eLpNorm (fun y => Ui i y) (ENNReal.ofReal p) volume ≤
        κ * eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal p) volume := by
      intro i
      refine (eLpNorm_conv_le hp (Br_continuous α).measurable (hcomp_cont i).measurable hκt).trans ?_
      gcongr
      exact eLpNorm_mono (hcomp_cont i).aestronglyMeasurable fun x => by
        simpa using PiLp.norm_apply_le (u x) i
    have hUnorm_meas : AEStronglyMeasurable (fun x => ‖U x‖) volume := by
      have : AEMeasurable U volume :=
        (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp_aemeasurable
          (AEMeasurable.of_eval fun i => (hUm i).aemeasurable)
      exact this.aestronglyMeasurable.norm
    have h2 : eLpNorm (fun x => ‖U x‖) (ENNReal.ofReal p) volume ≤
        ∑ i : Fin d, eLpNorm (fun y => Ui i y) (ENNReal.ofReal p) volume := by
      calc eLpNorm (fun x => ‖U x‖) (ENNReal.ofReal p) volume
          ≤ eLpNorm (fun x => ∑ i : Fin d, ‖Ui i x‖) (ENNReal.ofReal p) volume := by
            refine eLpNorm_mono_real hUnorm_meas fun x => ?_
            rw [norm_norm]
            refine (norm_le_sum_abs (U x)).trans (le_of_eq ?_)
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hUapp, Real.norm_eq_abs]
        _ = eLpNorm (∑ i : Fin d, fun x => ‖Ui i x‖) (ENNReal.ofReal p) volume := by
            congr 1
            funext x
            simp [Finset.sum_apply]
        _ ≤ ∑ i : Fin d, eLpNorm (fun x => ‖Ui i x‖) (ENNReal.ofReal p) volume :=
            eLpNorm_sum_le hP1
        _ = ∑ i : Fin d, eLpNorm (fun y => Ui i y) (ENNReal.ofReal p) volume := by
            refine Finset.sum_congr rfl fun i _ => ?_
            exact eLpNorm_norm _ (hUm i)
    have h3 : eLpNorm (fun x => ‖U x‖) (ENNReal.ofReal p) volume ≤
        (d : ℝ≥0∞) * (κ * eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal p) volume) := by
      refine h2.trans ?_
      calc ∑ i : Fin d, eLpNorm (fun y => Ui i y) (ENNReal.ofReal p) volume
          ≤ ∑ _i : Fin d, κ * eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal p) volume :=
            Finset.sum_le_sum fun i _ => hUi_le i
        _ = _ := by simp
    have hEC : E ≤ ENNReal.ofReal (E.toReal + 1) := by
      calc E = ENNReal.ofReal E.toReal := (ENNReal.ofReal_toReal hEt).symm
        _ ≤ ENNReal.ofReal (E.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)
    calc eLpNorm (fun x => ‖U x‖) (ENNReal.ofReal p) volume + cubeSupNorm p u
        ≤ (d : ℝ≥0∞) * (κ * eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal p) volume) +
            (d : ℝ≥0∞) * S * eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal p) volume :=
          add_le_add h3 h1
      _ = E * eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal p) volume := by
          rw [hE]; ring
      _ ≤ ENNReal.ofReal (E.toReal + 1) * eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal p) volume := by
          gcongr

end HRS.Commutator.Whole.SAMP2
