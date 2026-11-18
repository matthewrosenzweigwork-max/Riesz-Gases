import HRS.Commutator.Whole.LocalAuxSAMP2Fourier
import HRS.Commutator.Whole.LocalAuxKR3
import HRS.Commutator.Whole.ExternalAuxHLS5

/-!
# CMX-SAMP (`potentialSobolev`), part 2: `∇g_{≤1} * σ` as an inverse Fourier integral

`gloForce_i = 𝓕⁻[M_i]`, `M_i(ξ) = c ξ_i|ξ|^{-(d-s)} χ(ξ)` (an `L¹` function), and for a finite
measure `σ`: `(∇g_{≤1} * σ)_i = 𝓕⁻[M_i σ̂]`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole.SAMP2

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

/-- The symbol `M_i(ξ) = c ξ_i |ξ|^{-(d-s)} χ(ξ)`. -/
def Msym (d : ℕ) (s : ℝ) (c : ℂ) (i : Fin d) (ξ : Euc d) : ℂ :=
  c * cmxMY_hi d s i ξ * cmxFB_gL d 1 ξ

/-- `ξ ↦ e^{2πi ⟨ξ,x⟩} χ(ξ)` as a Schwartz function. -/
def modS (x : Euc d) : SchwartzMap (Euc d) ℂ :=
  (show HasCompactSupport (fun ξ : Euc d => Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) *
      Complex.I) * cmxFB_gL d 1 ξ) from
    (cmxFB_gL_compact (d := d) (by norm_num : (0 : ℝ) < 1)).mul_left).toSchwartzMap
    (by
      refine ContDiff.mul ?_ (cmxFB_gL_contDiff 1)
      refine Complex.contDiff_exp.comp (ContDiff.mul ?_ contDiff_const)
      exact Complex.ofRealCLM.contDiff.comp
        (contDiff_const.mul (contDiff_id.inner ℝ contDiff_const)))

lemma modS_apply (x ξ : Euc d) : modS x ξ =
    Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) * cmxFB_gL d 1 ξ := rfl

lemma fourier_modS (x y : Euc d) :
    𝓕 (⇑(modS x)) y = cmxFB_Om (d := d) 1 one_pos (x - y) := by
  have h : (⇑(modS x) : Euc d → ℂ) = fun ξ => Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) *
      Complex.I) * cmxFB_gL d 1 ξ := funext (modS_apply x)
  rw [h, cmxHLS_modulation, cmxFB_Om_apply, cmxFB_finv_eq]

lemma Msym_norm_le (hd : 3 ≤ d) (hs0 : 0 ≤ s) (c : ℂ) (i : Fin d) (ξ : Euc d) (hξ : ξ ≠ 0) :
    ‖Msym d s c i ξ‖ ≤ ‖c‖ * (‖ξ‖ ^ (1 - ((d : ℝ) - s)) *
      ‖cmxFB_G (d := d) 1 one_pos ξ‖) := by
  have hxn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hxi : |ξ i| ≤ ‖ξ‖ := by simpa using PiLp.norm_apply_le ξ i
  have h1 : ‖cmxMY_hi d s i ξ‖ ≤ ‖ξ‖ ^ (1 - ((d : ℝ) - s)) := by
    unfold cmxMY_hi
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg ξ) _)]
    calc |ξ i| * ‖ξ‖ ^ (-((d : ℝ) - s)) ≤ ‖ξ‖ * ‖ξ‖ ^ (-((d : ℝ) - s)) := by gcongr
      _ = ‖ξ‖ ^ (1 - ((d : ℝ) - s)) := by
          rw [show 1 - ((d : ℝ) - s) = 1 + -((d : ℝ) - s) by ring, Real.rpow_add hxn, Real.rpow_one]
  unfold Msym
  rw [norm_mul, norm_mul, cmxFB_G_apply]
  calc ‖c‖ * ‖cmxMY_hi d s i ξ‖ * ‖cmxFB_gL d 1 ξ‖
      ≤ ‖c‖ * ‖ξ‖ ^ (1 - ((d : ℝ) - s)) * ‖cmxFB_gL d 1 ξ‖ := by gcongr
    _ = _ := by ring

lemma Msym_integrable (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (c : ℂ) (i : Fin d) :
    Integrable (Msym d s c i) := by
  have hd1 : 1 ≤ d := by omega
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 := integrable_norm_rpow_mul_schwartz hd1 (s := 1 - ((d : ℝ) - s)) (by linarith)
    (by linarith) (cmxFB_G (d := d) 1 one_pos)
  have hm : Measurable (Msym d s c i) := by
    unfold Msym cmxMY_hi cmxFB_gL
    refine Measurable.mul (Measurable.mul measurable_const ?_) ?_
    · exact Complex.measurable_ofReal.comp (((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.measurable).mul
        (measurable_norm.pow_const _))
    · exact Complex.measurable_ofReal.comp (cmxFB_chi_contDiff.continuous.measurable.comp
        (measurable_const_smul _))
  refine (h1.const_mul ‖c‖).mono' hm.aestronglyMeasurable ?_
  filter_upwards [ae_ne_zero_euc hd1] with ξ hξ
  exact Msym_norm_le hd hs0 c i ξ hξ

lemma glo_eq_finv (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {c : ℂ}
    (hc : ∀ (i : Fin d) (Φ : SchwartzMap (Euc d) ℂ),
      ∫ x : Euc d, ((kernGrad s x i : ℝ) : ℂ) * 𝓕 (⇑Φ) x =
        c * ∫ ξ : Euc d, (((ξ i) * ‖ξ‖ ^ (-((d : ℝ) - s)) : ℝ) : ℂ) * Φ ξ)
    (i : Fin d) (x : Euc d) :
    ((gloForce s x i : ℝ) : ℂ) = 𝓕⁻ (Msym d s c i) x := by
  have h1 := cmxMY_glo_component hd hs0 hsd x i
  have h2 : ∀ y, cmxFB_Om (d := d) 1 one_pos (x - y) * ((kernGrad s y i : ℝ) : ℂ) =
      ((kernGrad s y i : ℝ) : ℂ) * 𝓕 (⇑(modS x)) y := by
    intro y
    rw [fourier_modS, mul_comm]
  simp_rw [h2] at h1
  rw [h1, hc i (modS x), Real.fourierInv_eq', ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul, modS_apply, Msym, cmxMY_hi]
  ring

lemma finv_integral_meas (μ : Measure (Euc d)) [IsFiniteMeasure μ] (M : Euc d → ℂ)
    (hM : Integrable M) (x : Euc d) :
    ∫ y, 𝓕⁻ M (x - y) ∂μ = ∫ ξ, M ξ * Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) *
        Complex.I) * ∫ y, Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ y ξ : ℝ))) ∂μ := by
  have e1 : ∀ y, 𝓕⁻ M (x - y) = ∫ ξ, Complex.exp (((2 * Real.pi * inner ℝ ξ (x - y) : ℝ) : ℂ) *
      Complex.I) * M ξ := by
    intro y
    rw [Real.fourierInv_eq']
    simp only [smul_eq_mul]
  simp_rw [e1]
  have hint : Integrable (Function.uncurry fun (y ξ : Euc d) =>
      Complex.exp (((2 * Real.pi * inner ℝ ξ (x - y) : ℝ) : ℂ) * Complex.I) * M ξ)
      (μ.prod volume) := by
    have hg : Integrable (fun z : Euc d × Euc d => (1 : ℝ) * ‖M z.2‖) (μ.prod volume) :=
      Integrable.mul_prod (integrable_const (1 : ℝ)) hM.norm
    refine hg.mono' ?_ (Eventually.of_forall fun z => ?_)
    · have h1 : Continuous fun z : Euc d × Euc d =>
          Complex.exp (((2 * Real.pi * inner ℝ z.2 (x - z.1) : ℝ) : ℂ) * Complex.I) := by
        fun_prop
      exact h1.aestronglyMeasurable.mul
        (hM.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
    · obtain ⟨y, ξ⟩ := z
      simp only [Function.uncurry_apply_pair, norm_mul, one_mul]
      rw [Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  beta_reduce
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  beta_reduce
  have key : Complex.exp (((2 * Real.pi * inner ℝ ξ (x - y) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) *
        Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ y ξ : ℝ))) := by
    rw [← Complex.exp_add]
    congr 1
    rw [inner_sub_right, real_inner_comm y ξ]
    push_cast
    ring
  rw [key]
  ring

/-- The Fourier transform of a finite measure. -/
def fm (μ : Measure (Euc d)) (ξ : Euc d) : ℂ :=
  ∫ y, Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ y ξ : ℝ))) ∂μ

lemma norm_exp_neg_le (y ξ : Euc d) :
    ‖Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ y ξ : ℝ)))‖ = 1 := by
  have : -(2 * (Real.pi : ℂ) * Complex.I * ((inner ℝ y ξ : ℝ) : ℂ)) =
      ((-(2 * Real.pi * inner ℝ y ξ) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma fm_continuous (μ : Measure (Euc d)) [IsFiniteMeasure μ] : Continuous (fm μ) := by
  unfold fm
  refine continuous_of_dominated (bound := fun _ => 1) (fun ξ => ?_) (fun ξ => ?_)
    (integrable_const _) ?_
  · exact (by fun_prop : Continuous fun y : Euc d =>
      Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ y ξ : ℝ)))).aestronglyMeasurable
  · exact Eventually.of_forall fun y => (norm_exp_neg_le y ξ).le
  · exact Eventually.of_forall fun y => by fun_prop

lemma norm_fm_le (μ : Measure (Euc d)) [IsFiniteMeasure μ] (ξ : Euc d) :
    ‖fm μ ξ‖ ≤ μ.real Set.univ := by
  unfold fm
  have := norm_integral_le_of_norm_le_const (μ := μ) (C := 1)
    (f := fun y => Complex.exp (-(2 * Real.pi * Complex.I * (inner ℝ y ξ : ℝ))))
    (Eventually.of_forall fun y => (norm_exp_neg_le y ξ).le)
  simpa using this

lemma glo_bdd (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ B : ℝ, ∀ z : Euc d, ‖gloForce s z‖ ≤ B := by
  have hK := cmxFB_kerOK hd hs0 hsd
  obtain ⟨B, hB⟩ := cmxFB_Phi_bdd hK (cmxFB_B0 d) (cmxFB_Om (d := d) 1 one_pos)
  exact ⟨B, fun z => by rw [cmxFB_gloForce_eq]; exact hB z⟩

lemma finv_meas_integrable (μ : Measure (Euc d)) [IsFiniteMeasure μ] (M : Euc d → ℂ)
    (hM : Integrable M) (x : Euc d) :
    Integrable (fun ξ => M ξ * Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) *
      fm μ ξ) := by
  refine (hM.norm.mul_const (μ.real Set.univ)).mono' ?_ (Eventually.of_forall fun ξ => ?_)
  · have h1 : Continuous fun ξ : Euc d =>
        Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) := by fun_prop
    exact (hM.1.mul h1.aestronglyMeasurable).mul (fm_continuous μ).aestronglyMeasurable
  · rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact mul_le_mul_of_nonneg_left (norm_fm_le μ ξ) (norm_nonneg _)

lemma conv_component (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {c : ℂ}
    (hc : ∀ (i : Fin d) (Φ : SchwartzMap (Euc d) ℂ),
      ∫ x : Euc d, ((kernGrad s x i : ℝ) : ℂ) * 𝓕 (⇑Φ) x =
        c * ∫ ξ : Euc d, (((ξ i) * ‖ξ‖ ^ (-((d : ℝ) - s)) : ℝ) : ℂ) * Φ ξ)
    (σ : SMeas d) (hf : σ.IsFinite) (x : Euc d) (i : Fin d) :
    ((σ.convForce (gloForce s) x i : ℝ) : ℂ) =
      𝓕⁻ (fun ξ => Msym d s c i ξ * σ.fourier ξ) x := by
  obtain ⟨hp, hn⟩ := hf
  haveI := hp
  haveI := hn
  have hM := Msym_integrable hd hs0 hsd c i
  obtain ⟨B, hB⟩ := glo_bdd hd hs0 hsd
  have hcont := cmxMY_gloForce_continuous hd hs0 hsd (s := s)
  have hint : ∀ μ : Measure (Euc d), IsFiniteMeasure μ →
      Integrable (fun y => gloForce s (x - y)) μ := by
    intro μ hμ
    exact (integrable_const B).mono'
      (hcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun y => hB _)
  have hcomp : ∀ μ : Measure (Euc d), IsFiniteMeasure μ →
      (∫ y, gloForce s (x - y) ∂μ) i = ∫ y, gloForce s (x - y) i ∂μ := by
    intro μ hμ
    have := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).integral_comp_comm (hint μ hμ)
    simpa using this.symm
  have h1 : σ.convForce (gloForce s) x i =
      ∫ y, gloForce s (x - y) i ∂σ.pos - ∫ y, gloForce s (x - y) i ∂σ.neg := by
    unfold SMeas.convForce SMeas.intV
    rw [PiLp.sub_apply, hcomp _ hp, hcomp _ hn]
  have hF : ∀ μ : Measure (Euc d), IsFiniteMeasure μ →
      (((∫ y, gloForce s (x - y) i ∂μ : ℝ)) : ℂ) =
        ∫ ξ, Msym d s c i ξ * Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) *
          fm μ ξ := by
    intro μ hμ
    rw [← integral_complex_ofReal]
    simp_rw [glo_eq_finv hd hs0 hsd hc i]
    exact finv_integral_meas μ _ hM x
  rw [h1, Complex.ofReal_sub, hF _ hp, hF _ hn, ← integral_sub (finv_meas_integrable _ _ hM x)
    (finv_meas_integrable _ _ hM x), Real.fourierInv_eq']
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul, SMeas.fourier, fm]
  ring

end HRS.Commutator.Whole.SAMP2
