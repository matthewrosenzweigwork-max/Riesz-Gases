import HRS.Commutator.Whole.LocalAuxKR
import HRS.Commutator.Whole.LocalAuxFC2
import HRS.Commutator.Whole.YoungAux
import HRS.Commutator.Whole.RieszAux

/-!
# CMX-KR auxiliary (2): the pairing of `∇g_{>1}` with the Fourier transform of a test function

`cmxMY_ghi_pairing`: `∫ (∇g_{>1})_i 𝓕Φ = ∫ (∇g)_i 𝓕((1-χ)Φ)` (Fubini and `ψ * 𝓕Φ = 𝓕(χΦ)`).
Names prefixed `cmxMY_`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ}

lemma cmxMY_fourier_fourier (Φ : SchwartzMap (Euc d) ℂ) (x : Euc d) :
    𝓕 (⇑(𝓕 Φ : SchwartzMap (Euc d) ℂ)) x = Φ (-x) := by
  have h : (𝓕⁻ (𝓕 Φ : SchwartzMap (Euc d) ℂ) : SchwartzMap (Euc d) ℂ) = Φ :=
    FourierTransform.fourierInv_fourier_eq Φ
  have h2 : (𝓕⁻ (𝓕 Φ : SchwartzMap (Euc d) ℂ) : SchwartzMap (Euc d) ℂ) (-x) = Φ (-x) := by rw [h]
  rw [← h2, SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, neg_neg]

/-- `χ Φ` as a Schwartz function. -/
def cmxMY_chiPhi (Φ : SchwartzMap (Euc d) ℂ) : SchwartzMap (Euc d) ℂ :=
  (show HasCompactSupport (fun ξ : Euc d => ((chi ξ : ℝ) : ℂ) * Φ ξ) from by
    have : HasCompactSupport (fun ξ : Euc d => ((chi ξ : ℝ) : ℂ)) := by
      have := (chiBump d).hasCompactSupport
      exact this.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
    exact this.mul_right).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp cmxFB_chi_contDiff |>.mul Φ.smooth')

lemma cmxMY_W (Φ : SchwartzMap (Euc d) ℂ) (x : Euc d) :
    𝓕 (⇑(Φ - cmxMY_chiPhi Φ)) x =
      𝓕 (⇑Φ) x - ∫ t : Euc d, cmxFB_Om (d := d) 1 one_pos t * 𝓕 (⇑Φ) (x - t) := by
  set Ω : SchwartzMap (Euc d) ℂ := cmxFB_Om (d := d) 1 one_pos with hΩ
  set Ψ : SchwartzMap (Euc d) ℂ := 𝓕 Φ with hΨ
  set Φ' : SchwartzMap (Euc d) ℂ := Φ - cmxMY_chiPhi Φ with hΦ'
  set E1 : SchwartzMap (Euc d) ℂ :=
    Ψ - SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) Ω Ψ with hE1
  set E2 : SchwartzMap (Euc d) ℂ := 𝓕 Φ' with hE2
  have hΩF : ∀ ξ : Euc d, 𝓕 (⇑Ω) ξ = ((chi ξ : ℝ) : ℂ) := by
    intro ξ
    rw [← SchwartzMap.fourier_coe, hΩ, cmxFB_fourier_Om, cmxFB_G_apply]
    simp [cmxFB_gL]
  have hF1 : ∀ ξ : Euc d, 𝓕 (⇑E1) ξ = (1 - ((chi ξ : ℝ) : ℂ)) * Φ (-ξ) := by
    intro ξ
    rw [hE1, fourier_test_sub Ω Ψ ξ, hΩF, hΨ, cmxMY_fourier_fourier]
  have hF2 : ∀ ξ : Euc d, 𝓕 (⇑E2) ξ = (1 - ((chi ξ : ℝ) : ℂ)) * Φ (-ξ) := by
    intro ξ
    rw [hE2, cmxMY_fourier_fourier]
    simp only [hΦ', cmxMY_chiPhi, sub_apply]
    show Φ (-ξ) - ((chi (-ξ) : ℝ) : ℂ) * Φ (-ξ) = _
    rw [cmxFB_chi_neg]; ring
  have hE : E1 = E2 := by
    have h1 : (𝓕 E1 : SchwartzMap (Euc d) ℂ) = 𝓕 E2 := by
      ext ξ
      rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, hF1, hF2]
    have h2 : (𝓕⁻ (𝓕 E1 : SchwartzMap (Euc d) ℂ) : SchwartzMap (Euc d) ℂ) = E1 :=
      FourierTransform.fourierInv_fourier_eq E1
    have h3 : (𝓕⁻ (𝓕 E2 : SchwartzMap (Euc d) ℂ) : SchwartzMap (Euc d) ℂ) = E2 :=
      FourierTransform.fourierInv_fourier_eq E2
    rw [← h2, ← h3, h1]
  have := congrArg (fun T : SchwartzMap (Euc d) ℂ => T x) hE
  rw [hE2, SchwartzMap.fourier_coe] at this
  rw [← this, hE1, sub_apply, conv_kernel_apply]
  rfl

lemma cmxMY_fubini (K : Euc d → Euc d) (hK : cmxFB_KerOK K) (ψ Ψ : SchwartzMap (Euc d) ℂ)
    (i : Fin d) :
    Integrable (fun p : Euc d × Euc d => ψ (p.1 - p.2) * ((K p.2 i : ℝ) : ℂ) * Ψ p.1)
      (volume.prod volume) := by
  obtain ⟨C, hC0, hC⟩ := cmxFB_schwartz_a ψ
  obtain ⟨c2, hc2⟩ := cmxFB_dom hK (fun z => ψ z) C hC0 hC
  set cst : ℝ := C * (∫ y in ball (0 : Euc d) 1, ‖K y‖) + c2 * (∫ y, cmxFB_a d y) with hcst
  have hKi : AEStronglyMeasurable (fun y : Euc d => ((K y i : ℝ) : ℂ)) volume :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hK.meas)
  have hmeas : AEStronglyMeasurable
      (fun p : Euc d × Euc d => ψ (p.1 - p.2) * ((K p.2 i : ℝ) : ℂ) * Ψ p.1) (volume.prod volume) := by
    have h1 : Continuous fun p : Euc d × Euc d => ψ (p.1 - p.2) := ψ.continuous.comp (continuous_fst.sub continuous_snd)
    have h2 : Continuous fun p : Euc d × Euc d => Ψ p.1 := Ψ.continuous.comp continuous_fst
    have hK2 : AEStronglyMeasurable (fun p : Euc d × Euc d => ((K p.2 i : ℝ) : ℂ))
        (volume.prod volume) :=
      hKi.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have h3 := h1.aestronglyMeasurable (μ := volume.prod volume)
    have h4 := h2.aestronglyMeasurable (μ := volume.prod volume)
    exact (h3.mul hK2).mul h4
  have hbd : ∀ x y : Euc d, ‖ψ (x - y) * ((K y i : ℝ) : ℂ) * Ψ x‖ ≤ cmxFB_bd K C c2 x y * ‖Ψ x‖ := by
    intro x y
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : ‖ψ (x - y)‖ * |K y i| ≤ cmxFB_bd K C c2 x y := by
      refine le_trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) (hc2 x x (by simp) y)
      simpa using PiLp.norm_apply_le (K y) i
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  rw [integrable_prod_iff hmeas]
  refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
  · refine ((cmxFB_bd_integrable hK C c2 x).mul_const ‖Ψ x‖).mono' ?_ (Eventually.of_forall (hbd x))
    have h1 : Continuous fun y : Euc d => ψ (x - y) := ψ.continuous.comp (continuous_const.sub continuous_id)
    have h2 : AEStronglyMeasurable (fun _ : Euc d => Ψ x) (volume : Measure (Euc d)) :=
      aestronglyMeasurable_const
    exact (h1.aestronglyMeasurable.mul hKi).mul h2
  · refine (Ψ.integrable.norm.const_mul cst).mono' ?_ ?_
    · exact hmeas.norm.integral_prod_right'
    · refine Eventually.of_forall fun x => ?_
      simp only
      rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
      calc ∫ y, ‖ψ (x - y) * ((K y i : ℝ) : ℂ) * Ψ x‖ ≤ ∫ y, cmxFB_bd K C c2 x y * ‖Ψ x‖ :=
            integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _)
              ((cmxFB_bd_integrable hK C c2 x).mul_const ‖Ψ x‖) (Eventually.of_forall (hbd x))
        _ = cst * ‖Ψ x‖ := by rw [integral_mul_const, cmxFB_bd_integral hK]

lemma cmxMY_int_KS (K : Euc d → Euc d) (hK : cmxFB_KerOK K) (S : SchwartzMap (Euc d) ℂ) (i : Fin d) :
    Integrable (fun x : Euc d => ((K x i : ℝ) : ℂ) * S x) := by
  obtain ⟨M, hM⟩ := hK.far
  obtain ⟨C0, hC0, hC⟩ := cmxFB_decay S 0
  have hKi : AEStronglyMeasurable (fun y : Euc d => ((K y i : ℝ) : ℂ)) volume :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hK.meas)
  have hD : Integrable (fun x : Euc d =>
      C0 * (ball (0 : Euc d) 1).indicator (fun y => ‖K y‖) x + |M| * ‖S x‖) :=
    (((integrable_indicator_iff measurableSet_ball).2 hK.loc.norm).const_mul C0).add
      (S.integrable.norm.const_mul |M|)
  refine hD.mono' (hKi.mul S.continuous.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hKx : |K x i| ≤ ‖K x‖ := by simpa using PiLp.norm_apply_le (K x) i
  have hSx : ‖S x‖ ≤ C0 := by simpa using hC x
  by_cases hx : x ∈ ball (0 : Euc d) 1
  · rw [Set.indicator_of_mem hx]
    have : |K x i| * ‖S x‖ ≤ ‖K x‖ * C0 := mul_le_mul hKx hSx (norm_nonneg _) (norm_nonneg _)
    nlinarith [mul_nonneg (abs_nonneg M) (norm_nonneg (S x))]
  · rw [Set.indicator_of_notMem hx]
    have hx1 : 1 ≤ ‖x‖ := by simpa [mem_ball_zero_iff] using hx
    have : |K x i| ≤ |M| := hKx.trans ((hM x hx1).trans (le_abs_self M))
    have := mul_le_mul_of_nonneg_right this (norm_nonneg (S x))
    nlinarith

lemma cmxMY_glo_component (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2)
    (x : Euc d) (i : Fin d) :
    ((gloForce s x i : ℝ) : ℂ) =
      ∫ y : Euc d, cmxFB_Om (d := d) 1 one_pos (x - y) * ((kernGrad s y i : ℝ) : ℂ) := by
  have hK := cmxFB_kerOK hd hs0 hsd
  have hint := cmxFB_Phi_integrable hK (cmxFB_B0 d) (cmxFB_Om (d := d) 1 one_pos) x
  have h1 := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).integral_comp_comm hint
  have h2 : gloForce s x = ∫ y, cmxFB_B0 d (cmxFB_Om (d := d) 1 one_pos (x - y)) (kernGrad s y) := by
    rw [cmxFB_gloForce_eq]; rfl
  have h3 : gloForce s x i = ∫ y : Euc d, psiL 1 (x - y) * kernGrad s y i := by
    rw [h2]
    show (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) _ = _
    rw [← h1]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp [cmxFB_B0_apply, cmxFB_Om_apply]
  rw [h3, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [cmxFB_Om_apply]

lemma cmxMY_ghi_pairing (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (i : Fin d)
    (Φ : SchwartzMap (Euc d) ℂ) :
    ∫ x : Euc d, ((ghiForce s x i : ℝ) : ℂ) * 𝓕 (⇑Φ) x =
      ∫ x : Euc d, ((kernGrad s x i : ℝ) : ℂ) * 𝓕 (⇑(Φ - cmxMY_chiPhi Φ)) x := by
  have hK := cmxFB_kerOK hd hs0 hsd
  set Ω : SchwartzMap (Euc d) ℂ := cmxFB_Om (d := d) 1 one_pos with hΩ
  set Ψ : SchwartzMap (Euc d) ℂ := 𝓕 Φ with hΨ
  have hΨf : ⇑Ψ = 𝓕 (⇑Φ) := rfl
  rw [← hΨf]
  have hΩeven : ∀ z : Euc d, Ω (-z) = Ω z := by
    intro z; simp only [hΩ, cmxFB_Om_apply, cmxFB_psiL_neg]
  -- integrability facts
  have hI1 : Integrable (fun x : Euc d => ((kernGrad s x i : ℝ) : ℂ) * Ψ x) :=
    cmxMY_int_KS _ hK Ψ i
  have hgloc : Continuous (gloForce s : Euc d → Euc d) := by
    have : ContDiff ℝ ∞ (gloForce s : Euc d → Euc d) := by
      rw [cmxFB_gloForce_eq, contDiff_infty]
      exact fun n => cmxFB_Phi_contDiff hK n _ _
    exact this.continuous
  obtain ⟨B, hB⟩ := cmxFB_Phi_bdd hK (cmxFB_B0 d) Ω
  have hI2 : Integrable (fun x : Euc d => ((gloForce s x i : ℝ) : ℂ) * Ψ x) := by
    refine (Ψ.integrable.norm.const_mul |B|).mono' ?_ (Eventually.of_forall fun x => ?_)
    · exact (Complex.continuous_ofReal.comp ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp
        hgloc)).aestronglyMeasurable.mul Ψ.continuous.aestronglyMeasurable
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 : |gloForce s x i| ≤ |B| := by
        have : ‖gloForce s x‖ ≤ B := by
          rw [cmxFB_gloForce_eq]; exact hB x
        exact (by simpa using PiLp.norm_apply_le (gloForce s x) i : |gloForce s x i| ≤ ‖gloForce s x‖).trans
          (this.trans (le_abs_self B))
      exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  -- split
  have hsplit : ∫ x : Euc d, ((ghiForce s x i : ℝ) : ℂ) * Ψ x =
      (∫ x : Euc d, ((kernGrad s x i : ℝ) : ℂ) * Ψ x) - ∫ x : Euc d, ((gloForce s x i : ℝ) : ℂ) * Ψ x := by
    rw [← integral_sub hI1 hI2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [ghiForce, PiLp.sub_apply]
    push_cast; ring
  -- swap
  have hswap : ∫ x : Euc d, ((gloForce s x i : ℝ) : ℂ) * Ψ x =
      ∫ y : Euc d, ((kernGrad s y i : ℝ) : ℂ) * ∫ x : Euc d, Ω (x - y) * Ψ x := by
    have h1 : ∀ x : Euc d, ((gloForce s x i : ℝ) : ℂ) * Ψ x =
        ∫ y : Euc d, Ω (x - y) * ((kernGrad s y i : ℝ) : ℂ) * Ψ x := by
      intro x
      rw [cmxMY_glo_component hd hs0 hsd x i, ← integral_mul_const]
    simp_rw [h1]
    rw [integral_integral_swap (f := fun x y => Ω (x - y) * ((kernGrad s y i : ℝ) : ℂ) * Ψ x)
      (cmxMY_fubini _ hK Ω Ψ i)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [← integral_const_mul]
    congr 1; ext x; ring
  have hconv : ∀ y : Euc d, ∫ x : Euc d, Ω (x - y) * Ψ x = ∫ t : Euc d, Ω t * Ψ (y - t) := by
    intro y
    have := integral_sub_left_eq_self (fun t : Euc d => Ω t * Ψ (y - t)) volume y
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [sub_sub_cancel]
    rw [← hΩeven (x - y), neg_sub]
  have hI3 : Integrable (fun y : Euc d => ((kernGrad s y i : ℝ) : ℂ) * ∫ t : Euc d, Ω t * Ψ (y - t)) := by
    have := cmxMY_int_KS _ hK (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) Ω Ψ) i
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp only [conv_kernel_apply]
  rw [hsplit, hswap]
  simp_rw [hconv]
  rw [← integral_sub hI1 hI3]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have := cmxMY_W Φ y
  beta_reduce
  rw [this]
  show _ = _ * (Ψ y - ∫ t : Euc d, Ω t * Ψ (y - t))
  ring

end HRS.Commutator.Whole
