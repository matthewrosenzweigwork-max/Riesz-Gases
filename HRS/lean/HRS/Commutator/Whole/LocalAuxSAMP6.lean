import HRS.Commutator.Whole.LocalAuxSAMP5
import HRS.Commutator.Whole.ExternalAuxHLS12
import HRS.Commutator.Whole.YoungAux

/-!
# Translation, Fubini for convolutions, and the representation of `k * v` (packet CMX-SAMP, file 6)
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff

noncomputable section

namespace HRS.Commutator.Whole.SAMP1

open HRS HRS.Whole HRS.Commutator.Whole

variable {d : ℕ}

/-- The Schwartz translate `x ↦ φ (x + y)`. -/
def shiftS (y : Euc d) (φ : SchwartzMap (Euc d) ℂ) : SchwartzMap (Euc d) ℂ :=
  SchwartzMap.compSubConstCLM ℂ (-y) φ

lemma shiftS_apply (y : Euc d) (φ : SchwartzMap (Euc d) ℂ) (x : Euc d) :
    shiftS y φ x = φ (x + y) := by
  simp [shiftS]

lemma fourier_shiftS (y : Euc d) (φ : SchwartzMap (Euc d) ℂ) (ξ : Euc d) :
    𝓕 (⇑(shiftS y φ)) ξ =
      Complex.exp (((2 * Real.pi * inner ℝ y ξ : ℝ) : ℂ) * Complex.I) * 𝓕 (⇑φ) ξ := by
  have h : (⇑(shiftS y φ) : Euc d → ℂ) = fun x => φ (x + y) := funext (shiftS_apply y φ)
  rw [h, Real.fourier_eq', Real.fourier_eq', ← integral_const_mul]
  set g : Euc d → ℂ := fun v =>
    Complex.exp (((-2 * Real.pi * inner ℝ (v - y) ξ : ℝ) : ℂ) * Complex.I) • φ v with hg
  have e1 : ∫ v : Euc d, Complex.exp (((-2 * Real.pi * inner ℝ v ξ : ℝ) : ℂ) * Complex.I) •
      φ (v + y) = ∫ v : Euc d, g (v + y) := by
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp [hg]
  rw [e1, integral_add_right_eq_self g y]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [hg, smul_eq_mul]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  rw [inner_sub_left]; push_cast; ring

/-- `T_a φ := 𝓕⁻[a · 𝓕φ]` commutes with translations. -/
lemma Tm_shiftS (a : Euc d → ℂ) (y : Euc d) (φ : SchwartzMap (Euc d) ℂ) (x : Euc d) :
    𝓕⁻ (fun ξ => a ξ * 𝓕 (⇑(shiftS y φ)) ξ) x = 𝓕⁻ (fun ξ => a ξ * 𝓕 (⇑φ) ξ) (x + y) := by
  rw [Real.fourierInv_eq', Real.fourierInv_eq']
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [fourier_shiftS, smul_eq_mul]
  have : Complex.exp (((2 * Real.pi * inner ℝ ξ (x + y) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((2 * Real.pi * inner ℝ y ξ : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add, inner_add_right, real_inner_comm ξ y]
    congr 1; push_cast; ring
  rw [this]; ring

/-- Fubini for `∫ (κ * f) g = ∫ κ(y) ∫ f(x-y) g(x)`. -/
lemma integral_conv_mul_swap (κ f g : Euc d → ℂ)
    (hint : Integrable (fun p : Euc d × Euc d => κ p.2 * f (p.1 - p.2) * g p.1)) :
    ∫ x, (∫ y, κ y * f (x - y)) * g x = ∫ y, κ y * ∫ x, f (x - y) * g x := by
  have e1 : ∀ x, (∫ y, κ y * f (x - y)) * g x = ∫ y, κ y * f (x - y) * g x :=
    fun x => (integral_mul_const _ _).symm
  simp_rw [e1]
  rw [integral_integral_swap (f := fun x y => κ y * f (x - y) * g x) hint]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  ring

lemma integral_shift_neg (F : Euc d → ℂ) (y : Euc d) :
    ∫ x, F (x - y) = ∫ x, F x := integral_sub_right_eq_self F y


/-- `T_α φ = |∇|^α φ`. -/
def Tfrac (α : ℝ) (φ : SchwartzMap (Euc d) ℂ) (x : Euc d) : ℂ :=
  𝓕⁻ (fun ξ : Euc d => (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ) * 𝓕 (⇑φ) ξ) x

lemma Tfrac_integrable (hd : 1 ≤ d) {α : ℝ} (hα : 1 < α) (φ : SchwartzMap (Euc d) ℂ) :
    Integrable (fun x : Euc d => ‖Tfrac α φ x‖) ∧
      Integrable (fun x : Euc d => ‖x‖ * ‖Tfrac α φ x‖) := by
  have hFc : (⇑(𝓕 φ : SchwartzMap (Euc d) ℂ) : Euc d → ℂ) = 𝓕 ⇑φ := SchwartzMap.fourier_coe φ
  have h0 := (cmxHLS_lhs_sum hd hα (v := fun _ => (1 : ℝ)) continuous_const (A := 1)
    (fun x => by simp only [abs_one, one_mul]; linarith [norm_nonneg x]) (𝓕 φ : SchwartzMap (Euc d) ℂ)).1
  have h1 := (cmxHLS_lhs_sum hd hα (v := fun x : Euc d => ‖x‖) continuous_norm (A := 1)
    (fun x => by rw [abs_of_nonneg (norm_nonneg x)]; linarith) (𝓕 φ : SchwartzMap (Euc d) ℂ)).1
  simp only [hFc] at h0 h1
  refine ⟨?_, ?_⟩
  · refine h0.norm.congr (Eventually.of_forall fun x => ?_)
    simp [Tfrac]
  · refine h1.norm.congr (Eventually.of_forall fun x => ?_)
    simp [Tfrac]

lemma integrable_conv_pairing (hd : 1 ≤ d) {k : Euc d → ℝ} (hkm : Measurable k)
    (hk0 : Integrable k) {w : Euc d → ℝ} (hwm : Measurable w) {p : ℝ} (hp : 1 < p)
    (hwp : ∫⁻ y, ‖w y‖ₑ ^ p ≠ ⊤) (φ : SchwartzMap (Euc d) ℂ) :
    Integrable (fun q : Euc d × Euc d => (k q.2 : ℂ) * (w (q.1 - q.2) : ℂ) * φ q.1) := by
  have hp0 : 0 < p := by linarith
  set P : ℝ≥0∞ := ENNReal.ofReal p with hP
  have hP1 : 1 ≤ P := by
    rw [hP, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le
  have : P.HolderConjugate (ENNReal.conjExponent P) := ENNReal.HolderConjugate.conjExponent hP1
  set P' := ENNReal.conjExponent P with hP'
  have hum : AEStronglyMeasurable (fun x : Euc d => ((w x : ℝ) : ℂ)) volume :=
    (Complex.measurable_ofReal.comp hwm).aestronglyMeasurable
  have hu : MemLp (fun x : Euc d => ((w x : ℝ) : ℂ)) P volume := by
    rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top hum,
      ENNReal.toReal_ofReal hp0.le]
    simp_rw [cmxHLS_enorm_ofReal]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hwp
  have hφ : MemLp φ P' volume := φ.memLp P'
  have hmeas : AEStronglyMeasurable
      (fun q : Euc d × Euc d => (k q.2 : ℂ) * (w (q.1 - q.2) : ℂ) * φ q.1) (volume.prod volume) := by
    refine Measurable.aestronglyMeasurable ?_
    exact ((Complex.measurable_ofReal.comp (hkm.comp measurable_snd)).mul
      (Complex.measurable_ofReal.comp (hwm.comp (measurable_fst.sub measurable_snd)))).mul
      (φ.continuous.measurable.comp measurable_fst)
  refine ⟨hmeas, ?_⟩
  unfold HasFiniteIntegral
  have hm2 := hmeas.enorm
  beta_reduce
  refine lt_of_eq_of_lt (lintegral_prod_symm _ hm2) ?_
  have hfin : eLpNorm (fun x : Euc d => ((w x : ℝ) : ℂ)) P volume * eLpNorm φ P' volume < ⊤ :=
    ENNReal.mul_lt_top hu.eLpNorm_lt_top hφ.eLpNorm_lt_top
  calc ∫⁻ y, ∫⁻ x, ‖(k (x, y).2 : ℂ) * (w ((x, y).1 - (x, y).2) : ℂ) * φ (x, y).1‖ₑ
      ≤ ∫⁻ y, ‖k y‖ₑ * (eLpNorm (fun x : Euc d => ((w x : ℝ) : ℂ)) P volume *
          eLpNorm φ P' volume) := by
        refine lintegral_mono fun y => ?_
        have h : ∀ x : Euc d, ‖(k (x, y).2 : ℂ) * (w ((x, y).1 - (x, y).2) : ℂ) * φ (x, y).1‖ₑ
            = ‖k y‖ₑ * ‖((w (x - y) : ℝ) : ℂ) * φ x‖ₑ := by
          intro x
          simp only
          rw [mul_assoc, enorm_mul, cmxHLS_enorm_ofReal]
        simp_rw [h]
        rw [lintegral_const_mul' _ _ enorm_ne_top]
        gcongr
        have := lintegral_holder_shift hu hφ (-y)
        simpa [sub_eq_add_neg] using this
    _ = (∫⁻ y, ‖k y‖ₑ) * (eLpNorm (fun x : Euc d => ((w x : ℝ) : ℂ)) P volume *
          eLpNorm φ P' volume) := lintegral_mul_const' _ _ (by finiteness)
    _ < ⊤ := ENNReal.mul_lt_top hk0.2 hfin


lemma cast_conv (k f : Euc d → ℝ) (x : Euc d) :
    ((∫ y, k y * f (x - y) : ℝ) : ℂ) = ∫ y, (k y : ℂ) * (f (x - y) : ℂ) := by
  rw [← integral_complex_ofReal]; push_cast; rfl

/-- **Convolution commutes with `|∇|^α`**: if `|∇|^α v = w` (distributionally, `v` of linear
growth, `w ∈ L^p`) and `k` has finite first moment, then `|∇|^α (k * v) = k * w`. -/
theorem rep_conv (hd : 1 ≤ d) {α : ℝ} (hα : 1 < α) {k : Euc d → ℝ} (hkm : Measurable k)
    (hk0 : Integrable k) (hk1 : Integrable (fun y : Euc d => ‖y‖ * |k y|))
    {v w : Euc d → ℝ} (hvc : Continuous v) {A : ℝ} (hv : ∀ x, |v x| ≤ A * (1 + ‖x‖))
    (hwm : Measurable w) {p : ℝ} (hp : 1 < p) (hwp : ∫⁻ y, ‖w y‖ₑ ^ p ≠ ⊤)
    (hrep : IsFracDerivRep α v w) :
    IsFracDerivRep α (fun x => ∫ y, k y * v (x - y)) (fun x => ∫ y, k y * w (x - y)) := by
  intro φ
  obtain ⟨hT0, hT1⟩ := Tfrac_integrable hd hα φ
  have hTc : Continuous (Tfrac α φ) := cmxHLS_frac_continuous (by linarith) φ
  have hP1 : Integrable (fun q : Euc d × Euc d =>
      (k q.2 : ℂ) * (v (q.1 - q.2) : ℂ) * Tfrac α φ q.1) := by
    have hkb : Integrable (fun y : Euc d => |k y| * (1 + ‖y‖)) := by
      refine (hk0.norm.add hk1).congr (Eventually.of_forall fun y => ?_)
      simp only [Pi.add_apply, Real.norm_eq_abs]; ring
    have hb : Integrable (fun q : Euc d × Euc d => A * (‖Tfrac α φ q.1‖ * (|k q.2| * (1 + ‖q.2‖)) +
        ‖q.1‖ * ‖Tfrac α φ q.1‖ * |k q.2|)) (volume.prod volume) :=
      ((hT0.mul_prod hkb).add (hT1.mul_prod hk0.norm)).const_mul A
    refine hb.mono' ?_ (Eventually.of_forall fun q => ?_)
    · exact (((Complex.measurable_ofReal.comp (hkm.comp measurable_snd)).mul
        (Complex.measurable_ofReal.comp (hvc.measurable.comp (measurable_fst.sub measurable_snd)))).mul
        (hTc.measurable.comp measurable_fst)).aestronglyMeasurable
    · simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 := hv (q.1 - q.2)
      have h2 : ‖q.1 - q.2‖ ≤ ‖q.1‖ + ‖q.2‖ := norm_sub_le _ _
      have h3 : |v (q.1 - q.2)| ≤ A * (1 + (‖q.1‖ + ‖q.2‖)) := by
        refine h1.trans ?_
        exact mul_le_mul_of_nonneg_left (by linarith) (by
          have := hv 0; simp at this; exact (abs_nonneg _).trans this)
      calc |k q.2| * |v (q.1 - q.2)| * ‖Tfrac α φ q.1‖
          ≤ |k q.2| * (A * (1 + (‖q.1‖ + ‖q.2‖))) * ‖Tfrac α φ q.1‖ := by
            gcongr
        _ = _ := by ring
  have hP2 := integrable_conv_pairing hd hkm hk0 hwm hp hwp φ
  have E1 : ∫ x, ((∫ y, k y * v (x - y) : ℝ) : ℂ) * Tfrac α φ x =
      ∫ y, (k y : ℂ) * ∫ x, (v (x - y) : ℂ) * Tfrac α φ x := by
    simp_rw [cast_conv k v]
    exact integral_conv_mul_swap (fun y => (k y : ℂ)) (fun z => (v z : ℂ)) (Tfrac α φ) hP1
  have E3 : ∫ x, ((∫ y, k y * w (x - y) : ℝ) : ℂ) * φ x =
      ∫ y, (k y : ℂ) * ∫ x, (w (x - y) : ℂ) * φ x := by
    simp_rw [cast_conv k w]
    exact integral_conv_mul_swap (fun y => (k y : ℂ)) (fun z => (w z : ℂ)) φ hP2
  have E2 : ∀ y : Euc d, ∫ x, (v (x - y) : ℂ) * Tfrac α φ x = ∫ x, (w (x - y) : ℂ) * φ x := by
    intro y
    have s1 : ∫ x, (v (x - y) : ℂ) * Tfrac α φ x = ∫ x, (v x : ℂ) * Tfrac α φ (x + y) := by
      rw [← integral_add_right_eq_self (fun x : Euc d => (v (x - y) : ℂ) * Tfrac α φ x) y]
      simp
    have s2 : ∀ x, Tfrac α φ (x + y) =
        𝓕⁻ (fun ξ : Euc d => (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ) * 𝓕 (⇑(shiftS y φ)) ξ) x :=
      fun x => (Tm_shiftS (fun ξ : Euc d => (((2 * Real.pi * ‖ξ‖) ^ α : ℝ) : ℂ)) y φ x).symm
    have s3 := (hrep (shiftS y φ)).2.2
    have s4 : ∫ x, (w x : ℂ) * shiftS y φ x = ∫ x, (w (x - y) : ℂ) * φ x := by
      simp_rw [shiftS_apply]
      rw [← integral_add_right_eq_self (fun x : Euc d => (w (x - y) : ℂ) * φ x) y]
      simp
    simp_rw [s2] at s1
    rw [s1, s3, s4]
  have hI1 : Integrable (fun x : Euc d => ((∫ y, k y * v (x - y) : ℝ) : ℂ) * Tfrac α φ x) := by
    have := hP1.integral_prod_left
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [integral_mul_const, cast_conv k v]
  have hI2 : Integrable (fun x : Euc d => ((∫ y, k y * w (x - y) : ℝ) : ℂ) * φ x) := by
    have := hP2.integral_prod_left
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [integral_mul_const, cast_conv k w]
  refine ⟨hI1, hI2, ?_⟩
  show ∫ x, ((∫ y, k y * v (x - y) : ℝ) : ℂ) * Tfrac α φ x = _
  rw [E1, E3]
  exact integral_congr_ae (Eventually.of_forall fun y => by simp only [E2 y])

end HRS.Commutator.Whole.SAMP1
