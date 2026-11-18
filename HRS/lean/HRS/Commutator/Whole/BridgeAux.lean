import HRS.Commutator.Whole.Defs
import HRS.Commutator.Whole.ApproxAux

/-!
# CMX-BRIDGE auxiliary: kernel normalisations and densities

Helper lemmas for `Bridge.lean` (all names prefixed `cmxFB_`).  The factor `rieszScale s` of
`Bridge.lean` is written here as `if s = 0 then 1 else s`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff RealInnerProductSpace

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

theorem cmxFB_rk_eq (x : Euc d) :
    rieszKernel d s x = (if s = 0 then 1 else s) * kern s x := by
  unfold rieszKernel kern
  by_cases h : s = 0
  · simp [h]
  · simp only [h, ite_false]
    rw [mul_inv_cancel_left₀ h]

theorem cmxFB_hasGrad_sq (z : Euc d) {G : ℝ → ℝ} {G' : ℝ} (h : HasDerivAt G G' (‖z‖ ^ 2)) :
    HasGradientAt (fun x : Euc d => G (‖x‖ ^ 2)) ((2 * G') • z) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 := h.comp_hasFDerivAt z (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  refine h1.congr_fderiv ?_
  ext w
  simp
  ring

theorem cmxFB_rk_grad (z : Euc d) (hz : z ≠ 0) :
    rieszKernelGrad d s z = (if s = 0 then 1 else s) • kernGrad s z := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hn2 : 0 < ‖z‖ ^ 2 := by positivity
  unfold rieszKernelGrad
  by_cases hs : s = 0
  · subst hs
    have hf : rieszKernel d 0 = fun x : Euc d => (-(1 / 2 : ℝ)) * Real.log (‖x‖ ^ 2) := by
      funext x
      simp only [rieszKernel, ite_true]
      rw [Real.log_pow]
      push_cast
      ring
    rw [hf]
    have hD : HasDerivAt (fun t : ℝ => (-(1 / 2 : ℝ)) * Real.log t) ((-(1 / 2 : ℝ)) * (‖z‖ ^ 2)⁻¹)
        (‖z‖ ^ 2) :=
      (Real.hasDerivAt_log hn2.ne').const_mul _
    have := (cmxFB_hasGrad_sq z hD).gradient
    simp only [ite_true, one_smul]
    convert this using 1
    unfold kernGrad
    rw [show -((0 : ℝ) + 2) = -(2 : ℝ) by ring, Real.rpow_neg hn.le]
    have : (‖z‖ ^ (2 : ℝ)) = ‖z‖ ^ 2 := by exact_mod_cast Real.rpow_natCast ‖z‖ 2
    rw [this]
    congr 1
    ring
  · have hf : rieszKernel d s = fun x : Euc d => (‖x‖ ^ 2) ^ (-s / 2) := by
      funext x
      simp only [rieszKernel, hs, ite_false]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
      congr 1
      push_cast
      ring
    rw [hf]
    have hD := Real.hasDerivAt_rpow_const (x := ‖z‖ ^ 2) (p := -s / 2) (Or.inl hn2.ne')
    have := (cmxFB_hasGrad_sq z hD).gradient
    simp only [hs, ite_false]
    convert this using 1
    unfold kernGrad
    have e1 : ‖z‖ ^ (-(s + 2)) = (‖z‖ ^ 2) ^ (-s / 2 - 1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
      congr 1
      push_cast
      ring
    rw [e1, smul_smul]
    congr 1
    ring

theorem cmxFB_commKernel_eq (v : Euc d → Euc d) (x y : Euc d) :
    commutatorKernel d s v x y = (if s = 0 then 1 else s) * commKer (kernGrad s) v x y := by
  unfold commutatorKernel commKer
  by_cases h : x = y
  · subst h; simp
  · rw [if_neg h, cmxFB_rk_grad (x - y) (sub_ne_zero.2 h), inner_smul_right]

/-! ### Integration against `ρ dx` -/

theorem cmxFB_int_wd {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : Euc d → E) :
    ∫ y, f y ∂(HRS.Whole.withDensityReal ρ) = ∫ y, ρ y • f y := by
  unfold HRS.Whole.withDensityReal
  rw [integral_withDensity_eq_integral_toReal_smul hρ.measurable.ennreal_ofReal
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [ENNReal.toReal_ofReal (hρ.nonneg y)]

theorem cmxFB_integrable_wd {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Euc d → E) :
    Integrable f (HRS.Whole.withDensityReal ρ) ↔ Integrable (fun y => ρ y • f y) := by
  unfold HRS.Whole.withDensityReal
  rw [integrable_withDensity_iff_integrable_smul' hρ.measurable.ennreal_ofReal
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integrable_congr (Eventually.of_forall fun y => ?_)
  simp only
  rw [ENNReal.toReal_ofReal (hρ.nonneg y)]

theorem cmxFB_integrable_wd2 {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    (f : Euc d × Euc d → ℝ) :
    Integrable f ((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)) ↔
      Integrable (fun p : Euc d × Euc d => (ρ p.1 * ρ p.2) * f p) (volume.prod volume) := by
  unfold HRS.Whole.withDensityReal
  rw [prod_withDensity₀ hρ.measurable.ennreal_ofReal.aemeasurable
    hρ.measurable.ennreal_ofReal.aemeasurable]
  have hm : Measurable fun z : Euc d × Euc d => ENNReal.ofReal (ρ z.1) * ENNReal.ofReal (ρ z.2) :=
    (hρ.measurable.ennreal_ofReal.comp measurable_fst).mul
      (hρ.measurable.ennreal_ofReal.comp measurable_snd)
  rw [integrable_withDensity_iff_integrable_smul' hm
    (Eventually.of_forall fun x => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)]
  refine integrable_congr (Eventually.of_forall fun p => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hρ.nonneg _), ENNReal.toReal_ofReal (hρ.nonneg _)]

theorem cmxFB_inner_wd {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (c : ℝ) (k h : Euc d → Euc d → ℝ)
    (hk : ∀ x y, h x y = c * k x y) (a : Euc d) :
    ∫ y, h a y ∂(HRS.Whole.withDensityReal ρ) = c * ∫ y, k a y * ρ y := by
  rw [cmxFB_int_wd hρ, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [smul_eq_mul, hk]
  ring

theorem cmxFB_outer_wd {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (c : ℝ) (k h : Euc d → Euc d → ℝ)
    (hk : ∀ x y, h x y = c * k x y) :
    ∫ x, ∫ y, h x y ∂(HRS.Whole.withDensityReal ρ) ∂(HRS.Whole.withDensityReal ρ) =
      c * ∫ x, ∫ y, k x y * ρ x * ρ y := by
  rw [cmxFB_int_wd hρ, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  rw [cmxFB_inner_wd hρ c k h hk x]
  have : ∫ y, k x y * ρ x * ρ y = ρ x * ∫ y, k x y * ρ y := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    ring
  rw [this]
  ring

/-- The common core of `rieszEnergy_eq` and `commN_eq`. -/
theorem cmxFB_cpf_eq {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) {N : ℕ} (c : ℝ)
    (k h : Euc d → Euc d → ℝ) (hk : ∀ x y, h x y = c * k x y) (X : Fin N → Euc d) :
    HRS.Whole.centeredPairFunctional h X (HRS.Whole.withDensityReal ρ) = c * pairGen k X ρ := by
  unfold HRS.Whole.centeredPairFunctional pairGen
  rw [cmxFB_outer_wd hρ c k h hk]
  have e1 : ∀ i, ∫ y, h (X i) y ∂(HRS.Whole.withDensityReal ρ) = c * ∫ y, k (X i) y * ρ y :=
    fun i => cmxFB_inner_wd hρ c k h hk (X i)
  simp_rw [e1, hk, ← Finset.mul_sum]
  ring

theorem cmxFB_integrable_scale {α : Type*} [MeasurableSpace α] {μ : Measure α} {c : ℝ}
    (hc : c ≠ 0) {f g : α → ℝ} (h : ∀ x, f x = c * g x) : Integrable f μ ↔ Integrable g μ := by
  constructor
  · intro hf
    refine (hf.const_mul c⁻¹).congr (Eventually.of_forall fun x => ?_)
    simp only [h x]
    field_simp
  · intro hg
    exact (hg.const_mul c).congr (Eventually.of_forall fun x => (h x).symm)

theorem cmxFB_logIntegrable (ρ : Euc d → ℝ) (hρ : HRS.Whole.IsProbDensity ρ) (Λ : ℝ)
    (hΛ : ∀ x, ρ x ≤ Λ) (L : ℝ) (hlog : HRS.Whole.HasLogMoment (HRS.Whole.withDensityReal ρ) L) :
    LogIntegrable ρ := by
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · subst hd0
    unfold LogIntegrable
    refine (integrable_zero (Euc 0 × Euc 0) ℝ _).congr (Eventually.of_forall fun p => ?_)
    have : p.1 - p.2 = 0 := Subsingleton.elim _ _
    simp [this, kern]
  · have h1 : Integrable ρ := by
      by_contra h
      have := hρ.integral_one
      rw [integral_undef h] at this
      exact zero_ne_one this
    have hinf : MemLp ρ ⊤ volume :=
      memLp_top_of_bound h1.aestronglyMeasurable |Λ| (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hρ.nonneg x)]
        exact le_trans (hΛ x) (le_abs_self Λ))
    have hWρ : Integrable (fun x => cmxSA_W 0 x * ρ x) := by
      have := (cmxFB_integrable_wd hρ _).1 hlog.1
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp only [cmxSA_W, ite_true, smul_eq_mul]
      ring
    have hσ0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
    have hq : (1 : ℝ) ≤ 1 := le_rfl
    have hσq : (1 / 2 : ℝ) * 1 < d := by
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    obtain ⟨B, hB, hconv⟩ := cmxSA_conv_bound (by omega) hσ0 hq hσq ⊤ (by simp) ρ hinf
    have := cmxSA_core_m (k := fun x y : Euc d => kern (0 : ℝ) (x - y))
      ((cmxSA_kern_measurable 0).comp (measurable_fst.sub measurable_snd)) ρ hρ.measurable h1
      (cmxSA_W 0) (cmxSA_W_measurable 0) (cmxSA_W_nonneg 0) hWρ (0 : ℝ)⁻¹
      ((0 : ℝ)⁻¹ + (1 / 2 : ℝ)⁻¹) (1 / 2) (inv_nonneg.2 le_rfl) (by positivity) B hB hconv
      (fun x y => cmxSA_kern_bound (s := 0) le_rfl (by norm_num) (by norm_num) x y)
    unfold LogIntegrable
    refine this.2.congr (Eventually.of_forall fun p => ?_)
    simp only
    ring

end HRS.Commutator.Whole
