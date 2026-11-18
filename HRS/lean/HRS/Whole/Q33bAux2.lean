import HRS.Whole.Q33bAux1

/-!
# Q33b helpers, measure-level part (supplement S11.5, whole-space clause)

For a probability measure `μ` on `ℝ^d` with `ℓ = log⟨·⟩ ∈ L¹(μ)` and the row bound
`sup_y ∫ exp(ε b(x,y)) dμ(x) ≤ C`, the centred logarithm `k(x,y) = g(x-y) - G(x) - G(y) + 2I` (with `G = g * μ`,
`2I = ∬ g dμ dμ`) satisfies `k = b(x,y) - b_μ(x) - b_μ(y) + b̄` (mass one), hence `|k| ≤ b + 2C/ε`, and the
exponential row bound and the factorial moments follow with the constant `exp(2C)·C`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HRS.Whole

/-- `b_μ(x) = ∫ b(x,w) dμ(w)`. -/
def q33b_bmu {d : ℕ} (μ : Measure (Euc d)) (x : Euc d) : ℝ := ∫ w, q33b_b x w ∂μ

theorem q33b_le_exp_div {ε : ℝ} (hε : 0 < ε) (t : ℝ) : t ≤ ε⁻¹ * Real.exp (ε * t) := by
  have h := Real.add_one_le_exp (ε * t)
  calc t = ε⁻¹ * (ε * t) := by rw [← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul]
    _ ≤ ε⁻¹ * Real.exp (ε * t) := mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hε.le)

theorem q33b_b_meas_left {d : ℕ} (x : Euc d) : Measurable (fun w : Euc d => q33b_b x w) :=
  (q33b_b_measurable (d := d)).comp (f := fun w : Euc d => (x, w))
    (measurable_const.prodMk measurable_id)

theorem q33b_b_lintegral_le {d : ℕ} {μ : Measure (Euc d)} {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (hrow : ∀ y : Euc d, ∫⁻ x, ENNReal.ofReal (Real.exp (ε * q33b_b x y)) ∂μ ≤ ENNReal.ofReal C)
    (x : Euc d) : ∫⁻ w, ENNReal.ofReal (q33b_b x w) ∂μ ≤ ENNReal.ofReal (C / ε) := by
  calc ∫⁻ w, ENNReal.ofReal (q33b_b x w) ∂μ
      ≤ ∫⁻ w, ENNReal.ofReal ε⁻¹ * ENNReal.ofReal (Real.exp (ε * q33b_b w x)) ∂μ := by
        refine lintegral_mono fun w => ?_
        rw [q33b_b_comm x w, ← ENNReal.ofReal_mul (inv_nonneg.2 hε.le)]
        exact ENNReal.ofReal_le_ofReal (q33b_le_exp_div hε _)
    _ = ENNReal.ofReal ε⁻¹ * ∫⁻ w, ENNReal.ofReal (Real.exp (ε * q33b_b w x)) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ε⁻¹ * ENNReal.ofReal C := by
        gcongr
        exact hrow x
    _ = ENNReal.ofReal (C / ε) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hε.le), div_eq_mul_inv, mul_comm]

theorem q33b_b_integrable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {ε C : ℝ} (hε : 0 < ε)
    (hC : 0 ≤ C)
    (hrow : ∀ y : Euc d, ∫⁻ x, ENNReal.ofReal (Real.exp (ε * q33b_b x y)) ∂μ ≤ ENNReal.ofReal C)
    (x : Euc d) : Integrable (fun w => q33b_b x w) μ := by
  have hfin : ∫⁻ w, ENNReal.ofReal (q33b_b x w) ∂μ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (q33b_b_lintegral_le hε hC hrow x)
  have h := integrable_toReal_of_lintegral_ne_top (μ := μ)
    (f := fun w => ENNReal.ofReal (q33b_b x w))
    (ENNReal.measurable_ofReal.comp (q33b_b_meas_left x)).aemeasurable hfin
  refine h.congr (Filter.Eventually.of_forall fun w => ?_)
  exact ENNReal.toReal_ofReal (q33b_b_nonneg x w)

theorem q33b_bmu_bounds {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {ε C : ℝ} (hε : 0 < ε)
    (hC : 0 ≤ C)
    (hrow : ∀ y : Euc d, ∫⁻ x, ENNReal.ofReal (Real.exp (ε * q33b_b x y)) ∂μ ≤ ENNReal.ofReal C)
    (x : Euc d) : 0 ≤ q33b_bmu μ x ∧ q33b_bmu μ x ≤ C / ε := by
  unfold q33b_bmu
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun w => q33b_b_nonneg x w)
    (q33b_b_meas_left x).aestronglyMeasurable]
  exact ⟨ENNReal.toReal_nonneg,
    ENNReal.toReal_le_of_le_ofReal (div_nonneg hC hε.le) (q33b_b_lintegral_le hε hC hrow x)⟩

theorem q33b_bmu_measurable {d : ℕ} (μ : Measure (Euc d)) [IsFiniteMeasure μ] :
    Measurable (q33b_bmu μ) := by
  have h : StronglyMeasurable (fun p : Euc d × Euc d => q33b_b p.1 p.2) :=
    (q33b_b_measurable (d := d)).stronglyMeasurable
  exact (h.integral_prod_right' (ν := μ)).measurable

theorem q33b_bmu_integrable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {ε C : ℝ} (hε : 0 < ε)
    (hC : 0 ≤ C)
    (hrow : ∀ y : Euc d, ∫⁻ x, ENNReal.ofReal (Real.exp (ε * q33b_b x y)) ∂μ ≤ ENNReal.ofReal C) :
    Integrable (q33b_bmu μ) μ :=
  Integrable.of_bound (q33b_bmu_measurable μ).aestronglyMeasurable (C / ε)
    (Filter.Eventually.of_forall fun x => by
      obtain ⟨h0, h1⟩ := q33b_bmu_bounds hε hC hrow x
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact h1)

theorem q33b_conv_eq {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {ε C : ℝ} (hε : 0 < ε)
    (hC : 0 ≤ C) (hℓ : Integrable (fun x : Euc d => q33b_ell x) μ)
    (hrow : ∀ y : Euc d, ∫⁻ x, ENNReal.ofReal (Real.exp (ε * q33b_b x y)) ∂μ ≤ ENNReal.ofReal C)
    (x : Euc d) :
    convMeasure (rieszKernel d 0) μ x = q33b_bmu μ x - q33b_ell x - ∫ z, q33b_ell z ∂μ := by
  have hb := q33b_b_integrable hε hC hrow x
  have e : ∀ z : Euc d, rieszKernel d 0 (x - z) = (q33b_b x z - q33b_ell x) - q33b_ell z := by
    intro z
    unfold q33b_b
    ring
  unfold convMeasure q33b_bmu
  simp_rw [e]
  have h1 : Integrable (fun y => q33b_b x y - q33b_ell x) μ := hb.sub (integrable_const _)
  rw [integral_sub h1 hℓ, integral_sub hb (integrable_const _)]
  simp

theorem q33b_conv_integral {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {ε C : ℝ} (hε : 0 < ε)
    (hC : 0 ≤ C) (hℓ : Integrable (fun x : Euc d => q33b_ell x) μ)
    (hrow : ∀ y : Euc d, ∫⁻ x, ENNReal.ofReal (Real.exp (ε * q33b_b x y)) ∂μ ≤ ENNReal.ofReal C) :
    ∫ x, convMeasure (rieszKernel d 0) μ x ∂μ
      = (∫ x, q33b_bmu μ x ∂μ) - (∫ x, q33b_ell x ∂μ) - ∫ x, q33b_ell x ∂μ := by
  have hfun : (fun x => convMeasure (rieszKernel d 0) μ x)
      = fun x => q33b_bmu μ x - q33b_ell x - ∫ z, q33b_ell z ∂μ :=
    funext (q33b_conv_eq hε hC hℓ hrow)
  have h1 : Integrable (fun x => q33b_bmu μ x - q33b_ell x) μ :=
    (q33b_bmu_integrable hε hC hrow).sub hℓ
  rw [hfun, integral_sub h1 (integrable_const _),
    integral_sub (q33b_bmu_integrable hε hC hrow) hℓ, integral_const]
  simp

theorem q33b_k_eq {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {ε C : ℝ} (hε : 0 < ε)
    (hC : 0 ≤ C) (hℓ : Integrable (fun x : Euc d => q33b_ell x) μ)
    (hrow : ∀ y : Euc d, ∫⁻ x, ENNReal.ofReal (Real.exp (ε * q33b_b x y)) ∂μ ≤ ENNReal.ofReal C)
    (x y : Euc d) :
    rieszKernel d 0 (x - y) - convMeasure (rieszKernel d 0) μ x - convMeasure (rieszKernel d 0) μ y
      + 2 * ((1 / 2) * ∫ z, convMeasure (rieszKernel d 0) μ z ∂μ)
      = q33b_b x y - q33b_bmu μ x - q33b_bmu μ y + ∫ z, q33b_bmu μ z ∂μ := by
  rw [q33b_conv_eq hε hC hℓ hrow x, q33b_conv_eq hε hC hℓ hrow y, q33b_conv_integral hε hC hℓ hrow]
  unfold q33b_b
  ring

/-- `|z|^p ≤ (ε⁻¹)^p p! exp(ε|z|)` for `z ≥ 0`. -/
theorem q33b_pow_le {ε : ℝ} (hε : 0 < ε) {z : ℝ} (hz : 0 ≤ z) (p : ℕ) :
    z ^ p ≤ (ε⁻¹) ^ p * (p.factorial : ℝ) * Real.exp (ε * z) := by
  have hfact : (0 : ℝ) < (p.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos p
  have h := Real.pow_div_factorial_le_exp (ε * z) (mul_nonneg hε.le hz) p
  have h2 : (ε * z) ^ p ≤ Real.exp (ε * z) * (p.factorial : ℝ) := (div_le_iff₀ hfact).1 h
  have h3 : z ^ p = (ε⁻¹) ^ p * (ε * z) ^ p := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [h3]
  calc (ε⁻¹) ^ p * (ε * z) ^ p ≤ (ε⁻¹) ^ p * (Real.exp (ε * z) * (p.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left h2 (pow_nonneg (inv_nonneg.2 hε.le) p)
    _ = (ε⁻¹) ^ p * (p.factorial : ℝ) * Real.exp (ε * z) := by ring

/-- The main measure-level statement: the row bound, integrability and factorial moments of the centred
logarithm `k` (with the constant `exp(2C)·C`). -/
theorem q33b_main {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {ε C : ℝ} (hε : 0 < ε)
    (hC : 0 ≤ C) (hℓ : Integrable (fun x : Euc d => q33b_ell x) μ)
    (hrow : ∀ y : Euc d, ∫⁻ x, ENNReal.ofReal (Real.exp (ε * q33b_b x y)) ∂μ ≤ ENNReal.ofReal C) :
    Integrable (fun p : Euc d × Euc d => rieszKernel d 0 (p.1 - p.2)) (μ.prod μ) ∧
    (∀ y : Euc d, ∫⁻ x, ENNReal.ofReal (Real.exp (ε * |rieszKernel d 0 (x - y)
        - convMeasure (rieszKernel d 0) μ x - convMeasure (rieszKernel d 0) μ y
        + 2 * ((1 / 2) * ∫ z, convMeasure (rieszKernel d 0) μ z ∂μ)|)) ∂μ
        ≤ ENNReal.ofReal (Real.exp (2 * C) * C)) ∧
    (∀ (p : ℕ) (y : Euc d), ∫⁻ x, ENNReal.ofReal (|rieszKernel d 0 (x - y)
        - convMeasure (rieszKernel d 0) μ x - convMeasure (rieszKernel d 0) μ y
        + 2 * ((1 / 2) * ∫ z, convMeasure (rieszKernel d 0) μ z ∂μ)| ^ p) ∂μ
        ≤ ENNReal.ofReal (Real.exp (2 * C) * C * (p.factorial : ℝ) * (ε⁻¹) ^ p)) := by
  have hbmu := q33b_bmu_integrable hε hC hrow
  have hb01 := fun x => q33b_bmu_bounds hε hC hrow x
  -- `b̄ = ∫ b_μ dμ ∈ [0, C/ε]`
  have hbbar0 : 0 ≤ ∫ z, q33b_bmu μ z ∂μ :=
    integral_nonneg fun z => (hb01 z).1
  have hbbarM : ∫ z, q33b_bmu μ z ∂μ ≤ C / ε := by
    have := integral_mono hbmu (integrable_const (C / ε)) (fun z => (hb01 z).2)
    simpa using this
  -- the bound on the centred kernel `|k| ≤ b + 2C/ε`
  have hk : ∀ x y : Euc d, |rieszKernel d 0 (x - y) - convMeasure (rieszKernel d 0) μ x
      - convMeasure (rieszKernel d 0) μ y
      + 2 * ((1 / 2) * ∫ z, convMeasure (rieszKernel d 0) μ z ∂μ)| ≤ q33b_b x y + 2 * (C / ε) := by
    intro x y
    rw [q33b_k_eq hε hC hℓ hrow x y]
    have hbxy := q33b_b_nonneg x y
    have hM0 : 0 ≤ C / ε := div_nonneg hC hε.le
    rw [abs_le]
    have h1 := hb01 x
    have h2 := hb01 y
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, hbbar0, hbbarM]
  -- first clause: integrability on the product
  have hprod_b : Integrable (fun p : Euc d × Euc d => q33b_b p.1 p.2) (μ.prod μ) := by
    rw [integrable_prod_iff (q33b_b_measurable (d := d)).aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun x => q33b_b_integrable hε hC hrow x, ?_⟩
    refine hbmu.congr (Filter.Eventually.of_forall fun x => ?_)
    unfold q33b_bmu
    congr 1
    funext w
    exact (Real.norm_of_nonneg (q33b_b_nonneg x w)).symm
  -- pointwise bound on `exp(ε|k|)`
  have hpt : ∀ x y : Euc d, Real.exp (ε * |rieszKernel d 0 (x - y) - convMeasure (rieszKernel d 0) μ x
      - convMeasure (rieszKernel d 0) μ y
      + 2 * ((1 / 2) * ∫ z, convMeasure (rieszKernel d 0) μ z ∂μ)|)
      ≤ Real.exp (2 * C) * Real.exp (ε * q33b_b x y) := by
    intro x y
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have h2 := mul_le_mul_of_nonneg_left (hk x y) hε.le
    have h3 : ε * (q33b_b x y + 2 * (C / ε)) = ε * q33b_b x y + 2 * C := by
      rw [mul_add, show ε * (2 * (C / ε)) = 2 * C by field_simp]
    linarith
  have hclause2 : ∀ y : Euc d, ∫⁻ x, ENNReal.ofReal (Real.exp (ε * |rieszKernel d 0 (x - y)
      - convMeasure (rieszKernel d 0) μ x - convMeasure (rieszKernel d 0) μ y
      + 2 * ((1 / 2) * ∫ z, convMeasure (rieszKernel d 0) μ z ∂μ)|)) ∂μ
      ≤ ENNReal.ofReal (Real.exp (2 * C) * C) := by
    intro y
    calc ∫⁻ x, ENNReal.ofReal (Real.exp (ε * |rieszKernel d 0 (x - y)
          - convMeasure (rieszKernel d 0) μ x - convMeasure (rieszKernel d 0) μ y
          + 2 * ((1 / 2) * ∫ z, convMeasure (rieszKernel d 0) μ z ∂μ)|)) ∂μ
        ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (2 * C)) * ENNReal.ofReal (Real.exp (ε * q33b_b x y)) ∂μ := by
          refine lintegral_mono fun x => ?_
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
          exact ENNReal.ofReal_le_ofReal (hpt x y)
      _ = ENNReal.ofReal (Real.exp (2 * C)) * ∫⁻ x, ENNReal.ofReal (Real.exp (ε * q33b_b x y)) ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Real.exp (2 * C)) * ENNReal.ofReal C := by
          gcongr
          exact hrow y
      _ = ENNReal.ofReal (Real.exp (2 * C) * C) := (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
  refine ⟨?_, hclause2, ?_⟩
  · have hfun : (fun p : Euc d × Euc d => rieszKernel d 0 (p.1 - p.2))
        = fun p => (q33b_b p.1 p.2 - q33b_ell p.1) - q33b_ell p.2 := by
      funext p
      unfold q33b_b
      ring
    rw [hfun]
    exact (hprod_b.sub (hℓ.comp_fst μ)).sub (hℓ.comp_snd μ)
  · intro p y
    have hnn : 0 ≤ (ε⁻¹) ^ p * (p.factorial : ℝ) :=
      mul_nonneg (pow_nonneg (inv_nonneg.2 hε.le) p) (Nat.cast_nonneg _)
    calc ∫⁻ x, ENNReal.ofReal (|rieszKernel d 0 (x - y)
          - convMeasure (rieszKernel d 0) μ x - convMeasure (rieszKernel d 0) μ y
          + 2 * ((1 / 2) * ∫ z, convMeasure (rieszKernel d 0) μ z ∂μ)| ^ p) ∂μ
        ≤ ∫⁻ x, ENNReal.ofReal ((ε⁻¹) ^ p * (p.factorial : ℝ)) * ENNReal.ofReal (Real.exp (ε * |rieszKernel d 0 (x - y)
          - convMeasure (rieszKernel d 0) μ x - convMeasure (rieszKernel d 0) μ y
          + 2 * ((1 / 2) * ∫ z, convMeasure (rieszKernel d 0) μ z ∂μ)|)) ∂μ := by
          refine lintegral_mono fun x => ?_
          rw [← ENNReal.ofReal_mul hnn]
          exact ENNReal.ofReal_le_ofReal (q33b_pow_le hε (abs_nonneg _) p)
      _ = ENNReal.ofReal ((ε⁻¹) ^ p * (p.factorial : ℝ)) * ∫⁻ x, ENNReal.ofReal (Real.exp (ε * |rieszKernel d 0 (x - y)
          - convMeasure (rieszKernel d 0) μ x - convMeasure (rieszKernel d 0) μ y
          + 2 * ((1 / 2) * ∫ z, convMeasure (rieszKernel d 0) μ z ∂μ)|)) ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal ((ε⁻¹) ^ p * (p.factorial : ℝ)) * ENNReal.ofReal (Real.exp (2 * C) * C) := by
          gcongr
          exact hclause2 y
      _ = ENNReal.ofReal (Real.exp (2 * C) * C * (p.factorial : ℝ) * (ε⁻¹) ^ p) := by
          rw [← ENNReal.ofReal_mul hnn]
          congr 1
          ring

end HRS.Whole
